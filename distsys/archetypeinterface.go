package distsys

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"sync"
	"sync/atomic"
)

// ArchetypeInterface provides an archetype-centric interface to an MPCalContext.
// While just an opaque wrapper for an MPCalContext, it provides a separation of concerns between:
// (1) how to configure and run and MPCal archetype (available via a plain MPCalContext)
// (2) how the MPCal archetype's code accesses its configuration and internal state while running (available via ArchetypeInterface)
type ArchetypeInterface struct {
	ctx            *MPCalContext
	resourceStates map[ArchetypeResourceHandle]ArchetypeResourceState
	killCh         chan struct{} // TODO: not used yet, but intended for resource implementations to detect preemption
}

// Self returns the associated archetype's self binding. Requires a configured archetype.
func (iface *ArchetypeInterface) Self() tla.TLAValue {
	iface.ctx.requireRunnable()
	return iface.ctx.self
}

func (iface *ArchetypeInterface) ensureCriticalSectionWith(handle ArchetypeResourceHandle) {
	_ = iface.getResourceStateByHandle(handle)
}

// Write models the MPCal statement resourceFromHandle[indices...] := value.
// It is expected to be called only from PGo-generated code.
func (iface *ArchetypeInterface) Write(handle ArchetypeResourceHandle, indices []tla.TLAValue, value tla.TLAValue) (err error) {
	iface.ensureCriticalSectionWith(handle)
	state := iface.getResourceStateByHandle(handle)
	var component ArchetypeResourceComponent = state
	for _, index := range indices {
		component, err = component.Index(index)
		if err != nil {
			return
		}
	}
	err = component.WriteValue(iface, value)
	return
}

// Read models the MPCal expression resourceFromHandle[indices...].
// If is expected to be called only from PGo-generated code.
func (iface *ArchetypeInterface) Read(handle ArchetypeResourceHandle, indices []tla.TLAValue) (value tla.TLAValue, err error) {
	iface.ensureCriticalSectionWith(handle)
	state := iface.getResourceStateByHandle(handle)
	var component ArchetypeResourceComponent = state
	for _, index := range indices {
		component, err = component.Index(index)
		if err != nil {
			return
		}
	}
	value, err = component.ReadValue(iface)
	return
}

// NextFairnessCounter returns number [0,ceiling) indicating a non-deterministic branching decision which,
// given an MPCal critical section being retried indefinitely with no other changes, will try to guarantee that all
// possible non-deterministic branch choices will be attempted.
func (iface *ArchetypeInterface) NextFairnessCounter(id string, ceiling uint) uint {
	return iface.ctx.fairnessCounter.NextFairnessCounter(id, ceiling)
}

type BranchResourceMap map[ArchetypeResourceHandle]ArchetypeResource

//type branch func(branchResources BranchResourceMap) error
type branch func(iface *ArchetypeInterface) error

func (iface *ArchetypeInterface) forkIFace() *ArchetypeInterface {
	copiedStates := make(map[ArchetypeResourceHandle]ArchetypeResourceState, len(iface.resourceStates))
	for handle, state := range iface.resourceStates {
		copiedStates[handle] = state.ForkState()
	}
	return &ArchetypeInterface{
		ctx:            iface.ctx,
		resourceStates: copiedStates,
		killCh:         make(chan struct{}),
	}
}

func (iface *ArchetypeInterface) abort() {
	var nonTrivialAborts []chan struct{}
	for _, res := range iface.resourceStates {
		nonTrivialAborts = append(nonTrivialAborts, res.Abort()...)
	}
	for _, ch := range nonTrivialAborts {
		<-ch
	}
}

func (iface *ArchetypeInterface) commit() (err error) {
	// dispatch all parts of the pre-commit phase asynchronously, so we only wait as long as the slowest resource
	var nonTrivialPreCommits []chan error
	for _, res := range iface.resourceStates {
		nonTrivialPreCommits = append(nonTrivialPreCommits, res.PreCommit()...)
	}
	for _, ch := range nonTrivialPreCommits {
		localErr := <-ch
		if localErr != nil {
			err = localErr
		}
	}

	// if there was an error, stop now, and expect either (1) total crash, or (2) Abort to be called
	if err != nil {
		return
	}

	// same as above, run all the commit processes async
	var nonTrivialCommits []chan struct{}
	for _, res := range iface.resourceStates {
		nonTrivialCommits = append(nonTrivialCommits, res.Commit()...)
	}
	for _, ch := range nonTrivialCommits {
		<-ch
	}

	// the go compiler optimizes this to a map clear operation
	for resHandle := range iface.resourceStates {
		delete(iface.resourceStates, resHandle)
	}
	return
}

func (iface *ArchetypeInterface) RunBranchConcurrently(branches ...branch) error {
	fmt.Println("Starting critical section")

	if len(branches) == 0 {
		return ErrCriticalSectionAborted // no branches => no success
	}

	// Create set of forked ifaces
	childIfaces := []*ArchetypeInterface{iface}
	for range branches[1:] {
		childIfaces = append(childIfaces, iface.forkIFace())
	}

	type branchResult struct {
		idx int32
		err error
	}

	doneSignal := make(chan struct{})
	result := branchResult{
		idx: -1,
	}
	var abortCount int32 = 0

	temp := sync.WaitGroup{}
	temp.Add(3)

	for i := range branches {
		index := i
		branch := branches[index]
		iface := childIfaces[index]
		go func() {
			defer temp.Done()
			// Run branch
			err := branch(iface)
			if err == ErrCriticalSectionAborted {
				currentAbortCount := atomic.AddInt32(&abortCount, 1)
				if currentAbortCount == int32(len(branches)) {
					result.err = ErrCriticalSectionAborted // ok to write, we know we're last
					close(doneSignal)                      // we all aborted, give up
				}
				iface.abort() // abort on-thread, because abort might block a little

				return // we aborted, so, unless we were the last, let someone else maybe succeed
			}
			if err != ErrCriticalSectionAborted {
				// something happened that wasn't an abort. notify the waiting goroutine it was us
				// (but only if we were the first to see something; ensure this with atomic CAS)
				amIFirst := atomic.CompareAndSwapInt32(&result.idx, -1, int32(index))
				if amIFirst {
					fmt.Printf("%d chosen\n", index)
					result.err = err // write before signal, so the waiting goroutine sees err
					close(doneSignal)
				} else {
					iface.abort() // abort on-thread, because abort might block a little
				}
			}
		}()
	}

	<-doneSignal
	if result.idx != -1 && result.err == nil {
		//for h, r := range iface.resourceStates {
		//	fmt.Printf("{%v, %v}\n", h, r)
		//}
		for h, r := range childIfaces[result.idx].resourceStates {
			fmt.Printf("{%v, %v}\n", h, r)
		}
		// steal resources of successful child to continue, if there is one
		iface.resourceStates = childIfaces[result.idx].resourceStates
	}
	fmt.Println("result")
	for h, r := range iface.resourceStates {
		fmt.Printf("{%v, %v}\n", h, r)
	}
	temp.Wait()
	return result.err
}

// GetConstant returns the constant operator bound to the given name as a variadic Go function.
// The function is generated in DefineConstantOperator, and is expected to check its own arguments.
func (iface *ArchetypeInterface) GetConstant(name string) func(args ...tla.TLAValue) tla.TLAValue {
	fn, wasFound := iface.ctx.constantDefns[name]
	if !wasFound {
		panic(fmt.Errorf("could not find constant definition %s", name))
	}
	return fn
}

func (iface *ArchetypeInterface) getResourceStateByHandle(handle ArchetypeResourceHandle) ArchetypeResourceState {
	if state, ok := iface.resourceStates[handle]; ok {
		return state
	}
	res := iface.ctx.getResourceByHandle(handle)
	state := res.FreshState()
	iface.resourceStates[handle] = state
	return state
}

// RequireArchetypeResource returns a handle to the archetype resource with the given name. It panics if this resource
// does not exist.
func (iface *ArchetypeInterface) RequireArchetypeResource(name string) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle(name)
	_ = iface.getResourceStateByHandle(handle)
	return handle
}

// RequireArchetypeResourceRef returns a handle to the archetype resource with the given name, when the name refers
// to a resource that was passed by ref in MPCal (in Go, ref-passing has an extra indirection that must be followed).
// If the resource does not exist, or an invalid indirection is used, this method will panic.
func (iface *ArchetypeInterface) RequireArchetypeResourceRef(name string) (ArchetypeResourceHandle, error) {
	ptr := iface.RequireArchetypeResource(name)
	ptrVal, err := iface.Read(ptr, nil)
	if err != nil {
		return "", err
	}
	return iface.RequireArchetypeResource(ptrVal.AsString()), nil
}

// EnsureArchetypeResourceLocal ensures that a local state variable exists (local to an archetype or procedure), creating
// it with the given default value if not.
func (iface *ArchetypeInterface) EnsureArchetypeResourceLocal(name string, value tla.TLAValue) {
	_ = iface.ctx.ensureArchetypeResource(name, LocalArchetypeResourceMaker(value))
}

func (iface *ArchetypeInterface) getCriticalSection(name string) MPCalCriticalSection {
	if criticalSection, ok := iface.ctx.jumpTable[name]; ok {
		return criticalSection
	}
	panic(fmt.Errorf("could not find critical section %s", name))
}

func (iface *ArchetypeInterface) getProc(name string) MPCalProc {
	if proc, ok := iface.ctx.procTable[name]; ok {
		return proc
	}
	panic(fmt.Errorf("could not find procedure %s", name))
}

var defaultLocalArchetypeResourceMaker = LocalArchetypeResourceMaker(tla.TLAValue{})

func (iface *ArchetypeInterface) ensureArchetypeResourceLocalWithDefault(name string) ArchetypeResourceHandle {
	return iface.ctx.ensureArchetypeResource(name, defaultLocalArchetypeResourceMaker)
}

// Goto sets the running archetype's program counter to the target value.
// It will panic if the target is not a valid label name.
// This method should be called at the end of a critical section.
func (iface *ArchetypeInterface) Goto(target string) error {
	_ = iface.getCriticalSection(target) // crash now if the new pc isn't in the jump table
	pc := iface.RequireArchetypeResource(".pc")
	return iface.Write(pc, nil, tla.MakeTLAString(target))
}

// Call performs all necessary steps of a procedure call in MPCal, given a procedure name, a program counter to return to,
// and any number of arguments.
// Specifically, this involves:
// - read the callee's locals, and saving them onto the stack state variable
// - write the new argument values (argVals, in the same order as in MPCal) to the callee's arguments
// - initialize any local state variables in the callee
// - jump to the callee's first label via Goto
//
// This method should be called at the end of a critical section.
func (iface *ArchetypeInterface) Call(procName string, returnPC string, argVals ...tla.TLAValue) error {
	proc := iface.getProc(procName)
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}

	// StateVars is organised as [arg_1, ..., arg_i, local_1, ..., local_j], for i arguments and j locals
	// during a call, argument values will be passed, but local vals will not.
	// there's an explicit bounds check below that differentiates between argIdx being in range of arg vals,
	// and argIdx referring to a state var (beyond len(argVals)).
	// It's only an error to have more argVals than StateVars.
	if len(argVals) > len(proc.StateVars) {
		panic(fmt.Errorf("too many arguments when calling procedure %s", proc.Name))
	}

	// store all the callee's locals into the stack, to avoid clobbering them while the procedure runs
	builder := immutable.NewMapBuilder(tla.TLAValueHasher{})
	builder.Set(tla.MakeTLAString(".pc"), tla.MakeTLAString(returnPC)) // store return address
	for argIdx, argVarName := range proc.StateVars {
		argHandle := iface.ensureArchetypeResourceLocalWithDefault(argVarName)

		// save original argument value
		argVal, err := iface.Read(argHandle, nil)
		if err != nil {
			return err
		}
		builder.Set(tla.MakeTLAString(argVarName), argVal)

		// write the argument value into callee state (if we are still dealing with args; extra state vars are not args)
		if argIdx < len(argVals) {
			err = iface.Write(argHandle, nil, argVals[argIdx])
			if err != nil {
				return err
			}
		}
	}
	newStackRecord := tla.MakeTLARecordFromMap(builder.Map())

	// push the record onto the stack via tuple concatenation
	err = iface.Write(stack, nil, tla.TLA_OSymbol(tla.MakeTLATuple(newStackRecord), stackVal))
	if err != nil {
		return err
	}

	// perform the preamble, which will set up any initial state variable values caller-side (yes, that is how PCal does it)
	err = proc.PreAmble(iface)
	if err != nil {
		return err
	}

	// finally, jump to procedure start label
	return iface.Goto(proc.Label)
}

// TailCall specialises the Call operation via the well-known tail-call optimisation.
// It does this by:
// - extracting a return value from the top of the callstack
// - performing a Return
// - immediately performing a Call to procName with argVals and the extracted return destination
//
// This ensures that the existing top-of-stack is cleaned up, the correct return address is stored, and
// all the procedure call semantics for a new call replacing the current one are satisfied.
//
// Note: like Return, this should never be called outside a procedure, as it relies on an existing stack frame.
//
// This method, like those it wraps, should be called at the end of a critical section.
func (iface *ArchetypeInterface) TailCall(procName string, argVals ...tla.TLAValue) error {
	// pull the top-of-stack return address from the initial stack, so we can use it in the tail-call process below
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	tailPC, ok := stackVal.AsFunction().Get(tla.MakeTLAString(".pc"))
	if !ok {
		panic(fmt.Errorf("stack record %v does not contain a program counter (.pc)", stackVal))
	}

	// first, perform a standard return, to ensure that we've dropped our current stack frame and restored
	// all the relevant state variables, as if we really returned
	err = iface.Return()
	if err != nil {
		return err
	}
	// then immediately call out to the tail-call target, both clobbering the PC we just jumped to via return,
	// and preserving it by making it the return target for the call we clobber it with.
	return iface.Call(procName, tailPC.(tla.TLAValue).AsString(), argVals...)
}

// Return executes the entire semantics of an MPCal procedure return.
// This involves:
// - popping a record from top-of-stack (which must not be empty), which contains many pairs of name -> TLA+ value
//   - for each pair, find the resource with the given name, and write the given TLA+ value to it
//
// This ensures all the callee's local state variables have their values restored to how they were before the procedure call.
// The program counter, with the label to return to, is included in the state variables to "restore", so no special logic
// is needed for that.
//
// This method should be called at the end of a critical section.
func (iface *ArchetypeInterface) Return() error {
	stack := iface.RequireArchetypeResource(".stack")
	// rewrite the stack, "popping" one the head element
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	err = iface.Write(stack, nil, tla.TLA_Tail(stackVal))
	if err != nil {
		return err
	}

	// each element of the record ("function") at stack head maps a resource name to a resource value,
	// with the associated value being a snapshot of that resource that must be restored
	// this includes the magic .pc resource, which will effectively jump us back to the caller
	headRec := tla.TLA_Head(stackVal)
	headFn := headRec.AsFunction()
	it := headFn.Iterator()
	for !it.Done() {
		name, value := it.Next()
		handle := iface.RequireArchetypeResource(name.(tla.TLAValue).AsString())
		err = iface.Write(handle, nil, value.(tla.TLAValue))
		if err != nil {
			return err
		}
	}
	return nil
}
