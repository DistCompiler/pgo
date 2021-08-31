package distsys

import (
	"fmt"
	"github.com/benbjohnson/immutable"
)

// ArchetypeInterface provides an archetype-centric interface to an MPCalContext.
// While just an opaque wrapper for an MPCalContext, it provides a separation of concerns between:
// (1) how to configure and run and MPCal archetype (available via a plain MPCalContext)
// (2) how the MPCal archetype's code accesses its configuration and internal state while running (available via ArchetypeInterface)
type ArchetypeInterface struct {
	ctx *MPCalContext
}

// Self returns the associated archetype's self binding. Requires a configured archetype.
func (iface ArchetypeInterface) Self() TLAValue {
	iface.ctx.requireArchetype()
	return iface.ctx.self
}

func (iface ArchetypeInterface) ensureCriticalSectionWith(handle ArchetypeResourceHandle) {
	iface.ctx.dirtyResourceHandles[handle] = true
}

// Write models the MPCal statement resourceFromHandle[indices...] := value.
// It is expected to be called only from PGo-generated code.
func (iface ArchetypeInterface) Write(handle ArchetypeResourceHandle, indices []TLAValue, value TLAValue) (err error) {
	iface.ensureCriticalSectionWith(handle)
	res := iface.ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	err = res.WriteValue(value)
	return
}

// Read models the MPCal expression resourceFromHandle[indices...].
// If is expected to be called only from PGo-generated code.
func (iface ArchetypeInterface) Read(handle ArchetypeResourceHandle, indices []TLAValue) (value TLAValue, err error) {
	iface.ensureCriticalSectionWith(handle)
	res := iface.ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	value, err = res.ReadValue()
	return
}

// Fairness returns an int, which, from call to call, for the same id, follows the looping sequence 0..ceiling
// This allows an archetype to explore different branches of an either statement (each of which has its own id) during execution.
func (iface ArchetypeInterface) Fairness(id string, ceiling int) int {
	fairnessCounters := iface.ctx.fairnessCounters
	counter := fairnessCounters[id]
	var nextCounter int
	if counter >= ceiling - 1 {
		nextCounter = 0
	} else {
		nextCounter = counter + 1
	}
	fairnessCounters[id] = nextCounter
	return counter
}

// GetConstant returns the constant operator bound to the given name as a variadic Go function.
// The function is generated in DefineConstantOperator, and is expected to check its own arguments.
func (iface ArchetypeInterface) GetConstant(name string) func(args... TLAValue) TLAValue {
	fn, wasFound := iface.ctx.constantDefns[name]
	if !wasFound {
		panic(fmt.Errorf("could not find constant definition %s", name))
	}
	return fn
}

// RequireArchetypeResource returns a handle to the archetype resource with the given name. It panics if this resource
// does not exist.
func (iface ArchetypeInterface) RequireArchetypeResource(name string) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle(name)
	_ = iface.ctx.getResourceByHandle(handle)
	return handle
}

// RequireArchetypeResourceRef returns a handle to the archetype resource with the given name, when the name refers
// to a resource that was passed by ref in MPCal (in Go, ref-passing has an extra indirection that must be followed).
// If the resource does not exist, or an invalid indirection is used, this method will panic.
func (iface ArchetypeInterface) RequireArchetypeResourceRef(name string) (ArchetypeResourceHandle, error) {
	ptr := iface.RequireArchetypeResource(name)
	ptrVal, err := iface.Read(ptr, nil)
	if err != nil {
		return "", err
	}
	return iface.RequireArchetypeResource(ptrVal.AsString()), nil
}

// EnsureArchetypeResourceLocal ensures that a local state variable exists (local to an archetype or procedure), creating
// it with the given default value if not.
func (iface ArchetypeInterface) EnsureArchetypeResourceLocal(name string, value TLAValue) {
	_ = iface.ctx.ensureArchetypeResource(name, LocalArchetypeResourceMaker(value))
}

// ReadArchetypeResourceLocal is a short-cut to reading a local state variable, which, unlike other resources, is
// statically known to not require any critical section management. It will return the resource's value as-is, and
// will crash if the named resource isn't exactly a local state variable.
func (iface ArchetypeInterface) ReadArchetypeResourceLocal(name string) TLAValue {
	return iface.ctx.getResourceByHandle(ArchetypeResourceHandle(name)).(*LocalArchetypeResource).value
}

func (iface ArchetypeInterface) getCriticalSection(name string) MPCalCriticalSection {
	if criticalSection, ok := iface.ctx.jumpTable[name]; ok {
		return criticalSection
	}
	panic(fmt.Errorf("could not find critical section %s", name))
}


func (iface ArchetypeInterface) getProc(name string) MPCalProc {
	if proc, ok := iface.ctx.procTable[name]; ok {
		return proc
	}
	panic(fmt.Errorf("could not find procedure %s", name))
}

var defaultLocalArchetypeResourceMaker = LocalArchetypeResourceMaker(TLAValue{})

func (iface ArchetypeInterface) ensureArchetypeResourceLocal(name string) ArchetypeResourceHandle {
	return iface.ctx.ensureArchetypeResource(name, defaultLocalArchetypeResourceMaker)
}

// Goto sets the running archetype's program counter to the target value.
// It will panic if the target is not a valid label name.
// This method should be called at the end of a critical section.
func (iface ArchetypeInterface) Goto(target string) error {
	_ = iface.getCriticalSection(target) // crash now if the new pc isn't in the jump table
	pc := iface.RequireArchetypeResource(".pc")
	return iface.Write(pc, nil, NewTLAString(target))
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
func (iface ArchetypeInterface) Call(procName string, returnPC string, argVals... TLAValue) error {
	proc := iface.getProc(procName)
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}

	if len(argVals) > len(proc.StateVars) {
		panic(fmt.Errorf("too many arguments when calling procedure %s", proc.Name))
	}

	// store all the callee's locals into the stack, to avoid clobbering them while the procedure runs
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	builder.Set(NewTLAString(".pc"), NewTLAString(returnPC)) // store return address
	for argIdx, argVarName := range proc.StateVars {
		argHandle := iface.ensureArchetypeResourceLocal(argVarName)

		// save original argument value
		argVal, err := iface.Read(argHandle, nil)
		if err != nil {
			return err
		}
		builder.Set(NewTLAString(argVarName), argVal)

		// write the argument value into callee state (if we are still dealing with args; extra state vars are not args)
		if argIdx < len(argVals) {
			err = iface.Write(argHandle, nil, argVals[argIdx])
			if err != nil {
				return err
			}
		}
	}
	newStackRecord := TLAValue{&tlaValueFunction{builder.Map()}}

	// push the record onto the stack via tuple concatenation
	err = iface.Write(stack, nil, TLA_OSymbol(NewTLATuple(newStackRecord), stackVal))
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
// This method, like those it wraps, should be called at the end of a critical section.
func (iface ArchetypeInterface) TailCall(procName string, argVals... TLAValue) error {
	// pull the top-of-stack return address from the initial stack, so we can use it in the tail-call process below
	stack := iface.RequireArchetypeResource(".stack")
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	tailPC, ok := stackVal.AsFunction().Get(NewTLAString(".pc"))
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
	return iface.Call(procName, tailPC.(TLAValue).AsString(), argVals...)
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
func (iface ArchetypeInterface) Return() error {
	stack := iface.RequireArchetypeResource(".stack")
	// rewrite the stack, "popping" one the head element
	stackVal, err := iface.Read(stack, nil)
	if err != nil {
		return err
	}
	err = iface.Write(stack, nil, TLA_Tail(stackVal))
	if err != nil {
		return err
	}

	// each element of the record ("function") at stack head maps a resource name to a resource value,
	// with the associated value being a snapshot of that resource that must be restored
	// this includes the magic .pc resource, which will effectively jump us back to the caller
	headRec := TLA_Head(stackVal)
	headFn := headRec.AsFunction()
	it := headFn.Iterator()
	for !it.Done() {
		name, value := it.Next()
		handle := iface.RequireArchetypeResource(name.(TLAValue).AsString())
		err = iface.Write(handle, nil, value.(TLAValue))
		if err != nil {
			return err
		}
	}
	return nil
}
