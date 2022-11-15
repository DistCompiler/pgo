package distsys

import (
	"errors"
	"fmt"
	"reflect"
	"sync"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"go.uber.org/multierr"
)

// ErrAssertionFailed will be returned by an archetype function in the
// generated code if an assertion fails.
var ErrAssertionFailed = errors.New("assertion failed")

// ErrCriticalSectionAborted it may be returned by any resource operations that can return an error. If it is returned
// the critical section that was performing that operation will be rolled back and canceled.
var ErrCriticalSectionAborted = errors.New("MPCal critical section aborted")

// ErrDone exists only to be returned by archetype code implementing the Done label
var ErrDone = errors.New("a pseudo-error to indicate an archetype has terminated execution normally")

// ErrProcedureFallthrough indicated an archetype reached the Error label, and crashed.
var ErrProcedureFallthrough = errors.New("control has reached the end of a procedure body without reaching a return")

// MPCalJumpTable is an immutable table of all critical sections a given collection of archetypes and procedures might jump to
type MPCalJumpTable map[string]MPCalCriticalSection

// MakeMPCalJumpTable constructs a jump table from a sequence of MPCalCriticalSection records
func MakeMPCalJumpTable(criticalSections ...MPCalCriticalSection) MPCalJumpTable {
	tbl := make(MPCalJumpTable)
	for _, criticalSection := range criticalSections {
		tbl[criticalSection.Name] = criticalSection
	}
	return tbl
}

// MPCalCriticalSection holds metadata for a single MPCal critical section
type MPCalCriticalSection struct {
	Name string                               // the critical section's full name (in the form ArchetypeOrProcedureName.LabelName)
	Body func(iface ArchetypeInterface) error // code for executing this critical section. should be straight-line code that runs in a bounded amount of time.
}

// MPCalProcTable is an immutable table of all procedures a given collection of archetypes and procedures might call
type MPCalProcTable map[string]MPCalProc

// MakeMPCalProcTable constructs a table of procedure metadata from a sequence of MPCalProc
func MakeMPCalProcTable(procs ...MPCalProc) MPCalProcTable {
	tbl := make(MPCalProcTable)
	for _, proc := range procs {
		tbl[proc.Name] = proc
	}
	return tbl
}

// MPCalProc holds all metadata necessary for calling an MPCal procedure
type MPCalProc struct {
	Name      string                               // the procedure's name, as given in the MPCal model
	Label     string                               // the fully qualified name of the procedure's first label
	StateVars []string                             // the fuly-qualified names of all the procedure's local state variables, including arguments and refs
	PreAmble  func(iface ArchetypeInterface) error // code to initialize local state variables, writing any initial values they might have. runs as part of a call to the procedure.
}

// MPCalArchetype holds all the metadata necessary to run an archetype, aside from user-provided configuration
type MPCalArchetype struct {
	Name                                 string                         // the archetype's name, as it reads in the MPCal source code
	Label                                string                         // the full label name of the first critical section this archetype should execute
	RequiredRefParams, RequiredValParams []string                       // names of ref and non-ref parameters
	JumpTable                            MPCalJumpTable                 // a cross-reference to a jump table containing this archetype's critical sections
	ProcTable                            MPCalProcTable                 // a cross-reference to a table of all MPCal procedures this archetype might call
	PreAmble                             func(iface ArchetypeInterface) // called on archetype start-up, this code should initialize any local variables the archetype has
}

// ArchetypeResourceHandle encapsulates a reference to an ArchetypeResource.
// These handles insulate the end-user from worrying about the specifics of resource lifetimes, logging, and
// crash recovery scenarios.
type ArchetypeResourceHandle string

// MPCalContext manages the internal lifecycle of a compiled MPCal model's execution.
// This includes:
// - critical section state
// - configured resources, constant values, and the archetype's self binding
// - the ability to start and stop the archetype, via Run and Close.
type MPCalContext struct {
	archetype MPCalArchetype

	self      tla.Value
	resources map[ArchetypeResourceHandle]ArchetypeResource

	// state for ArchetypeInterface.NextFairnessCounter
	fairnessCounter FairnessCounter

	jumpTable MPCalJumpTable
	procTable MPCalProcTable

	eventState            trace.EventState
	apparentResourceNames map[ArchetypeResourceHandle]string

	dirtyResourceHandles map[ArchetypeResourceHandle]bool

	// iface points right back to this *MPCalContext; used to separate external and internal APIs
	iface ArchetypeInterface

	constantDefns map[string]func(args ...tla.Value) tla.Value

	// whether anything related to Run() is allowed. true if we were created by NewMPCalContext, false otherwise
	allowRun bool

	runStateLock  sync.Mutex
	exitRequested bool // has an exit been requested yet? (can be true any time, even if the archetype never runs)
	// Used to track Run execution. non-nil if the archetype is running, and, if !exitRequested, we can request an exit.
	requestExit chan struct{}
	// Used for tracking execution of Run. We never intend to write to this, just read from it and block.
	// Then, when we terminate (or preempt running at all), we close it and all readers (Stop case 1) will unblock
	awaitExit chan struct{}
}

type MPCalContextConfigFn func(ctx *MPCalContext)

// NewMPCalContext is the principal function for creating MPCalContext instances.
// It returns a fully-constructed context, executing configuration steps internally.
// The self parameter refers to the archetype's "self" binding, and should be an appropriately unique TLA+ value, with
// the same semantics as used in PlusCal and TLC.
// The archetype parameter should refer to a static PGo-compiled structure, which contains all intrinsic information
// about how a given archetype should run.
// This information includes:
// - necessary value-level archetype parameters (no ref keyword)
// - necessary archetype resources (with ref keyword, and with or without [_])
// - control flow information, pointers to routines for the relevant critical sections
//
// See MPCalArchetype for further information.
//
// For information on both necessary and optional configuration, see MPCalContextConfigFn, which can be provided to
// NewMPCalContext in order to set constant values, pass archetype parameters, and any other configuration information.
func NewMPCalContext(self tla.Value, archetype MPCalArchetype, configFns ...MPCalContextConfigFn) *MPCalContext {
	ctx := &MPCalContext{
		archetype: archetype,

		self:            self,
		resources:       make(map[ArchetypeResourceHandle]ArchetypeResource),
		fairnessCounter: MakeRoundRobinFairnessCounter(),

		jumpTable: archetype.JumpTable,
		procTable: archetype.ProcTable,

		eventState: trace.EventState{
			ArchetypeName: archetype.Name,
			ArchetypeSelf: self,
		},
		apparentResourceNames: make(map[ArchetypeResourceHandle]string),

		dirtyResourceHandles: make(map[ArchetypeResourceHandle]bool),

		// iface

		constantDefns: make(map[string]func(args ...tla.Value) tla.Value),

		allowRun: true,

		awaitExit: make(chan struct{}),
	}
	ctx.iface = ArchetypeInterface{ctx: ctx}

	ctx.ensureArchetypeResource(".pc", NewLocalArchetypeResource(tla.MakeString(archetype.Label)))
	ctx.ensureArchetypeResource(".stack", NewLocalArchetypeResource(tla.MakeTuple()))
	for _, configFn := range configFns {
		configFn(ctx)
	}
	return ctx
}

func (ctx *MPCalContext) Archetype() MPCalArchetype {
	ctx.requireRunnable()
	return ctx.archetype
}

// requireRunnable should be called at the start of any method that requires ctx to have more than
// MPCalContext.constantDefns initialised. Most user-accessible functions will need this.
func (ctx *MPCalContext) requireRunnable() {
	if !ctx.allowRun {
		panic(fmt.Errorf("this operation requires an MPCalContext that is runnable, not one that was acquired via NewMPCalContextWithoutArchetype"))
	}
}

// EnsureMPCalContextConfigs allows multiple MPCalContext configuration options to be treated as one.
// This is useful when there is a set of options common to several contexts, and you want a simple way to just "import"
// them into each configuration. Without this construct, something like a slice append() is needed, which makes
// the code harder to read and adds even more complexity to the already-complicated and deeply nested NewMPCalContext call.
// With this construct, you can just add the whole collection as a configuration option, and continue listing custom
// configuration as normal.
func EnsureMPCalContextConfigs(configs ...MPCalContextConfigFn) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		for _, config := range configs {
			config(ctx)
		}
	}
}

// EnsureArchetypeRefParam binds an ArchetypeResource to the provided name.
// The name must match one of the archetype's parameter names, and must refer to a ref parameter.
// Calling MPCalContext.Run while failing to meet these conditions will panic.
// The resource is provided via the res argument.
func EnsureArchetypeRefParam(name string, res ArchetypeResource) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireRunnable()
		resourceName := "&" + ctx.archetype.Name + "." + name
		refName := ctx.archetype.Name + "." + name
		_ = ctx.ensureArchetypeResource(resourceName, res)
		_ = ctx.ensureArchetypeResource(refName, NewLocalArchetypeResource(tla.MakeString(resourceName)))
	}
}

// EnsureArchetypeValueParam binds a Value to the provided name.
// The name must match one of the archetype's parameter names, and must not refer to a ref parameter. If these conditions
// are not met, attempting to call MPCalContext.Run will panic.
// Like with EnsureArchetypeRefParam, the provided value may not be used, if existing state has been recovered from storage.
func EnsureArchetypeValueParam(name string, value tla.Value) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireRunnable()
		_ = ctx.ensureArchetypeResource(ctx.archetype.Name+"."+name, NewLocalArchetypeResource(value))
	}
}

// DefineConstantValue will bind a constant name to a provided TLA+ value.
// The name must match one of the constants declared in the MPCal module, for this option to make sense.
// Not all constants need to be defined, as long as they are not accessed at runtime.
func DefineConstantValue(name string, value tla.Value) MPCalContextConfigFn {
	return DefineConstantOperator(name, func() tla.Value {
		return value
	})
}

// DefineConstantOperator is a more generic form of DefineConstantValue, which allows the specification of
// higher-order constants.
//
// e.g:
//
//		CONSTANT IM_SPECIAL(_, _)
//
// The above example could be configured as such, if one wanted to approximate `IM_SPECIAL(a, b) == a + b`:
//
// 		DefineConstantOperator("IM_SPECIAL", func(a, b Value) Value {
//      	return ModulePlusSymbol(a, b)
//      })
//
// Note that the type of defn is interface{} in order to accommodate variadic functions, with reflection being used
// to determine the appropriate arity information. Any functions over Value, returning a single Value, are accepted.
// To match TLA+ semantics, the provided function should behave as effectively pure.
//
// Valid inputs include:
//
// 		func() Value { ... }
// 		func(a, b, c, Value) Value { ... }
// 		func(variadic... Value) Value { ... }
//		func(a Value, variadic... Value) Value { ... }
//
func DefineConstantOperator(name string, defn interface{}) MPCalContextConfigFn {
	doubleDefnCheck := func(ctx *MPCalContext) {
		if _, ok := ctx.constantDefns[name]; ok {
			panic(fmt.Errorf("constant definition %s defined twice", name))
		}
	}

	switch defn := defn.(type) {
	case func(args ...tla.Value) tla.Value: // special case: if the defn is variadic, we can safely pass it straight through without reflection weirdness
		return func(ctx *MPCalContext) {
			doubleDefnCheck(ctx)
			ctx.constantDefns[name] = defn
		}
		// TODO: maybe special-case a simpler setup for arities 0-3 or something, if perf is impacted by what lurks below
	default: // general case: use reflection to make sure the function looks "about right", and call it the generic way
		defnVal := reflect.ValueOf(defn)
		defnTyp := reflect.TypeOf(defn)
		ValueTyp := reflect.TypeOf(tla.Value{})
		ValuesType := reflect.TypeOf([]tla.Value{})

		// reflection-based sanity checks. we want fixed-arity functions of the shape func(Value...) Value
		if defnTyp.Kind() != reflect.Func {
			panic(fmt.Errorf("constant operator definition %s is not a function, is %v", name, defn))
		}
		argCount := defnTyp.NumIn()
		if defnTyp.NumOut() != 1 {
			panic(fmt.Errorf("constant operator definition %s does not have exactly one return value, instead it has %d", name, defnTyp.NumOut()))
		}
		if !ValueTyp.AssignableTo(defnTyp.Out(0)) {
			panic(fmt.Errorf("constant operator definition %s does not return a Value; returns a %v instead", name, defnTyp.Out(0)))
		}
		for i := 0; i < argCount; i++ {
			if i == argCount-1 && defnTyp.IsVariadic() {
				if !ValuesType.AssignableTo(defnTyp.In(i)) {
					panic(fmt.Errorf("constant operator definition %s argument %d, which is its variadic argument, does not have type []Value; is a %v instead", name, i, defnTyp.In(i)))
				}
			} else if !ValueTyp.AssignableTo(defnTyp.In(i)) {
				panic(fmt.Errorf("constant operator definition %s argument %d does not have type Value; is a %v instead", name, i, defnTyp.In(i)))
			}
		}

		return func(ctx *MPCalContext) {
			doubleDefnCheck(ctx)

			argVals := make([]reflect.Value, argCount)
			ctx.constantDefns[name] = func(args ...tla.Value) tla.Value {
				if len(argVals) != len(args) {
					panic(fmt.Errorf("constant operator %s called with wrong number of arguments. expected %d arguments, got %v", name, len(argVals), args))
				}
				// convert arguments to a pre-allocated array of reflect.Value, to avoid unnecessary slice allocation
				for i, arg := range args {
					argVals[i] = reflect.ValueOf(arg)
				}

				// invoke the function; may crash with an arity error, but should otherwise work in all cases
				result := defnVal.Call(argVals)

				// reset argVals array to zero-values, to avoid accidentally caching arguments
				for i := range argVals {
					argVals[i] = reflect.Value{}
				}

				return result[0].Interface().(tla.Value)
			}
		}
	}
}

func SetFairnessCounter(fairnessCounter FairnessCounter) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.fairnessCounter = fairnessCounter
	}
}

func SetTraceRecorder(recorder trace.Recorder) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.eventState.Recorder = recorder
	}
}

// NewMPCalContextWithoutArchetype creates an almost-uninitialized context, useful for calling pure TLA+ operators.
// The returned context will cause almost all operations to panic, except:
// - configuring constant definitions
// - passing the result of MPCalContext.IFace() to a plain TLA+ operator
func NewMPCalContextWithoutArchetype(configFns ...MPCalContextConfigFn) *MPCalContext {
	// only set constant defns; everything else is left zero-values, and all relevant ops should check
	// MPCalContext.requireRunnable before running
	ctx := &MPCalContext{
		constantDefns: make(map[string]func(args ...tla.Value) tla.Value),
	}
	ctx.iface = ArchetypeInterface{ctx}

	for _, configFn := range configFns {
		configFn(ctx)
	}

	return ctx
}

// IFace provides an ArchetypeInterface, giving access to methods considered MPCal-internal.
// This is useful when directly calling pure TLA+ operators using a context constructed via NewMPCalContextWithoutArchetype,
// and is one of very few operations that will work on such a context.
func (ctx *MPCalContext) IFace() ArchetypeInterface {
	return ctx.iface
}

func (ctx *MPCalContext) ensureArchetypeResource(name string, res ArchetypeResource) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle(name)
	ctx.resources[handle] = res
	ctx.apparentResourceNames[handle] = name
	return handle
}

func (ctx *MPCalContext) getResourceByHandle(handle ArchetypeResourceHandle) ArchetypeResource {
	res, ok := ctx.resources[handle]
	if !ok {
		panic(fmt.Errorf("could not find resource with name %v", handle))
	}
	return res
}

func (ctx *MPCalContext) abort() {
	var nonTrivialAborts []chan struct{}
	for resHandle := range ctx.dirtyResourceHandles {
		ch := ctx.getResourceByHandle(resHandle).Abort()
		if ch != nil {
			nonTrivialAborts = append(nonTrivialAborts, ch)
		}
	}
	for _, ch := range nonTrivialAborts {
		<-ch
	}
	ctx.eventState.DropEvent()

	// the go compiler optimizes this to a map clear operation
	for resHandle := range ctx.dirtyResourceHandles {
		delete(ctx.dirtyResourceHandles, resHandle)
	}
}

func (ctx *MPCalContext) commit() (err error) {
	// dispatch all parts of the pre-commit phase asynchronously, so we only wait as long as the slowest resource
	var nonTrivialPreCommits []chan error
	for resHandle := range ctx.dirtyResourceHandles {
		ch := ctx.getResourceByHandle(resHandle).PreCommit()
		if ch != nil {
			nonTrivialPreCommits = append(nonTrivialPreCommits, ch)
		}
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

	// run through dirty resources twice in order to reach VClock fixpoint
	if ctx.eventState.HasRecorder() {
		for i := 0; i < 2; i++ {
			for handle := range ctx.dirtyResourceHandles {
				ctx.eventState.UpdateVClock(
					ctx.getResourceByHandle(handle).VClockHint(ctx.eventState.VClock()))
			}
		}
	}
	// commit with fully-updated clock
	ctx.eventState.CommitEvent()

	// same as above, run all the commit processes async
	var nonTrivialCommits []chan struct{}
	for resHandle := range ctx.dirtyResourceHandles {
		ch := ctx.getResourceByHandle(resHandle).Commit()
		if ch != nil {
			nonTrivialCommits = append(nonTrivialCommits, ch)
		}
	}
	for _, ch := range nonTrivialCommits {
		<-ch
	}

	// the go compiler optimizes this to a map clear operation
	for resHandle := range ctx.dirtyResourceHandles {
		delete(ctx.dirtyResourceHandles, resHandle)
	}
	return
}

func (ctx *MPCalContext) preRun() {
	// sanity checks, so we don't try to run with missing resources, refs passed as vals, or vals passed as refs:
	for _, requiredValParam := range ctx.archetype.RequiredValParams {
		if _, ok := ctx.resources[ArchetypeResourceHandle(requiredValParam)]; !ok {
			panic(fmt.Errorf("archetype resource val param unspecified during initialization: %s", requiredValParam))
		}
		if _, ok := ctx.resources[ArchetypeResourceHandle("&"+requiredValParam)]; ok {
			panic(fmt.Errorf("archetype resource val param was configured as a ref param: %s", requiredValParam))
		}
	}
	for _, requiredRefParam := range ctx.archetype.RequiredRefParams {
		if _, ok := ctx.resources[ArchetypeResourceHandle(requiredRefParam)]; !ok {
			panic(fmt.Errorf("archetype resource ref param unspecified during initialization: %s", requiredRefParam))
		}
		if _, ok := ctx.resources[ArchetypeResourceHandle("&"+requiredRefParam)]; !ok {
			panic(fmt.Errorf("archetype resource ref param was configured as a val param: %s", requiredRefParam))
		}
	}

	// set up any local state variables that the archetype might have
	ctx.archetype.PreAmble(ctx.iface)
}

// Run will execute the archetype loaded into ctx.
// This routine assumes all necessary information (resources, constant definitions) have been pre-loaded, and
// encapsulates the entire archetype's execution.
//
// This method may return the following outcomes (be sure to use errors.Is, see last point):
// - nil: the archetype reached the Done label, and has ended of its own accord with no issues
// - ErrAssertionFailed: an assertion in the MPCal code failed (this error will be wrapped by a string describing the assertion)
// - ErrProcedureFallthrough: the Error label was reached, which is an error in the MPCal code
// - one or more (possibly aggregated, possibly with one of the above errors) implementation-defined errors produced by failing resources
func (ctx *MPCalContext) Run() (err error) {
	ctx.requireRunnable() // basic sanity, no-one should be calling Run on a non-runnable context.

	hasAlreadyClosed := func() bool {
		ctx.runStateLock.Lock()
		defer ctx.runStateLock.Unlock()
		if ctx.requestExit != nil {
			panic(fmt.Errorf("this context has already been run; you cannot run a context twice"))
		}

		// if we already know an exit was requested before even starting, we are in Stop case 2a and should not run
		if ctx.exitRequested {
			return true
		}

		// this single-element buffered channel will be written to 0 or one times:
		// 0. if no-one called Stop
		// 1. on the first call to Stop that is concurrent with Run
		ctx.requestExit = make(chan struct{}, 1)
		return false
	}()
	if hasAlreadyClosed {
		return nil
	}

	// clean up all our resources and notify any interested parties that we have terminated.
	defer func() {
		// do clean-up, merging any errors into the error we return
		err = multierr.Append(err, ctx.cleanupResources())
		// report the error to the tracer before dying, since this might be more useful than a truncated trace
		if err != nil {
			ctx.eventState.CrashEvent(err)
		}
		// send any notifications
		func() {
			ctx.runStateLock.Lock()
			defer ctx.runStateLock.Unlock()
			// notify all existing exit-requesters by closing the channel: any situations hitting Stop case 1
			close(ctx.awaitExit)
			// once we're done reporting our exit, null the requestExit channel so the next person to call Stop
			// hits case 2. we have already exited at this point.
			ctx.requestExit = nil
		}()
	}()

	// sanity checks and other setup, done here, so you can initialize a context, not call Run, and not get checks
	ctx.preRun()

	pc := ctx.iface.RequireArchetypeResource(".pc")
	for {
		// all error control flow lives here, reached by "continue" from below
		switch err {
		case nil: // everything is fine; carry on
		case ErrCriticalSectionAborted:
			ctx.abort()
			// we want to keep the invariant that always err is nil after the error
			// handling in the beginning of the loop. It's easier to read the code and
			// reason about it with this invariant.
			//nolint:ineffassign
			err = nil
		case ErrDone: // signals that we're done; quit successfully
			return nil
		default:
			// some other error; return it to caller, we probably crashed
			return err
		}

		// poll the done channel for Close calls.
		// this should execute "regularly", since all archetype label implementations are non-blocking
		// (except commits, which we discretely ignore; you can't cancel them, anyhow)
		select {
		case <-ctx.requestExit:
			return nil
		default: // pass
		}

		ctx.eventState.BeginEvent()

		var pcVal tla.Value
		pcVal, err = ctx.iface.Read(pc, nil)
		if err != nil {
			continue
		}
		pcValStr := pcVal.AsString()

		ctx.fairnessCounter.BeginCriticalSection(pcValStr)
		criticalSection := ctx.iface.getCriticalSection(pcValStr)
		err = criticalSection.Body(ctx.iface)
		if err != nil {
			continue
		}
		err = ctx.commit()
	}
}

// Stop requests that the archetype running under this context exits, roughly like the POSIX interrupt signal.
// The archetype's execution will be pre-empted at the next label boundary or critical section retry.
// This function will block until the exit is complete, and all resources have been cleaned up.
// If the archetype has not started, this function will ensure that it does not, without waiting.
func (ctx *MPCalContext) Stop() {
	ctx.requireRunnable()

	func() {
		ctx.runStateLock.Lock()
		defer ctx.runStateLock.Unlock()
		if ctx.requestExit != nil {
			// case 1a: the archetype is running, and we are the first to ask it to stop, so we should ask.
			//          future requests will not need to do this, as it will already have been done.
			if !ctx.exitRequested {
				ctx.requestExit <- struct{}{}
			}

			// case 1b: the archetype is running right now and a stop has already been requested
			//          either way, we should wait for it to stop
		} else {
			// case 2: the archetype is not running right now
			if !ctx.exitRequested {
				// case 2a: the archetype is not running, and no-one has requested that it doesn't run
				//          so, set the flag such that it will never run, and indicate that, semantically, it is now stopped.
				ctx.exitRequested = true
				select {
				case <-ctx.awaitExit: // do nothing; the archetype has already run and stopped, so this channel is already closed
				default:
					// the archetype has not started yet, so preemptively close the waiting channel, as it will now never start.
					close(ctx.awaitExit)
				}
			}
			// case 2b: the archetype is not running, and is already flagged not to run. nothing to do here.
		}
	}()
	<-ctx.awaitExit
}

func (ctx *MPCalContext) cleanupResources() (err error) {
	// Note that we should close all the resources, not just the dirty ones.
	for _, res := range ctx.resources {
		cerr := res.Close()
		err = multierr.Append(err, cerr)
	}
	return
}
