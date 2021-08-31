package distsys

import (
	"errors"
	"fmt"
	"reflect"
	"sync"

	"go.uber.org/multierr"
)

// ErrAssertionFailed will be returned by an archetype function in the
// generated code if an assertion fails.
var ErrAssertionFailed = errors.New("assertion failed")

// ErrCriticalSectionAborted it may be returned by any resource operations that can return an error. If it is returned
// the critical section that was performing that operation will be rolled back and canceled.
var ErrCriticalSectionAborted = errors.New("MPCal critical section aborted")

// ErrContextClosed will be returned if the context of an archetype is closed.
var ErrContextClosed = errors.New("MPCal context closed")

// ErrDone exists only to be returned by archetype code implementing the Done label
var ErrDone = errors.New("A pseudo-error to indicate an archetype has terminated execution normally")

// ErrProcedureFallthrough indicated an archetype reached the Error label, and crashed.
var ErrProcedureFallthrough = errors.New("control has reached the end of a procedure body without reaching a return")

type MPCalJumpTable map[string]MPCalCriticalSection

func MakeMPCalJumpTable(criticalSections... MPCalCriticalSection) MPCalJumpTable {
	tbl := make(MPCalJumpTable)
	for _, criticalSection := range criticalSections {
		tbl[criticalSection.Name] = criticalSection
	}
	return tbl
}

type MPCalCriticalSection struct {
	Name string
	Body func(iface ArchetypeInterface) error
}

type MPCalProcTable map[string]MPCalProc

func MakeMPCalProcTable(procs... MPCalProc) MPCalProcTable {
	tbl := make(MPCalProcTable)
	for _, proc := range procs {
		tbl[proc.Name] = proc
	}
	return tbl
}

type MPCalProc struct {
	Name string
	Label string
	StateVars []string
	PreAmble func(iface ArchetypeInterface) error
}

type MPCalArchetype struct {
	Name string
	Label string
	RequiredRefParams, RequiredValParams []string
	JumpTable MPCalJumpTable
	ProcTable MPCalProcTable
	PreAmble func(iface ArchetypeInterface)
}

// ArchetypeResourceHandle encapsulates a reference to an ArchetypeResource.
// These handles insulate the end-user from worrying about the specifics of resource lifetimes, logging, and
// crash recovery scenarios.
type ArchetypeResourceHandle string

// ArchetypeResourceMaker encapsulates how a specific kind of ArchetypeResource is created.
// At its simplest, Make() should produce a fresh instance, and Configure will then be called on that instance
// in order to do any further configuration to it.
// This two-step process anticipates situations where the ArchetypeResource has been e.g reloaded from disk
// during crash recovery, but might still need some configuration (setting up any function objects, user-provided Go channels).
type ArchetypeResourceMaker interface {
	Make() ArchetypeResource
	Configure(res ArchetypeResource)
}

// ArchetypeResourceMakerFn short-cuts the common case where there is no Configure step.
// It implements that step as a no-op, while wrapping an ArchetypeResource-creating function.
type ArchetypeResourceMakerFn func() ArchetypeResource

var _ ArchetypeResourceMaker = new(ArchetypeResourceMakerFn)

func (mkFunc ArchetypeResourceMakerFn) Make() ArchetypeResource {
	return mkFunc()
}

func (mkFunc ArchetypeResourceMakerFn) Configure(ArchetypeResource) {
	// pass
}

// ArchetypeResourceMakerStruct aims to handle anything ArchetypeResourceMakerFn can't.
// It provides full customisation of both steps.
type ArchetypeResourceMakerStruct struct {
	MakeFn      func() ArchetypeResource
	ConfigureFn func(res ArchetypeResource)
}

var _ ArchetypeResourceMaker = ArchetypeResourceMakerStruct{}

func (mkStruct ArchetypeResourceMakerStruct) Make() ArchetypeResource {
	return mkStruct.MakeFn()
}

func (mkStruct ArchetypeResourceMakerStruct) Configure(res ArchetypeResource) {
	mkStruct.ConfigureFn(res)
}

// MPCalContext manages the internal lifecycle of a compiled MPCal model's execution.
// This includes:
// - critical section state
// - configured resources, constant values, and the archetype's self binding
// - the ability to start and stop the archetype, via Run and Close.
type MPCalContext struct {
	archetype MPCalArchetype

	self TLAValue
	resources map[ArchetypeResourceHandle]ArchetypeResource
	fairnessCounters map[string]int

	jumpTable MPCalJumpTable
	procTable MPCalProcTable

	dirtyResourceHandles map[ArchetypeResourceHandle]bool

	// iface points right back to this *MPCalContext; used to separate external and internal APIs
	iface ArchetypeInterface

	constantDefns map[string]func(args... TLAValue)TLAValue

    done   chan struct{}
    events chan struct{}

    lock   sync.Mutex
    closed bool
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
func NewMPCalContext(self TLAValue, archetype MPCalArchetype, configFns... MPCalContextConfigFn) *MPCalContext {
	ctx := &MPCalContext{
		archetype: archetype,

		self: self,
		resources: make(map[ArchetypeResourceHandle]ArchetypeResource),
		fairnessCounters: make(map[string]int),

		jumpTable: archetype.JumpTable,
		procTable: archetype.ProcTable,

		dirtyResourceHandles: make(map[ArchetypeResourceHandle]bool),

		// iface

		constantDefns:      make(map[string]func(args... TLAValue)TLAValue),

        done:   make(chan struct{}),
        events: make(chan struct{}, 2),

        closed: false,
	}
	ctx.iface = ArchetypeInterface{ctx: ctx}

	ctx.ensureArchetypeResource(".pc", LocalArchetypeResourceMaker(NewTLAString(archetype.Label)))
	ctx.ensureArchetypeResource(".stack", LocalArchetypeResourceMaker(NewTLATuple()))
	for _, configFn := range configFns {
		configFn(ctx)
	}
	return ctx
}

// requireArchetype should be called at the start of any method that requires ctx to have more than
// MPCalContext.constantDefns initialised. Most user-accessible functions will need this.
func (ctx *MPCalContext) requireArchetype() {
	bad := ctx.fairnessCounters == nil ||
		ctx.resources == nil ||
		ctx.dirtyResourceHandles == nil ||
		ctx.procTable == nil ||
		ctx.jumpTable == nil
	if bad {
		panic(fmt.Errorf("this operation requires an MPCalContext with an archetype. an MPCalContext without an archetype only makes sense when calling TLA+ operators directly"))
	}
}

// EnsureArchetypeRefParam binds an ArchetypeResource to the provided name.
// The name must match one of the archetype's parameter names, and must refer to a ref parameter.
// Calling MPCalContext.Run while failing to meet these conditions will panic.
// The resource is provided via an ArchetypeResourceMaker, which allows resource construction routines to properly
// handle restart scenarios, where an existing resource was persisted to disk, and the MPCalContext in use was recovered
// containing existing state.
func EnsureArchetypeRefParam(name string, maker ArchetypeResourceMaker) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireArchetype()
		resourceName := "&" + ctx.archetype.Name + "." + name
		refName := ctx.archetype.Name + "." + name
		_ = ctx.ensureArchetypeResource(resourceName, maker)
		_ = ctx.ensureArchetypeResource(refName, LocalArchetypeResourceMaker(NewTLAString(resourceName)))
	}
}

// EnsureArchetypeValueParam binds a TLAValue to the provided name.
// The name must match one of the archetype's parameter names, and must not refer to a ref parameter. If these conditions
// are not met, attempting to call MPCalContext.Run will panic.
// Like with EnsureArchetypeRefParam, the provided value may not be used, if existing state has been recovered from storage.
func EnsureArchetypeValueParam(name string, value TLAValue) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireArchetype()
		_ = ctx.ensureArchetypeResource(ctx.archetype.Name + "." + name, LocalArchetypeResourceMaker(value))
	}
}

// DefineConstantValue will bind a constant name to a provided TLA+ value.
// The name must match one of the constants declared in the MPCal module, for this option to make sense.
// Not all constants need to be defined, as long as they are not accessed at runtime.
func DefineConstantValue(name string, value TLAValue) MPCalContextConfigFn {
	return DefineConstantOperator(name, func() TLAValue {
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
// 		DefineConstantOperator("IM_SPECIAL", func(a, b TLAValue) TLAValue {
//      	return TLA_PlusSymbol(a, b)
//      })
//
// Note that the type of defn is interface{} in order to accommodate variadic functions, with reflection being used
// to determine the appropriate arity information. Any functions over TLAValue, returning a single TLAValue, are accepted.
// To match TLA+ semantics, the provided function should behave as effectively pure.
//
// Valid inputs include:
//
// 		func() TLAValue { ... }
// 		func(a, b, c, TLAValue) TLAValue { ... }
// 		func(variadic... TLAValue) TLAValue { ... }
//		func(a TLAValue, variadic... TLAValue) TLAValue { ... }
//
func DefineConstantOperator(name string, defn interface{}) MPCalContextConfigFn {
	doubleDefnCheck := func(ctx *MPCalContext) {
		if _, ok := ctx.constantDefns[name]; ok {
			panic(fmt.Errorf("constant definition %s defined twice", name))
		}
	}

	switch defn := defn.(type) {
	case func(args... TLAValue) TLAValue: // special case: if the defn is variadic, we can safely pass it straight through without reflection weirdness
		return func(ctx *MPCalContext) {
			doubleDefnCheck(ctx)
			ctx.constantDefns[name] = defn
		}
		// TODO: maybe special-case a simpler setup for arities 0-3 or something, if perf is impacted by what lurks below
	default: // general case: use reflection to make sure the function looks "about right", and call it the generic way
		defnVal := reflect.ValueOf(defn)
		defnTyp := reflect.TypeOf(defn)
		tlaValueTyp := reflect.TypeOf(TLAValue{})
		tlaValuesType := reflect.TypeOf([]TLAValue{})

		// reflection-based sanity checks. we want fixed-arity functions of the shape func(TLAValue...) TLAValue
		if defnTyp.Kind() != reflect.Func {
			panic(fmt.Errorf("constant operator definition %s is not a function, is %v", name, defn))
		}
		argCount := defnTyp.NumIn()
		if defnTyp.NumOut() != 1 {
			panic(fmt.Errorf("constant operator definition %s does not have exactly one return value, instead it has %d", name, defnTyp.NumOut()))
		}
		if !tlaValueTyp.AssignableTo(defnTyp.Out(0)) {
			panic(fmt.Errorf("constant operator definition %s does not return a TLAValue; returns a %v instead", name, defnTyp.Out(0)))
		}
		for i := 0; i < argCount; i++ {
			if i == argCount - 1 && defnTyp.IsVariadic() {
				if !tlaValuesType.AssignableTo(defnTyp.In(i)) {
					panic(fmt.Errorf("constant operator definition %s argument %d, which is its variadic argument, does not have type []TLAValue; is a %v instead", name, i, defnTyp.In(i)))
				}
			} else if !tlaValueTyp.AssignableTo(defnTyp.In(i)) {
				panic(fmt.Errorf("constant operator definition %s argument %d does not have type TLAValue; is a %v instead", name, i, defnTyp.In(i)))
			}
		}

		return func(ctx *MPCalContext) {
			doubleDefnCheck(ctx)

			argVals := make([]reflect.Value, argCount)
			ctx.constantDefns[name] = func(args... TLAValue) TLAValue {
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

				return result[0].Interface().(TLAValue)
			}
		}
	}
}

// NewMPCalContextWithoutArchetype creates an almost-unitialized context, useful for calling pure TLA+ operators.
// The returned context will cause almost all operations to panic, except:
// - configuring constant definitions
// - passing the result of MPCalContext.IFace() to a plain TLA+ operator
func NewMPCalContextWithoutArchetype(configFns... MPCalContextConfigFn) *MPCalContext {
	// only set constant defns; everything else is left zero-values, and all relevant ops should check
	// MPCalContext.requireArchetype before running
	ctx := &MPCalContext{
		constantDefns:      make(map[string]func(args... TLAValue)TLAValue),
	}
	ctx.iface = ArchetypeInterface{ctx}

	for _, configFn := range configFns {
		configFn(ctx)
	}

	return ctx
}

// archetypeEvent shows an event in an archetype execution process
type archetypeEvent int

const (
	// ArchetypeStarted denotes that the archetype execution has started
	archetypeStarted archetypeEvent = iota
	// ArchetypeFinished denotes that the archetype execution has finished
	archetypeFinished
)

// reportEvent will be called by MPCalContext.Run to update execution state. Affects MPCalContext.Close
func (ctx *MPCalContext) reportEvent(event archetypeEvent) {
	switch event {
	case archetypeStarted:
		select {
		case ctx.events <- struct{}{}:
		default:
			panic("archetype has started before")
		}
	case archetypeFinished:
		close(ctx.events)
	}
}

// IFace provides an ArchetypeInterface, giving access to methods considered MPCal-internal.
// This is useful when directly calling pure TLA+ operators using a context constructed via NewMPCalContextWithoutArchetype,
// and is one of very few operations that will work on such a context.
func (ctx *MPCalContext) IFace() ArchetypeInterface {
	return ctx.iface
}

func (ctx *MPCalContext) ensureArchetypeResource(name string, maker ArchetypeResourceMaker) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle(name)
	// this case accounts for the case where the desired resource already exists
	if res, ok := ctx.resources[handle]; ok {
		maker.Configure(res.(ArchetypeResource))
	} else {
		res := maker.Make()
		maker.Configure(res)
		ctx.resources[handle] = res
	}
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
		if _, ok := ctx.resources[ArchetypeResourceHandle("&" + requiredValParam)]; ok {
			panic(fmt.Errorf("archetype resource val param was configured as a ref param: %s", requiredValParam))
		}
	}
	for _, requiredRefParam := range ctx.archetype.RequiredRefParams {
		if _, ok := ctx.resources[ArchetypeResourceHandle(requiredRefParam)]; !ok {
			panic(fmt.Errorf("archetype resource ref param unspecified during initialization: %s", requiredRefParam))
		}
		if _, ok := ctx.resources[ArchetypeResourceHandle("&" + requiredRefParam)]; !ok {
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
// This method may return the following outcomes:
// - nil: the archetype reached the Done label, and has ended of its own accord
// - ErrContextClosed: Close was called on ctx
// - ErrAssertionFailed: an assertion in the MPCal code failed (this error will be wrapped by a string describing the assertion)
// - ErrProcedureFallthrough: the Error label was reached, which is an error in the MPCal code
func (ctx *MPCalContext) Run() error {
	// pre-sanity checks: an archetype should be provided if we're going to try and run one
	ctx.requireArchetype()
	// sanity checks and other setup, done here so you can init a context, not call Run, and not get checks
	ctx.preRun()

	// report start, and defer reporting completion to whenever this function returns
	ctx.reportEvent(archetypeStarted)
	defer ctx.reportEvent(archetypeFinished)

	pc := ctx.iface.RequireArchetypeResource(".pc")
	var err error
	for {
		// poll the done channel for Close calls.
		// this should execute "regularly", since all archetype label implementations are non-blocking
		// (except commits, which we discretely ignore; you can't cancel them, anyhow)
		select {
		case <-ctx.done:
			return ErrContextClosed
		default: // pass
		}

		// all error control flow lives here, reached by "continue" from below
		switch err {
		case nil: // everything is fine; carry on
		case ErrCriticalSectionAborted:
			ctx.abort()
			err = nil
		case ErrDone: // signals that we're done; quit successfully
			return nil
		default:
			// some other error; return it to caller, we probably crashed
			return err
		}

		var pcVal TLAValue
		pcVal, err = ctx.iface.Read(pc, nil)
		if err != nil {
			continue
		}
		pcValStr := pcVal.AsString()

		criticalSection := ctx.iface.getCriticalSection(pcValStr)
		err = criticalSection.Body(ctx.iface)
		if err != nil {
			continue
		}
		err = ctx.commit()
	}
}

// Done returns a channel that blocks until the context closes. Successive
// calls to Done return the same value.
func (ctx *MPCalContext) Done() <-chan struct{} {
	return ctx.done
}

// Close first stops execution of the running archetype that uses this context
// and then closes registered resources. Calling Close more than once is safe,
// and after first call it always returns nil.
func (ctx *MPCalContext) Close() error {
	ctx.lock.Lock()
	defer ctx.lock.Unlock()
	if ctx.closed {
		return nil
	}
	ctx.closed = true

	select {
	case <-ctx.events:
		// Archetype execution has started

		select {
		case <-ctx.events:
			// Archetype execution has finished

		case ctx.done <- struct{}{}:
			// In order to not interrupting an archetype when it's in the middle of a
			// critical section, we block here to send the context closed signal to the
			// archetype. Archetype quits after receiving this signal, and then we can
			// close the done channel and the registered resources.
		}

	default:
		// Archetype has not even started
	}
	close(ctx.done)

	var err error
	// Note that we should close all the resources, not just the dirty ones.
	for _, res := range ctx.resources {
	    cerr := res.Close()
    	err = multierr.Append(err, cerr)
	}
	return err
}
