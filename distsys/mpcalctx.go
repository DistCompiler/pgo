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

var ErrDone = errors.New("A pseudo-error to indicate an archetype has terminated execution normally")

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
// - currently stub-level stack frame management
// - critical section semantics
// - resource lifecycle management, which may eventually include logging and crash recovery
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

// ArchetypeEvent shows an event in an archetype execution process
type ArchetypeEvent int

const (
	// ArchetypeStarted denotes that the archetype execution has started
	ArchetypeStarted ArchetypeEvent = iota
	// ArchetypeFinished denotes that the archetype execution has finished
	ArchetypeFinished
)

// ReportEvent will be called by an archetype to report an event about its
// execution.
func (ctx *MPCalContext) ReportEvent(event ArchetypeEvent) {
	switch event {
	case ArchetypeStarted:
		select {
		case ctx.events <- struct{}{}:
		default:
			panic("archetype has started before")
		}
	case ArchetypeFinished:
		close(ctx.events)
	}
}

func EnsureArchetypeRefParam(name string, maker ArchetypeResourceMaker) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireArchetype()
		resourceName := "&" + ctx.archetype.Name + "." + name
		refName := ctx.archetype.Name + "." + name
		_ = ctx.ensureArchetypeResource(resourceName, maker)
		_ = ctx.ensureArchetypeResource(refName, LocalArchetypeResourceMaker(NewTLAString(resourceName)))
	}
}

func EnsureArchetypeValueParam(name string, value TLAValue) MPCalContextConfigFn {
	return func(ctx *MPCalContext) {
		ctx.requireArchetype()
		_ = ctx.ensureArchetypeResource(ctx.archetype.Name + "." + name, LocalArchetypeResourceMaker(value))
	}
}

func DefineConstantValue(name string, value TLAValue) MPCalContextConfigFn {
	return DefineConstantOperator(name, func() TLAValue {
		return value
	})
}

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
			if !tlaValueTyp.AssignableTo(defnTyp.In(i)) {
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

// IFace provides an ArchetypeInterface, giving access to methods considered MPCal-internal.
// This is useful when directly calling pure TLA+ operators using a context constructed via NewMPCalContextWithoutArchetype,
// and is one of very few operations that will work on such a context.
// This operation is not expected to be useful when running with an MPCalArchetype.
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

func (ctx *MPCalContext) Run() error {
	// pre-sanity checks: an archetype should be provided if we're going to try and run one
	ctx.requireArchetype()
	// sanity checks and other setup, done here so you can init a context, not call Run, and not get checks
	ctx.preRun()

	pc := ctx.iface.RequireArchetypeResource(".pc")
	var err error
	for {
		// all error control flow lives here, reached by "continue" from below
		switch err {
		case nil: // everything is fine; carry on
		case ErrCriticalSectionAborted:
			ctx.abort()
			err = nil
		case ErrDone: // signals that we're done; quit successfully
			// TODO: "close" semantics here?
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
	it := ctx.resources.Iterator()
	for !it.Done() {
		_, r := it.Next()
		cerr := r.(ArchetypeResource).Close()
		err = multierr.Append(err, cerr)
	}
	return err
}
