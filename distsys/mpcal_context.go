package distsys

import (
	"errors"
	"fmt"
	"github.com/benbjohnson/immutable"
)

var ErrAssertionFailed = errors.New("assertion failed")

var ErrCriticalSectionAborted = errors.New("MPCal critical section aborted")

// ArchetypeResourceHandle encapsulates a reference to an ArchetypeResource.
// These handles insulate the end-user from worrying about the specifics of resource lifetimes, logging, and
// crash recovery scenarios.
type ArchetypeResourceHandle struct {
	path TLAValue
}

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
	resources *immutable.Map

	// stack-related fields
	pathBase   TLAValue
	frameIdx   int
	frameStack [][]ArchetypeResourceHandle

	dirtyResourceHandles []ArchetypeResourceHandle
}

func NewMPCalContext() *MPCalContext {
	return &MPCalContext{
		resources: immutable.NewMap(TLAValueHasher{}),

		pathBase:   NewTLATuple(),
		frameIdx:   0,
		frameStack: [][]ArchetypeResourceHandle{{}},
	}
}

func (ctx *MPCalContext) EnsureArchetypeResourceByName(name string, maker ArchetypeResourceMaker) ArchetypeResourceHandle {
	handle := ArchetypeResourceHandle{
		path: NewTLAString(name),
	}
	// this (currently unreachable) case accounts for a recovery situation, where the desired resource already exists
	if res, ok := ctx.resources.Get(handle.path); ok {
		maker.Configure(res.(ArchetypeResource))
		return handle
	}
	res := maker.Make()
	maker.Configure(res)
	ctx.resources = ctx.resources.Set(handle.path, res)
	return handle
}

func (ctx *MPCalContext) EnsureArchetypeResourceByPosition(maker ArchetypeResourceMaker) ArchetypeResourceHandle {
	frame := ctx.frameStack[len(ctx.frameStack)-1]
	handle := ArchetypeResourceHandle{
		path: TLA_Append(ctx.pathBase, NewTLATuple(NewTLANumber(int32(ctx.frameIdx)))),
	}

	// this (currently unreachable) case accounts for a recovery situation, where the desired resource is already in place
	if ctx.frameIdx < len(frame) {
		maker.Configure(ctx.getResourceByHandle(frame[ctx.frameIdx]))
		ctx.frameIdx += 1
		return handle
	}

	// without recovery, we push + setup a fresh resource
	ctx.frameIdx += 1
	ctx.frameStack[len(ctx.frameStack)-1] = append(frame, handle)
	res := maker.Make()
	maker.Configure(res)
	ctx.resources = ctx.resources.Set(handle.path, res)
	return handle
}

func (ctx *MPCalContext) getResourceByHandle(handle ArchetypeResourceHandle) ArchetypeResource {
	res, ok := ctx.resources.Get(handle.path)
	if !ok {
		panic(fmt.Errorf("could not find resource with path %s", handle.path.String()))
	}
	return res.(ArchetypeResource)
}

func (ctx *MPCalContext) Abort() {
	var nonTrivialAborts []chan struct{}
	for _, resHandle := range ctx.dirtyResourceHandles {
		ch := ctx.getResourceByHandle(resHandle).Abort()
		if ch != nil {
			nonTrivialAborts = append(nonTrivialAborts, ch)
		}
	}
	for _, ch := range nonTrivialAborts {
		<-ch
	}

	ctx.dirtyResourceHandles = nil
}

func (ctx *MPCalContext) Commit() (err error) {
	// dispatch all parts of the pre-commit phase asynchronously, so we only wait as long as the slowest resource
	var nonTrivialPreCommits []chan error
	for _, resHandle := range ctx.dirtyResourceHandles {
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
	for _, resHandle := range ctx.dirtyResourceHandles {
		ch := ctx.getResourceByHandle(resHandle).Commit()
		if ch != nil {
			nonTrivialCommits = append(nonTrivialCommits, ch)
		}
	}
	for _, ch := range nonTrivialCommits {
		<-ch
	}

	ctx.dirtyResourceHandles = nil
	return
}

func (ctx *MPCalContext) ensureCriticalSectionWith(handle ArchetypeResourceHandle) {
	for _, candidateHandle := range ctx.dirtyResourceHandles {
		if candidateHandle.path.Equal(handle.path) {
			return
		}
	}
	ctx.dirtyResourceHandles = append(ctx.dirtyResourceHandles, handle)
}

func (ctx *MPCalContext) Write(handle ArchetypeResourceHandle, indices []TLAValue, value TLAValue) (err error) {
	ctx.ensureCriticalSectionWith(handle)
	res := ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	err = res.WriteValue(value)
	return
}

func (ctx *MPCalContext) Read(handle ArchetypeResourceHandle, indices []TLAValue) (value TLAValue, err error) {
	ctx.ensureCriticalSectionWith(handle)
	res := ctx.getResourceByHandle(handle)
	for _, index := range indices {
		res, err = res.Index(index)
		if err != nil {
			return
		}
	}
	value, err = res.ReadValue()
	return
}
