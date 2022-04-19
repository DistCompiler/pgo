package distsys

import (
	"errors"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// ArchetypeResource represents an interface between an MPCal model and some external environment.
// Such a resource should be instantiated under the control of MPCalContext.EnsureArchetypeResource.
// Many implementations are available under ./resources.
// This API describes what is expected of those implementations, and any others.
type ArchetypeResource interface {
	// Close will be called when the archetype stops running (as a result, it's
	// not in the middle of a critical section). Close stops running of any
	// background jobs and cleans up the stuff that no longer needed when the
	// archetype is not running. Close will be called at most once by the MPCal
	// Context.
	Close() error
	FreshState() ArchetypeResourceState
}

type ArchetypeResourceState interface {
	// Abort will be called when the resource should be reset to a state similar to the last Commit.
	// May return nil. If it doesn't return nil, the channel should notify one time, when the operation is complete.
	// If it returns nil, the operation is considered complete immediately.
	Abort() []chan struct{}
	// PreCommit will be called after any number of ReadValue, WriteValue, or Index operations.
	// It signals if it is reasonable to go ahead with a Commit.
	// If the resource might need to back out, it should do it here.
	// May return nil. If it doesn't return nil, the channel should yield one error value. If the error is nil,
	// Commit may go ahead. Otherwise, it may not.
	// Returning nil is considered a short-cut to immediately yielding a nil error.
	PreCommit() []chan error
	// Commit will be called if no sibling PreCommit calls raised any errors.
	// It must unconditionally commit current resource state. By necessity, this is the only resource operation that
	// may block indefinitely.
	// May return nil. If it doesn't return nil, the channel should notify once the commit is complete.
	// Returning nil is considered as an immediately successful commit.
	Commit() []chan struct{}
	// ReadValue must return the resource's current value.
	// If the resource is not ready, ErrCriticalSectionAborted may be returned alongside a default TLAValue.
	// This operation should not block indefinitely.
	// This makes no sense for a map-like resource, and should be blocked off with ArchetypeResourceMapMixin in that case.
	ReadValue(iface *ArchetypeInterface) (tla.TLAValue, error)
	// WriteValue must update the resource's current value.
	// It follows the same conventions as ReadValue.
	WriteValue(iface *ArchetypeInterface, value tla.TLAValue) error
	// Index must return the resource's sub-resource at the given index.
	// It's unclear when this would be needed, but, if the resource is not ready, then this operation may return
	// ErrCriticalSectionAborted.
	// This makes no sense for a value-like resource, and should be blocked off with ArchetypeResourceLeafMixin in that case.
	Index(index tla.TLAValue) (ArchetypeResourceComponent, error)
	ForkState() ArchetypeResourceState
}

type ArchetypeResourceComponent interface {
	Index(index tla.TLAValue) (ArchetypeResourceComponent, error)
	ReadValue(iface *ArchetypeInterface) (tla.TLAValue, error)
	WriteValue(iface *ArchetypeInterface, value tla.TLAValue) error
}

type ArchetypeResourceLeafMixin struct{}

var ErrArchetypeResourceLeafIndexed = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(tla.TLAValue) (ArchetypeResourceComponent, error) {
	return nil, ErrArchetypeResourceLeafIndexed
}

type ArchetypeResourceMapMixin struct{}

var ErrArchetypeResourceMapReadWrite = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue(*ArchetypeInterface) (tla.TLAValue, error) {
	return tla.TLAValue{}, ErrArchetypeResourceMapReadWrite
}

func (ArchetypeResourceMapMixin) WriteValue(*ArchetypeInterface, tla.TLAValue) error {
	return ErrArchetypeResourceMapReadWrite
}

// A bare-bones resource: just holds and buffers a TLAValue
// --------------------------------------------------------

type LocalArchetypeResource struct {
	value tla.TLAValue
}

var _ ArchetypeResource = &LocalArchetypeResource{}

func LocalArchetypeResourceMaker(value tla.TLAValue) ArchetypeResourceMaker {
	return ArchetypeResourceMakerFn(func() ArchetypeResource {
		return &LocalArchetypeResource{
			value: value,
		}
	})
}

func (res *LocalArchetypeResource) Close() error {
	return nil
}

func (res *LocalArchetypeResource) FreshState() ArchetypeResourceState {
	return &localArchetypeResourceState{
		parent: res,
		value:  res.value,
	}
}

type localArchetypeResourceState struct {
	parent *LocalArchetypeResource
	value  tla.TLAValue
}

func (state *localArchetypeResourceState) Abort() []chan struct{} {
	return nil
}

func (state *localArchetypeResourceState) PreCommit() []chan error {
	return nil
}

func (state *localArchetypeResourceState) Commit() []chan struct{} {
	state.parent.value = state.value
	return nil
}

func (state *localArchetypeResourceState) ReadValue(_ *ArchetypeInterface) (tla.TLAValue, error) {
	return state.value, nil
}

func (state *localArchetypeResourceState) WriteValue(_ *ArchetypeInterface, value tla.TLAValue) error {
	state.value = value
	return nil
}

func (state *localArchetypeResourceState) Index(index tla.TLAValue) (ArchetypeResourceComponent, error) {
	return &localArchetypeResourceComponent{
		state:   state,
		indices: []tla.TLAValue{index},
	}, nil
}

func (state *localArchetypeResourceState) ForkState() ArchetypeResourceState {
	return &localArchetypeResourceState{
		parent: state.parent,
		value:  state.value,
	}
}

type localArchetypeResourceComponent struct {
	state   *localArchetypeResourceState
	stolen  bool
	indices []tla.TLAValue
}

func (comp *localArchetypeResourceComponent) Index(index tla.TLAValue) (ArchetypeResourceComponent, error) {
	if !comp.stolen {
		comp.stolen = true
		return &localArchetypeResourceComponent{
			state:   comp.state,
			indices: append(comp.indices, index),
		}, nil
	}
	return &localArchetypeResourceComponent{
		state:   comp.state,
		indices: append(append([]tla.TLAValue(nil), comp.indices...), index),
	}, nil
}

func (comp *localArchetypeResourceComponent) ReadValue(iface *ArchetypeInterface) (tla.TLAValue, error) {
	fn, err := comp.state.ReadValue(iface)
	if err != nil {
		return tla.TLAValue{}, err
	}
	for _, index := range comp.indices {
		fn = fn.ApplyFunction(index)
	}
	return fn, nil
}

func (comp *localArchetypeResourceComponent) WriteValue(iface *ArchetypeInterface, value tla.TLAValue) error {
	fn, err := comp.state.ReadValue(iface)
	if err != nil {
		return err
	}
	fn = tla.TLAFunctionSubstitution(fn, []tla.TLAFunctionSubstitutionRecord{{
		Keys: comp.indices,
		Value: func(_ tla.TLAValue) tla.TLAValue {
			return value
		},
	}})
	return comp.state.WriteValue(iface, fn)
}
