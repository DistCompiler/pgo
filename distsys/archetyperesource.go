package distsys

import (
	"bytes"
	"encoding/gob"
	"errors"

	"github.com/DistCompiler/pgo/distsys/tla"
)

// ArchetypeResource represents an interface between an MPCal model and some external environment.
// Such a resource should be instantiated under the control of MPCalContext.EnsureArchetypeResource.
// Many implementations are available under ./resources.
// This API describes what is expected of those implementations, and any others.
type ArchetypeResource interface {
	// Abort will be called when the resource should be reset to a state similar to the last Commit.
	// May return nil. If it doesn't return nil, the channel should notify one time, when the operation is complete.
	// If it returns nil, the operation is considered complete immediately.
	Abort(iface ArchetypeInterface) chan struct{}
	// PreCommit will be called after any number of ReadValue, WriteValue, or Index operations.
	// It signals if it is reasonable to go ahead with a Commit.
	// If the resource might need to back out, it should do it here.
	// May return nil. If it doesn't return nil, the channel should yield one error value. If the error is nil,
	// Commit may go ahead. Otherwise, it may not.
	// Returning nil is considered a short-cut to immediately yielding a nil error.
	PreCommit(iface ArchetypeInterface) chan error
	// Commit will be called if no sibling PreCommit calls raised any errors.
	// It must unconditionally commit current resource state. By necessity, this is the only resource operation that
	// may block indefinitely.
	// May return nil. If it doesn't return nil, the channel should notify once the commit is complete.
	// Returning nil is considered as an immediately successful commit.
	Commit(iface ArchetypeInterface) chan struct{}
	// ReadValue must return the resource's current value.
	// If the resource is not ready, ErrCriticalSectionAborted may be returned alongside a default Value.
	// This operation should not block indefinitely.
	// This makes no sense for a map-like resource, and should be blocked off with ArchetypeResourceMapMixin in that case.
	ReadValue(iface ArchetypeInterface) (tla.Value, error)
	// WriteValue must update the resource's current value.
	// It follows the same conventions as ReadValue.
	WriteValue(iface ArchetypeInterface, value tla.Value) error
	// Index must return the resource's sub-resource at the given index.
	// It's unclear when this would be needed, but, if the resource is not ready, then this operation may return
	// ErrCriticalSectionAborted.
	// This makes no sense for a value-like resource, and should be blocked off with ArchetypeResourceLeafMixin in that case.
	Index(iface ArchetypeInterface, index tla.Value) (ArchetypeResource, error)
	// Close will be called when the archetype stops running (as a result, it's
	// not in the middle of a critical section). Close stops running of any
	// background jobs and cleans up the stuff that no longer needed when the
	// archetype is not running. Close will be called at most once by an MPCal
	// Context.
	Close() error
}

type ArchetypeResourceLeafMixin struct{}

var ErrArchetypeResourceLeafIndexed = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(ArchetypeInterface, tla.Value) (ArchetypeResource, error) {
	return nil, ErrArchetypeResourceLeafIndexed
}

type ArchetypeResourceMapMixin struct{}

var ErrArchetypeResourceMapReadWrite = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue(ArchetypeInterface) (tla.Value, error) {
	return tla.Value{}, ErrArchetypeResourceMapReadWrite
}

func (ArchetypeResourceMapMixin) WriteValue(ArchetypeInterface, tla.Value) error {
	return ErrArchetypeResourceMapReadWrite
}

// LocalArchetypeResource is a bare-bones resource that just holds and buffers a
// Value.
type LocalArchetypeResource struct {
	// If this resource is already written in this critical section, oldValue contains the original value.
	// If there are no pending writes, oldValue == value
	// value always contains the "current" value
	value, oldValue tla.Value
	clock           tla.VClock
}

var _ ArchetypeResource = &LocalArchetypeResource{}

func NewLocalArchetypeResource(value tla.Value) *LocalArchetypeResource {
	return &LocalArchetypeResource{
		value:    value,
		oldValue: value,
	}
}

func (res *LocalArchetypeResource) Abort(ArchetypeInterface) chan struct{} {
	res.value = res.oldValue
	return nil
}

func (res *LocalArchetypeResource) PreCommit(ArchetypeInterface) chan error {
	return nil
}

func (res *LocalArchetypeResource) Commit(ArchetypeInterface) chan struct{} {
	res.oldValue = res.value
	return nil
}

func (res *LocalArchetypeResource) ReadValue(iface ArchetypeInterface) (tla.Value, error) {
	res.clock = res.clock.Merge(iface.GetVClockSink().GetVClock())
	return tla.WrapCausal(res.value, res.clock), nil
}

func (res *LocalArchetypeResource) WriteValue(iface ArchetypeInterface, value tla.Value) error {
	// record immediately previous value, so we support chains of assignments
	iface.oldValueHint(res.value)
	// update vclock, pull additional clock info from value
	iface.GetVClockSink().WitnessVClock(res.clock)
	if valueClock := value.GetVClock(); valueClock != nil {
		res.clock = res.clock.Merge(*valueClock)
	}
	res.value = value.StripVClock()
	return nil
}

// Index is a special case: a local resource uniquely _can_ be indexed and read/written interchangeably!
// See comment on localArchetypeSubResource
func (res *LocalArchetypeResource) Index(iface ArchetypeInterface, index tla.Value) (ArchetypeResource, error) {
	subRes := localArchetypeSubResource{
		indices: nil,
		parent:  res,
	}
	return subRes.Index(iface, index)
}

func (res *LocalArchetypeResource) Close() error {
	return nil
}

func (res *LocalArchetypeResource) GetState() ([]byte, error) {
	var writer bytes.Buffer
	encoder := gob.NewEncoder(&writer)
	err := encoder.Encode(&res.value)
	return writer.Bytes(), err
}

// localArchetypeSubResource is used to implement the no-op case for
// function-mapping.
// It's what happens when you call LocalArchetypeResource.Index, which is what
// happens when you write code like this:
// i[idx] := i[idx] + 1; \* where i is a local variable
type localArchetypeSubResource struct {
	// indices gives the total path from root value, as accumulated from calls to
	// Index, e.g with `i[a][b] := ...` you get []{a, b}
	indices []tla.Value
	// parent denotes the parent local resource. it does everything important,
	// which is why most methods here just return nil; they shouldn't even be
	// called
	parent *LocalArchetypeResource
}

var _ ArchetypeResource = &localArchetypeSubResource{}

func (res localArchetypeSubResource) Abort(ArchetypeInterface) chan struct{} {
	return nil
}

func (res localArchetypeSubResource) PreCommit(ArchetypeInterface) chan error {
	return nil
}

func (res localArchetypeSubResource) Commit(ArchetypeInterface) chan struct{} {
	return nil
}

func (res localArchetypeSubResource) ReadValue(iface ArchetypeInterface) (tla.Value, error) {
	fn := res.parent.value
	for _, index := range res.indices {
		fn = fn.ApplyFunction(index)
	}

	// update our vclock from current iface
	res.parent.clock = res.parent.clock.Merge(iface.GetVClockSink().GetVClock())

	// yield new causally wrapped value
	fn = tla.WrapCausal(fn, res.parent.clock)
	return fn, nil
}

func (res localArchetypeSubResource) WriteValue(iface ArchetypeInterface, value tla.Value) error {
	// witness this resource's vclock
	iface.GetVClockSink().WitnessVClock(res.parent.clock)
	// update, pull vclock from written value
	if valueClock := value.GetVClock(); valueClock != nil {
		res.parent.clock = res.parent.clock.Merge(*valueClock)
		value = value.StripVClock()
	}

	// update the value using the indices
	fn := res.parent.value
	fn = tla.FunctionSubstitution(fn, []tla.FunctionSubstitutionRecord{{
		Keys: res.indices,
		Value: func(oldValue tla.Value) tla.Value {
			iface.oldValueHint(oldValue)
			return value
		},
	}})
	res.parent.value = fn
	return nil
}

func (res localArchetypeSubResource) Index(iface ArchetypeInterface, index tla.Value) (ArchetypeResource, error) {
	newIndices := make([]tla.Value, len(res.indices)+1)
	lastIdx := copy(newIndices, res.indices)
	newIndices[lastIdx] = index
	return localArchetypeSubResource{
		indices: newIndices,
		parent:  res.parent,
	}, nil
}

func (res localArchetypeSubResource) Close() error {
	return nil
}
