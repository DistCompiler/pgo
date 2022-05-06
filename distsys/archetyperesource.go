package distsys

import (
	"bytes"
	"encoding/gob"
	"errors"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys/tla"
)

// ArchetypeResource represents an interface between an MPCal model and some external environment.
// Such a resource should be instantiated under the control of MPCalContext.EnsureArchetypeResource.
// Many implementations are available under ./resources.
// This API describes what is expected of those implementations, and any others.
type ArchetypeResource interface {
	// Abort will be called when the resource should be reset to a state similar to the last Commit.
	// May return nil. If it doesn't return nil, the channel should notify one time, when the operation is complete.
	// If it returns nil, the operation is considered complete immediately.
	Abort() chan struct{}
	// PreCommit will be called after any number of ReadValue, WriteValue, or Index operations.
	// It signals if it is reasonable to go ahead with a Commit.
	// If the resource might need to back out, it should do it here.
	// May return nil. If it doesn't return nil, the channel should yield one error value. If the error is nil,
	// Commit may go ahead. Otherwise, it may not.
	// Returning nil is considered a short-cut to immediately yielding a nil error.
	PreCommit() chan error
	// Commit will be called if no sibling PreCommit calls raised any errors.
	// It must unconditionally commit current resource state. By necessity, this is the only resource operation that
	// may block indefinitely.
	// May return nil. If it doesn't return nil, the channel should notify once the commit is complete.
	// Returning nil is considered as an immediately successful commit.
	Commit() chan struct{}
	// ReadValue must return the resource's current value.
	// If the resource is not ready, ErrCriticalSectionAborted may be returned alongside a default TLAValue.
	// This operation should not block indefinitely.
	// This makes no sense for a map-like resource, and should be blocked off with ArchetypeResourceMapMixin in that case.
	ReadValue() (tla.TLAValue, error)
	// WriteValue must update the resource's current value.
	// It follows the same conventions as ReadValue.
	WriteValue(value tla.TLAValue) error
	// Index must return the resource's sub-resource at the given index.
	// It's unclear when this would be needed, but, if the resource is not ready, then this operation may return
	// ErrCriticalSectionAborted.
	// This makes no sense for a value-like resource, and should be blocked off with ArchetypeResourceLeafMixin in that case.
	Index(index tla.TLAValue) (ArchetypeResource, error)
	// Close will be called when the archetype stops running (as a result, it's
	// not in the middle of a critical section). Close stops running of any
	// background jobs and cleans up the stuff that no longer needed when the
	// archetype is not running. Close will be called at most once by an MPCal
	// Context.
	Close() error
	// VClockHint allows the resource to transform the archetype's current vector clock, which can be used by the
	// archetype resource to indicate causality information.
	// This method will be called twice per critical section, between PreCommit and Commit, in order to allow the resource
	// implementation to both add its information to the current vector clock, and to learn the critical section's final
	// clock information.
	// This optional method has default implementations for both the leaf and map mixins which do nothing.
	VClockHint(archClock trace.VClock) trace.VClock
}

type ArchetypeResourceLeafMixin struct{}

var ErrArchetypeResourceLeafIndexed = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(tla.TLAValue) (ArchetypeResource, error) {
	return nil, ErrArchetypeResourceLeafIndexed
}

func (ArchetypeResourceLeafMixin) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}

type ArchetypeResourceMapMixin struct{}

var ErrArchetypeResourceMapReadWrite = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue() (tla.TLAValue, error) {
	return tla.TLAValue{}, ErrArchetypeResourceMapReadWrite
}

func (ArchetypeResourceMapMixin) WriteValue(tla.TLAValue) error {
	return ErrArchetypeResourceMapReadWrite
}

func (ArchetypeResourceMapMixin) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}

// LocalArchetypeResource is a bare-bones resource that just holds and buffers a
// TLAValue.
type LocalArchetypeResource struct {
	hasOldValue bool // if true, this resource has already been written in this critical section
	// if this resource is already written in this critical section, oldValue contains prev value
	// value always contains the "current" value
	value, oldValue tla.TLAValue
}

var _ ArchetypeResource = &LocalArchetypeResource{}

func NewLocalArchetypeResource(value tla.TLAValue) *LocalArchetypeResource {
	return &LocalArchetypeResource{
		value: value,
	}
}

func (res *LocalArchetypeResource) Abort() chan struct{} {
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
		res.oldValue = tla.TLAValue{}
	}
	return nil
}

func (res *LocalArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *LocalArchetypeResource) Commit() chan struct{} {
	res.hasOldValue = false
	res.oldValue = tla.TLAValue{}
	return nil
}

func (res *LocalArchetypeResource) ReadValue() (tla.TLAValue, error) {
	return res.value, nil
}

func (res *LocalArchetypeResource) WriteValue(value tla.TLAValue) error {
	if !res.hasOldValue {
		res.oldValue = res.value
		res.hasOldValue = true
	}
	res.value = value
	return nil
}

// Index is a special case: a local resource uniquely _can_ be indexed and read/written interchangeably!
// See comment on localArchetypeSubResource
func (res *LocalArchetypeResource) Index(index tla.TLAValue) (ArchetypeResource, error) {
	subRes := localArchetypeSubResource{
		indices: nil,
		parent:  res,
	}
	return subRes.Index(index)
}

func (res *LocalArchetypeResource) Close() error {
	return nil
}

func (res *LocalArchetypeResource) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
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
	indices []tla.TLAValue
	// parent denotes the parent local resource. it does everything important,
	// which is why most methods here just return nil; they shouldn't even be
	// called
	parent *LocalArchetypeResource
}

var _ ArchetypeResource = &localArchetypeSubResource{}

func (res localArchetypeSubResource) Abort() chan struct{} {
	return nil
}

func (res localArchetypeSubResource) PreCommit() chan error {
	return nil
}

func (res localArchetypeSubResource) Commit() chan struct{} {
	return nil
}

func (res localArchetypeSubResource) ReadValue() (tla.TLAValue, error) {
	fn, err := res.parent.ReadValue()
	if err != nil {
		return tla.TLAValue{}, err
	}
	for _, index := range res.indices {
		fn = fn.ApplyFunction(index)
	}
	return fn, nil
}

func (res localArchetypeSubResource) WriteValue(value tla.TLAValue) error {
	fn, err := res.parent.ReadValue()
	if err != nil {
		return err
	}
	fn = tla.TLAFunctionSubstitution(fn, []tla.TLAFunctionSubstitutionRecord{{
		Keys: res.indices,
		Value: func(_ tla.TLAValue) tla.TLAValue {
			return value
		},
	}})
	return res.parent.WriteValue(fn)
}

func (res localArchetypeSubResource) Index(index tla.TLAValue) (ArchetypeResource, error) {
	newIndices := make([]tla.TLAValue, len(res.indices)+1)
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

func (res localArchetypeSubResource) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}
