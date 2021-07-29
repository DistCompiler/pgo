package distsys

import (
	"errors"
)

// ArchetypeResource represents an interface between an MPCal model and some external environment.
// Such a resource should be instantiated under the control of MPCalContext.EnsureArchetypeResourceByName or
// MPCalContext.EnsureArchetypeResourceByPosition. Typically, the former would be clearer.
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
	ReadValue() (TLAValue, error)
	// WriteValue must update the resource's current value.
	// It follows the same conventions as ReadValue.
	WriteValue(value TLAValue) error
	// Index must return the resource's sub-resource at the given index.
	// It's unclear when this would be needed, but, if the resource is not ready, then this operation may return
	// ErrCriticalSectionAborted.
	// This makes no sense for a value-like resource, and should be blocked off with ArchetypeResourceLeafMixin in that case.
	Index(index TLAValue) (ArchetypeResource, error)
}

type ArchetypeResourceLeafMixin struct{}

var ErrArchetypeResourceLeafIndexed = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(TLAValue) (ArchetypeResource, error) {
	return nil, ErrArchetypeResourceLeafIndexed
}

type ArchetypeResourceMapMixin struct{}

var ErrArchetypeResourceMapReadWrite = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue() (TLAValue, error) {
	return TLAValue{}, ErrArchetypeResourceMapReadWrite
}

func (ArchetypeResourceMapMixin) WriteValue(TLAValue) error {
	return ErrArchetypeResourceMapReadWrite
}

// A bare-bones resource: just holds and buffers a TLAValue
// --------------------------------------------------------

type LocalArchetypeResource struct {
	ArchetypeResourceLeafMixin
	hasOldValue bool // if true, this resource has already been written in this critical section
	// if this resource is already written in this critical section, oldValue contains prev value
	// value always contains the "current" value
	value, oldValue TLAValue
}

var _ ArchetypeResource = &LocalArchetypeResource{}

func LocalArchetypeResourceMaker(value TLAValue) ArchetypeResourceMaker {
	return ArchetypeResourceMakerFn(func() ArchetypeResource {
		return &LocalArchetypeResource{
			value: value,
		}
	})
}

func (res *LocalArchetypeResource) Abort() chan struct{} {
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
		res.oldValue = TLAValue{}
	}
	return nil
}

func (res *LocalArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *LocalArchetypeResource) Commit() chan struct{} {
	res.hasOldValue = false
	res.oldValue = TLAValue{}
	return nil
}

func (res *LocalArchetypeResource) ReadValue() (TLAValue, error) {
	return res.value, nil
}

func (res *LocalArchetypeResource) WriteValue(value TLAValue) error {
	if !res.hasOldValue {
		res.oldValue = res.value
		res.hasOldValue = true
	}
	res.value = value
	return nil
}
