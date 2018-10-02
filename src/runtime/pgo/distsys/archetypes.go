package distsys

import (
	"fmt"
)

// ResourceAccess indicates what type of access the a caller is requesting.
type ResourceAccess int

const (
	READ_ACCESS = iota + 1
	WRITE_ACCESS
)

// ArchetypeResource defines the interface that parameters passed to functions
// derived from Modular PlusCal's archetypes must implement.
type ArchetypeResource interface {
	// Acquire attempts to get access to a resource, returning its associated
	// value when successful.
	Acquire(access ResourceAccess) (interface{}, error)

	// Commit receives a new value that the underlying resource is supposed
	// to be set to.
	Commit(value interface{}) error

	// Abort indicates an error situation. Access must be released, and any
	// state rolled back to its previous value (before acquisition)
	Abort() error
}

// Global variable is one type of archetype resource. It is backed by the
// StateServer implementation in this package.
type GlobalVariable struct {
	name        string
	stateServer *StateServer
	refs        VarReferences
}

// Variable is a convenience function to create a GlobalVariable struct from
// a previously configured StateServer. The returned GlobalVariable can be
// passed to archetypes, and the state represented by this variable will be
// managed by all peers in the system.
func (ss *StateServer) Variable(name string) *GlobalVariable {
	return &GlobalVariable{
		name:        name,
		stateServer: ss,
		refs:        nil,
	}
}

// Acquire wraps the underlying StateServer struct, creating a proper BorrowSpec
// and attempting to borrow the value from this node's peers in the network.
func (v *GlobalVariable) Acquire(access ResourceAccess) (interface{}, error) {
	if v.refs != nil {
		return nil, fmt.Errorf("variable %s already acquired", v.name)
	}

	var spec BorrowSpec

	if access&READ_ACCESS != 0 {
		spec.ReadNames = []string{v.name}
	}

	if access&WRITE_ACCESS != 0 {
		spec.WriteNames = []string{v.name}
	}

	refs, err := v.stateServer.Acquire(&spec)
	if err != nil {
		return nil, err
	}

	v.refs = refs
	return refs.Get(v.name), nil
}

// Commit updates previously obtained references (via `Acquire`) to
// the value passed to this function. After committing, the caller no
// longer holds access to the variable.
func (v *GlobalVariable) Commit(value interface{}) error {
	v.refs.Set(v.name, value)
	err := v.stateServer.Release(v.refs)
	v.refs = nil

	return err
}

// Abort releases access (previously obtained via `Acquire`) without modifying
// the underlying value of a variable.
func (v *GlobalVariable) Abort() error {
	err := v.stateServer.Release(v.refs)
	v.refs = nil

	return err
}
