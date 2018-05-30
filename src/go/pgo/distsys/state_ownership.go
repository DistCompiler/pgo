package distsys

import (
	"log"
	"sync"
)

const (
	REF_VAL = iota
	REF_MOVED
	REF_SKIP
)

type MigrationStrategy interface {
	ShouldMigrate(name, requester string) bool
}

type NeverMigrate string

func (never NeverMigrate) ShouldMigrate(_, _ string) bool {
	return false
}

type StateOwner struct {
	sync.RWMutex
	address string
}

// OwnershipTable maps variable names to host addresses that own them at
// different moments in time
type OwnershipTable struct {
	self  string                 // the address of the running node
	table map[string]*StateOwner // maps names to owners
}

func NewOwnershipTable(assignments map[string]string, self string) *OwnershipTable {
	ownership := map[string]*StateOwner{}

	for name, owner := range assignments {
		ownership[name] = &StateOwner{address: owner}
	}

	return &OwnershipTable{
		self:  self,
		table: ownership,
	}

}

// Lookup returns the address of the peer in the system that currently owns
// the variable with the given name. Panics if the information is unknown.
func (ownership OwnershipTable) Lookup(name string) string {
	peer, found := ownership.table[name]
	if !found {
		log.Panicf("%v", UnknownOwnerError{name})
	}

	return peer.address
}

func (ownership *OwnershipTable) IsMine(name string) bool {
	return ownership.Lookup(name) == ownership.self
}

// Update changes the ownership of variable `name` to the `address` given.
// Assumes that the caller has an appropriate write lock to the entry.
func (ownership *OwnershipTable) Update(name, address string) {
	peer, found := ownership.table[name]
	if !found {
		log.Panicf("%v", UnknownOwnerError{name})
	}

	peer.address = address
}

type RefHandler interface {
	GetRef() *Reference
}

func refBuilder(handler *localStateHandler, variable *BorrowSpecVariable) RefHandler {
	owner := handler.ownership.Lookup(variable.Name)

	if handler.ownership.IsMine(variable.Name) {
		if handler.ownershipMiss {
			return RefSkipHandler{}
		}

		return RefValHandler{
			name:              variable.Name,
			requester:         handler.requester,
			exclusive:         variable.Exclusive,
			store:             handler.store,
			ownership:         handler.ownership,
			migrationStrategy: handler.migrationStrategy,
		}
	}

	handler.ownershipMiss = true
	return RefMovedHandler{owner}
}

type RefValHandler struct {
	name              string
	requester         string
	exclusive         bool
	store             *SimpleDataStore
	ownership         *OwnershipTable
	migrationStrategy MigrationStrategy
}

func (refhandler RefValHandler) GetRef() *Reference {
	var hold func(string) (interface{}, error)

	if refhandler.exclusive {
		hold = refhandler.store.HoldExclusive
	} else {
		hold = refhandler.store.Hold
	}

	val, err := hold(refhandler.name)
	if err != nil {
		log.Panic(err)
	}

	moveOwnership := refhandler.migrationStrategy.ShouldMigrate(refhandler.name, refhandler.requester)

	if moveOwnership {
		// if we are moving this name, make sure we have exclusive access
		// to it first
		refhandler.store.HoldExclusive(refhandler.name)
		defer refhandler.store.ReleaseExclusive(refhandler.name)

		refhandler.store.Delete(refhandler.name)

		// update our ownership table to reflect the migration
		refhandler.ownership.Update(refhandler.name, refhandler.requester)
	}

	return &Reference{
		Type: REF_VAL,

		Value:     val,
		Exclusive: refhandler.exclusive,
		Ownership: moveOwnership,
	}
}

type RefMovedHandler struct {
	peer string
}

func (refhandler RefMovedHandler) GetRef() *Reference {
	return &Reference{
		Type: REF_MOVED,
		Peer: refhandler.peer,
	}
}

type RefSkipHandler struct{}

func (refhandler RefSkipHandler) GetRef() *Reference {
	return &Reference{
		Type: REF_SKIP,
	}
}

// localStateHandler is responsible for manipulating requests for global state that is
// to be present in this node's local store.
type localStateHandler struct {
	group             *VarReq           // the variables to be manipulated, including their permissions
	requester         string            // address of the node who sent the request for this group of variables
	store             *SimpleDataStore  // the underlying data store
	ownership         *OwnershipTable   // the current state of the ownership table
	migrationStrategy MigrationStrategy // when to migrate state
	ownershipMiss     bool              // whether some variable in `group` is not owned by this node
}

// GetState attempts to fulfill a request (a group of variables with read/write requirements)
// and populates a VarReferences struct once all the values of all variables are made
// available. Notice that not every variable in the VarReq struct may actually be owned
// by the node running this function -- it only means the caller believes it so. In case
// the variable is not owned by the running node, the `Reference` entry will indicate so.
func (handler localStateHandler) GetState() (VarReferences, error) {
	refs := VarReferences(map[string]*Reference{})

	// prevent migration of the variables being queried while we
	// check ownership of them
	for _, borrowVar := range handler.group.Names {
		owner := handler.ownership.table[borrowVar.Name]

		owner.Lock()
		defer owner.Unlock()
	}

	for _, borrowVar := range handler.group.Names {
		ref := refBuilder(&handler, borrowVar).GetRef()
		refs.insert(borrowVar.Name, ref)
	}

	return refs, nil
}

// ReleaseState releases locks previously held by corresponding calls to GetState.
// Calling this function before a corresponding call to GetState results in a runtime
// panic by the Go scheduler (i.e., double unlock). This situation should not happen,
// however, unless the developer manually changes code generated by PGo.
func (handler localStateHandler) ReleaseState(refs VarReferences) error {
	for name, ref := range refs {
		if ref.Exclusive {
			handler.store.Set(name, ref.Value)
			handler.store.ReleaseExclusive(name)
		} else {
			handler.store.Release(name)
		}
	}

	return nil
}
