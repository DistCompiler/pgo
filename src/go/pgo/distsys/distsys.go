package distsys

import (
	"fmt"
	"log"
	"sort"
	"strings"
	"sync"
)

// OwnershipTable maps variable names to host addresses that own them at
// different moments in time
type OwnershipTable struct {
	sync.RWMutex
	table map[string]string
}

func NewOwnershipTable(ownership map[string]string) *OwnershipTable {
	return &OwnershipTable{
		table: ownership,
	}
}

// UnknownOwnerError happens when a lookup for a certain piece of global
// state on the ownership table does not yield any result
type UnknownOwnerError struct {
	name string
}

func (e *UnknownOwnerError) Error() string {
	return fmt.Sprintf("Ownership table lookup failed: no owner for variable %s", e.name)
}

// Lookup searches for the address of the peer in the system that currently owns
// the variable with the given name. Panics if the information is unknown
func (ownership *OwnershipTable) Lookup(name string) string {
	peer, found := ownership.table[name]
	if !found {
		log.Panicf("%v", UnknownOwnerError{name})
	}

	return peer
}

// Network represents the state of the distributed system at a given point in
// time. It includes the lists of nodes running in the system, as well as the
// underlying store for global state.
type Network struct {
	*ProcessInitialization

	self   string          // the identifier of the running node
	hosts  []string        // the list of addresses of all nodes in the system
	owners OwnershipTable  // the current state ownership table
	store  SimpleDataStore // the underlying store for state owned by the running node
}

// NetworkRPC is a thin wrapper around the `Network` struct such that only a
// few methods are exposed to via RPC to other nodes
type NetworkRPC struct {
	network *Network
}

// BorrowSpec specifies a borrow request from a node to another. It includes a list
// of variables names for which exclusive access is required, as well as a list of
// names for which non-exclusive access is sufficient
type BorrowSpec struct {
	ReadNames  []string // which variables we are reading (non-exclusive access)
	WriteNames []string // which variables we are writing (exclusive access)
}

// BorrowSpecVariable represents a the borrowing requirements of a single variable
// within a `BorrowSpec`
type BorrowSpecVariable struct {
	Name      string
	Exclusive bool
}

type SortedBorrowSpec []*BorrowSpecVariable

func (spec SortedBorrowSpec) Len() int {
	return len(spec)
}

func (spec SortedBorrowSpec) Swap(i, j int) {
	spec[i], spec[j] = spec[j], spec[i]
}

func (spec SortedBorrowSpec) Less(i, j int) bool {
	return strings.Compare(spec[i].Name, spec[j].Name) < 0
}

// SortedNames returns a list of requested names in the borrow spec in alphabetical
// order.
func (spec *BorrowSpec) Sorted() SortedBorrowSpec {
	// remove duplicates across read and write names
	namesSet := map[string]bool{}

	for _, readVar := range spec.ReadNames {
		namesSet[readVar] = true
	}

	for _, writeVar := range spec.WriteNames {
		namesSet[writeVar] = true
	}

	names := []*BorrowSpecVariable{}
	for name, _ := range namesSet {
		writeVariable := false

		// if the current variable is a write-variable, access to
		// it must be declared exclusive
		for _, writeVar := range spec.WriteNames {
			if writeVar == name {
				writeVariable = true
				break
			}
		}

		names = append(names, &BorrowSpecVariable{
			Name:      name,
			Exclusive: writeVariable,
		})
	}

	sort.Sort(SortedBorrowSpec(names))
	return SortedBorrowSpec(names)
}

// Reference represents a variable reference. It indicates the current variable
// value and whether the reference is exclusive (no other node has access to
// it, and allows the node to mutate the value).
type Reference struct {
	Value     interface{} // the value of a variable reference
	exclusive bool        // whether access to this value is exclusive
}

// VarReferences maps variable names to references. Can be used when a node is
// transferring state it knows about to another node in the system
type VarReferences map[string]Reference

// GlobalStateOperation represents an attempt to get access to a set of variables
// from the system's global state. Depending on which variables are requested and
// who owns each part of it, this struct is able to group variables together
// in order to minimize the number of requests necessary to get access to the
// state requested
type GlobalStateOperation struct {
	spec      *BorrowSpec
	ownership *OwnershipTable
}

// VarReq represents a request to be sent to another peer in the system. It encapsulates
// the address of the peer as well as the pieces of state required from it
type VarReq struct {
	Peer  string                // the host to which this request should be sent
	Names []*BorrowSpecVariable // maps state names to whether exclusive access is required or not
}

// Groups places the variables contained in a `BorrowSpec` in groupings that minimize
// the number of network calls necessary to get access to the global state required.
// Given the state of the ownership table at the time of call, this function will
// group variables based on ownership.
//
// Examples:
//   ownershipTable := NewOwnershipTable(map[string]string{
//     "a": "10.10.10.1",
//     "b": "10.10.10.1",
//     "c": "10.10.10.3",
//   })
//
//   borrowSpec := BorrowSpec{
//     ReadNames:  []string{"a", "b", "c"},
//     WriteNames: []string{"b"},
//   }
//
//   op := GlobalStateOperation(spec: &spec, ownership: ownershipTable)
//   op.Groups() // =>
//     []*VarReq{
//       *VarReq{Peer: "10.10.10.1", Names: []*BorrowSpecVariable{{Name: "a", Exclusive: false}, ... },
//       *VarReq{Peer: "10.10.10.3", Names: []*BorrowSpecVariable{{Name: "c", Exclusive: false}, ...}
//     }
func (op *GlobalStateOperation) Groups() []*VarReq {
	reqs := []*VarReq{}
	sorted := op.spec.Sorted()

	// if borrow spec is empty, return early
	if len(sorted) == 0 {
		return reqs
	}

	// prevent migrations while we are grouping requests
	op.ownership.RLock()
	defer op.ownership.RUnlock()

	var currentPeer string
	var currVarReq *VarReq
	for _, borrowVar := range sorted {
		owner := op.ownership.Lookup(borrowVar.Name)

		// if this is the first iteration, the current peer is the owner
		// of the current variable
		if len(currentPeer) == 0 {
			currentPeer = owner
			currVarReq = &VarReq{
				Peer:  currentPeer,
				Names: []*BorrowSpecVariable{},
			}
		}

		if owner == currentPeer {
			currVarReq.Names = append(currVarReq.Names, borrowVar)
		} else {
			reqs = append(reqs, currVarReq)

			currentPeer = owner
			currVarReq = &VarReq{
				Peer:  currentPeer,
				Names: []*BorrowSpecVariable{borrowVar},
			}
		}
	}

	// add last group to the list of requests
	reqs = append(reqs, currVarReq)

	return reqs
}
