package distsys

import (
	"bytes"
	"fmt"
	"log"
	"sync"
)

const (
	readOnlyMode = iota
	writeMode
)

// NameNotFoundError occurs when a lookup for an unknown name in the store is made
type NameNotFoundError string

func (e NameNotFoundError) Error() string {
	return fmt.Sprintf("Local store: name not found: %s", e)
}

// DataEntry represents a single piece of global state that is
// contained in this node. Entries are protected by a read-write lock
// in order to make sure that two different nodes trying to read
// from/write to the same piece of global state concurrently will not
// lead to inconsistencies in program execution (race conditions)
type DataEntry struct {
	sync.RWMutex             // protects access to `value`
	value        interface{} // value, which can be of any type
}

// SimpleDataStore implements a volatile store that can be used to keep
// track of global state of applications compiled by PGo. State is modeled
// as a table that maps names (such as variable names) to values of any type,
// encapsulated as `DataEntry` structs.
type SimpleDataStore struct {
	sync.RWMutex                       // protects access to the variable table
	store        map[string]*DataEntry // maps variable names to their values
}

// NewSimpleStore creates a new `SimpleDataStore` struct. An initial state
// can be given in the `initValues` parameter, which makes sure the state local
// to this node will contain the data passed to this function.
func NewSimpleDataStore(initValues map[string]interface{}) *SimpleDataStore {
	store := make(map[string]*DataEntry, len(initValues))
	for key, value := range initValues {
		store[key] = &DataEntry{
			value: value,
		}
	}

	return &SimpleDataStore{
		store: store,
	}
}

// Hold reads a `name` from the data store for non-exclusive access (i.e., read only).
func (data *SimpleDataStore) Hold(name string) (interface{}, error) {
	log.Printf("Hold(%s)\n", name)
	return data.hold(name, readOnlyMode)
}

// HoldExclusive reads a `name` from the data store and prohibits anyone else from
// reading or writing to that name
func (data *SimpleDataStore) HoldExclusive(name string) (interface{}, error) {
	log.Printf("HoldExclusive(%s)\n", name)
	return data.hold(name, writeMode)
}

func (data *SimpleDataStore) hold(name string, mode int) (interface{}, error) {
	log.Printf("%v", data)
	data.RLock()
	defer data.RUnlock()

	entry, inStore := data.store[name]

	if !inStore {
		return nil, NameNotFoundError(name)
	}

	if mode == readOnlyMode {
		entry.RLock()
	} else {
		entry.Lock()
	}

	return entry.value, nil
}

// Release indicates that a variable previously held with non-exclusive access
// is no longer being used
func (data *SimpleDataStore) Release(name string) {
	log.Printf("Release(%s)\n", name)
	data.release(name, readOnlyMode)
}

// ReleaseExclusive indicates that a variable previously held with exclusive
// access is no longer being used
func (data *SimpleDataStore) ReleaseExclusive(name string) {
	log.Printf("ReleaseExclusive(%s)\n", name)
	data.release(name, writeMode)
}

func (data *SimpleDataStore) release(name string, mode int) {
	log.Printf("%v", data)
	data.RLock()
	defer data.RUnlock()

	entry, inStore := data.store[name]

	if !inStore {
		log.Panic(NameNotFoundError(name))
	}

	if mode == readOnlyMode {
		entry.RUnlock()
	} else {
		entry.Unlock()
	}
}

// Set updates the value associated with a given `name` in the underlying store.
// Invoking this function is only safe if the caller has previously called
// HoldExclusive.
func (data *SimpleDataStore) Set(name string, val interface{}) {
	entry, inStore := data.store[name]
	if !inStore {
		log.Panic(NameNotFoundError(name))
	}

	entry.value = val
}

func (data *SimpleDataStore) String() string {
	var buf bytes.Buffer
	var i int

	for name, entry := range data.store {
		if i > 0 {
			buf.WriteString(", ")
		}

		buf.WriteString(fmt.Sprintf("%s => %v (%p)", name, entry.value, entry))
		i++
	}

	return fmt.Sprintf("Store(%s)", buf.String())
}
