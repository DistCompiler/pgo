package distsys

import (
	"log"
	"sync"
)

type DataEntry struct {
	sync.Mutex
	value interface{}
}

type SimpleDataStore struct {
	sync.RWMutex
	store map[string]*DataEntry
}

func CreateSimpleDataStore(initValues map[string]interface{}) *SimpleDataStore {
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

// acquire exclusive access to the key, safe handling of contention

// leaves the entry locked, thus the caller should unlock the entry when applicable
// leaves the store locked, thus the caller should unlock the store
// func (t *SimpleDataStore) access(key string, acquire bool) (*DataEntry, error) {
// 	t.RLock()
// 	// t.Lock()
// 	entry, ok := t.store[key]
// 	// t.Unlock()

// 	if !ok {
// 		t.Lock()
// 		return nil, KeyNotFoundError(key)
// 	}

// 	if acquire {
// 		// this lock must happen outside the critical section, or if we block here
// 		// the future unlocker will not be able to get into the critical section
// 		// to unlock it
// 		entry.Lock()
// 	}

// 	// lock the data store until an action has been completed
// 	// t.Lock()
// 	return entry, nil
// }

// Removes the key from the store, any further requests for it will fail
// ASSUMES: key has acquired
func (t *SimpleDataStore) remove(key string) {
	log.Printf("Remove(%s)\n", key)

	t.Lock()
	defer t.Unlock()
	entry, ok := t.store[key]

	if !ok {
		log.Panic(KeyNotFoundError(key))
	}

	delete(t.store, key)
	entry.Unlock()
}

// Creates key, but locks it so it must be set before it
// can be read
func (t *SimpleDataStore) create(key string, value interface{}) {
	log.Printf("Create(%s)\n", key)

	t.Lock()
	defer t.Unlock()
	_, ok := t.store[key]

	if ok {
		log.Panicf("Tried to create key %s, already exists\n", key)
	}

	entry := &DataEntry{
		value: value,
	}

	entry.Lock()
	t.store[key] = entry
}

// return the value, unlocking the entry
func (t *SimpleDataStore) Get(key string) (interface{}, error) {
	log.Printf("Get(%s)\n", key)

	t.RLock()
	defer t.RUnlock()
	entry, ok := t.store[key]

	if !ok {
		return nil, KeyNotFoundError(key)
	}

	entry.Lock()

	log.Printf("Got(%s)=%v", key, entry.value)
	return entry.value, nil
}

// return the value, keeping the entry locked
func (t *SimpleDataStore) GetExclusive(key string) (interface{}, error) {
	log.Printf("GetExclusive(%s)\n", key)

	t.RLock()
	defer t.RUnlock()
	entry, ok := t.store[key]

	if !ok {
		return nil, KeyNotFoundError(key)
	}

	entry.Lock()

	log.Printf("Got(%s)=%v", key, entry.value)
	return entry.value, nil
}

func (t *SimpleDataStore) Set(key string, value interface{}) {
	log.Printf("Set(%s)=%v\n", key, value)

	t.RLock()
	defer t.RUnlock()
	entry, ok := t.store[key]

	if !ok {
		log.Panic(KeyNotFoundError(key))
	}

	entry.value = value
	entry.Unlock()
}

func (t *SimpleDataStore) Release(key string) {
	log.Printf("Release(%s)\n", key)

	t.RLock()
	defer t.RUnlock()
	entry, ok := t.store[key]

	if !ok {
		log.Panic(KeyNotFoundError(key))
	}

	entry.Unlock()
}
