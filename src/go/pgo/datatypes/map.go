// Implements a generic, thread-safe ordered map using a red-black tree.
package datatypes

import (
	"fmt"
	rbt "github.com/emirpasic/gods/trees/redblacktree"
	"reflect"
	"sync"
)

// Generic comparator function that satisfies utils.Comparator
func comp(a, b interface{}) int {
	if reflect.TypeOf(a) != reflect.TypeOf(b) {
		panic(fmt.Sprintf("Arguments to comparator are not the same type: %T %T", a, b))
	}
	// hopefully no typos
	switch a := a.(type) {
	case bool:
		if !a && b.(bool) {
			return -1
		} else if !b.(bool) && a {
			return 1
		}
		return 0
	case int:
		if a < b.(int) {
			return -1
		} else if a > b.(int) {
			return 1
		}
		return 0
	case uint:
		if a < b.(uint) {
			return -1
		} else if a > b.(uint) {
			return 1
		}
		return 0
	case uint8:
		if a < b.(uint8) {
			return -1
		} else if a > b.(uint8) {
			return 1
		}
		return 0
	case uint16:
		if a < b.(uint16) {
			return -1
		} else if a > b.(uint16) {
			return 1
		}
		return 0
	case uint32:
		if a < b.(uint32) {
			return -1
		} else if a > b.(uint32) {
			return 1
		}
		return 0
	case uint64:
		if a < b.(uint64) {
			return -1
		} else if a > b.(uint64) {
			return 1
		}
		return 0
	case int8:
		if a < b.(int8) {
			return -1
		} else if a > b.(int8) {
			return 1
		}
		return 0
	case int16:
		if a < b.(int16) {
			return -1
		} else if a > b.(int16) {
			return 1
		}
		return 0
	case int32:
		if a < b.(int32) {
			return -1
		} else if a > b.(int32) {
			return 1
		}
		return 0
	case int64:
		if a < b.(int64) {
			return -1
		} else if a > b.(int64) {
			return 1
		}
		return 0
	case float32:
		if a < b.(float32) {
			return -1
		} else if a > b.(float32) {
			return 1
		}
		return 0
	case float64:
		if a < b.(float64) {
			return -1
		} else if a > b.(float64) {
			return 1
		}
		return 0
	case string:
		if a < b.(string) {
			return -1
		} else if a > b.(string) {
			return 1
		}
		return 0
	//compare by real then by imag
	case complex64:
		if real(a) < real(b.(complex64)) {
			return -1
		} else if real(a) > real(b.(complex64)) {
			return 1
		}
		if imag(a) < imag(b.(complex64)) {
			return -1
		} else if imag(a) > imag(b.(complex64)) {
			return 1
		}
		return 0
	case complex128:
		if real(a) < real(b.(complex128)) {
			return -1
		} else if real(a) > real(b.(complex128)) {
			return 1
		}
		if imag(a) < imag(b.(complex128)) {
			return -1
		} else if imag(a) > imag(b.(complex128)) {
			return 1
		}
		return 0
	case Tuple:
		b := b.(Tuple)
		for i := 0; i < a.Size(); i++ {
			if i == b.Size() {
				return 1
			}
			switch comp(a.At(i), b.At(i)) {
			case -1:
				return -1
			case 1:
				return 1
			}
		}

		if a.Size() == b.Size() {
			return 0
		}
		return -1
	case Set:
		// Sets are compared using their elements.
		// Elements are ordered so we can just iterate.
		b := b.(Set)
		aIter, bIter := a.Iter(), b.Iter()
		for i := 0; i < a.Size(); i++ {
			if i == b.Size() {
				return 1
			}
			switch comp(<-aIter, <-bIter) {
			case -1:
				return -1
			case 1:
				return 1
			}
		}

		if a.Size() == b.Size() {
			return 0
		}
		return -1
	case Map:
		// Maps are compared first by their keys, then their corresponding values.
		// Elements are ordered so we can just iterate.
		b := b.(Map)
		aIter, bIter := a.Iter(), b.Iter()
		for i := 0; i < a.Size(); i++ {
			if i == b.Size() {
				return 1
			}
			aElt, bElt := <-aIter, <-bIter
			switch comp(aElt.Key, bElt.Key) {
			case -1:
				return -1
			case 1:
				return 1
			case 0:
				switch comp(aElt.Val, bElt.Val) {
				case -1:
					return -1
				case 1:
					return 1
				}
			}
		}

		if a.Size() == b.Size() {
			return 0
		}
		return -1
	default:
		// check if this is a struct or ptr
		// structs are compared based on each (exported) field (in order)
		// ptrs are compared based on pointed-to value
		// slices are compared in the same way as tuples
		v := reflect.ValueOf(a)
		w := reflect.ValueOf(b)
		switch v.Kind() {
		case reflect.Ptr:
			for v.Kind() == reflect.Ptr || v.Kind() == reflect.Interface {
				v = v.Elem()
				w = w.Elem()
			}
			return comp(v.Interface(), w.Interface())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if !v.CanInterface() || !w.CanInterface() {
					// this is an unexported field; panic if try to access
					continue
				}
				switch comp(v.Field(i).Interface(), w.Field(i).Interface()) {
				case 1:
					return 1
				case -1:
					return -1
				}
			}
			return 0
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				if i == w.Len() {
					return 1
				}
				switch comp(v.Index(i).Interface(), w.Index(i).Interface()) {
				case -1:
					return -1
				case 1:
					return 1
				}
			}

			if v.Len() == w.Len() {
				return 0
			}
			return -1
		default:
			panic(fmt.Sprintf("The type %T is not comparable", a))
		}
	}
}

type KVPair struct {
	Key interface{}
	Val interface{}
}

type Map interface {
	// Put the key-value pair in the map. If the key already exists we replace the value.
	Put(key, val interface{})
	// Return whether the key is in the map.
	Contains(key interface{}) bool
	// Get the val associated with the key; nil if key is not in map
	Get(key interface{}) interface{}
	// Remove the entry with the given key.
	Remove(key interface{})
	// Clear all entries.
	Clear()
	// Return true if the map is empty.
	IsEmpty() bool
	// Return the number of keys in the map.
	Size() int
	// Return the key set of the map.
	Domain() Set
	// Iterators over keys, values, and entries.
	Keys() <-chan interface{}
	Values() <-chan interface{}
	Iter() <-chan KVPair
	// Iterator with Next(), Prev()
	Iterator() rbt.Iterator
	// Return a new map equivalent to the current map.
	Clone() Map
}

// Implements the Map interface.
type mp struct {
	tree *rbt.Tree
	sync.RWMutex
}

func NewMap() Map {
	return &mp{rbt.NewWith(comp), sync.RWMutex{}}
}

func (m *mp) Put(key interface{}, val interface{}) {
	// If key/val are slices, we need to create a deep copy.
	kType, kVal := reflect.TypeOf(key), reflect.ValueOf(key)
	if kType.Kind() == reflect.Slice {
		cpy := reflect.MakeSlice(kType, kVal.Len(), kVal.Len())
		reflect.Copy(cpy, kVal)
		key = cpy.Interface()
	}

	eType, eVal := reflect.TypeOf(val), reflect.ValueOf(val)
	if eType.Kind() == reflect.Slice {
		cpy := reflect.MakeSlice(eType, eVal.Len(), eVal.Len())
		reflect.Copy(cpy, eVal)
		val = cpy.Interface()
	}

	// If key/val are maps, we need to clone the map.
	if k, ok := key.(Map); ok {
		key = k.Clone()
	}
	if e, ok := val.(Map); ok {
		val = e.Clone()
	}

	m.Lock()
	defer m.Unlock()
	m.tree.Put(key, val)
}

func (m *mp) Contains(key interface{}) bool {
	m.RLock()
	defer m.RUnlock()
	_, found := m.tree.Get(key)
	return found
}

func (m *mp) Get(key interface{}) interface{} {
	m.RLock()
	defer m.RUnlock()
	ret, _ := m.tree.Get(key)
	return ret
}

func (m *mp) Remove(key interface{}) {
	m.Lock()
	defer m.Unlock()
	m.tree.Remove(key)
}

func (m *mp) Clear() {
	m.Lock()
	defer m.Unlock()
	m.tree.Clear()
}

func (m *mp) IsEmpty() bool {
	m.RLock()
	defer m.RUnlock()
	return m.tree.Empty()
}

func (m *mp) Size() int {
	m.RLock()
	defer m.RUnlock()
	return m.tree.Size()
}

// Backed by the map.
func (m *mp) Domain() Set {
	return &set{m}
}

//Iterators (can be ranged over)
func (m *mp) Keys() <-chan interface{} {
	m.RLock()
	iter := m.tree.Iterator()
	ret := make(chan interface{})

	go func() {
		defer m.RUnlock()
		for iter.Next() {
			ret <- iter.Key()
		}
		close(ret)
	}()
	return ret
}

func (m *mp) Values() <-chan interface{} {
	m.RLock()
	iter := m.tree.Iterator()
	ret := make(chan interface{})

	go func() {
		defer m.RUnlock()
		for iter.Next() {
			ret <- iter.Value()
		}
		close(ret)
	}()
	return ret
}

func (m *mp) Iter() <-chan KVPair {
	m.RLock()
	iter := m.tree.Iterator()
	ret := make(chan KVPair, m.Size())

	go func() {
		defer m.RUnlock()
		for iter.Next() {
			ret <- KVPair{iter.Key(), iter.Value()}
		}
		close(ret)
	}()
	return ret
}

func (m *mp) Iterator() rbt.Iterator {
	return m.tree.Iterator()
}

func (m *mp) Clone() Map {
	ret := NewMap()
	for i := range m.Iter() {
		ret.Put(i.Key, i.Val)
	}
	return ret
}

func (m *mp) String() string {
	ret := "Map{"
	m.RLock()
	defer m.RUnlock()
	for kv := range m.Iter() {
		ret += fmt.Sprintf("%v = %v, ", kv.Key, kv.Val)
	}
	ret += "}"
	return ret
}
