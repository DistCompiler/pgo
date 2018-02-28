// Implements an ordered set using the pgo/datatypes map as a container.
package datatypes

import (
	"fmt"
	rbt "github.com/emirpasic/gods/trees/redblacktree"
)

// We declare an interface to avoid dealing with weird pointer stuff
type Set interface {
	// Add all elements to the set
	Add(elts ...interface{})
	// Returns whether elt is in set
	Contains(elt interface{}) bool
	// Remove elt, if it is in the set
	Remove(elt interface{})
	// Remove all elements from set
	Clear()
	// Test if set is empty
	IsEmpty() bool
	// Return number of elements
	Size() int
	// Can be ranged over; in-order
	Iter() <-chan interface{}
	// Iterator with next(), prev()
	Iterator() rbt.Iterator
	// Return a new set equal to the given set
	Clone() Set
	// Set operations, defined in the usual way
	Difference(other Set) Set
	Equal(other Set) bool
	Intersect(other Set) Set
	IsSubset(other Set) bool
	Union(other Set) Set
	PowerSet() Set
	CartesianProduct(others ...Set) Set
	// Return the union of the elements of the set (given that this is a set of sets)
	EltUnion() Set
	// Return ordered slice of elts
	ToSlice() []interface{}
}

type set struct {
	m Map
}

// Return a new set that contains the elements elts.
func NewSet(elts ...interface{}) Set {
	ret := set{NewMap()}
	for _, i := range elts {
		ret.m.Put(i, struct{}{})
	}
	return &ret
}

func (s *set) Add(elts ...interface{}) {
	for _, i := range elts {
		s.m.Put(i, struct{}{})
	}
}

func (s *set) Contains(elt interface{}) bool {
	return s.m.Contains(elt)
}

func (s *set) Remove(elt interface{}) {
	s.m.Remove(elt)
}

func (s *set) Clear() {
	s.m.Clear()
}

func (s *set) IsEmpty() bool {
	return s.m.IsEmpty()
}

func (s *set) Size() int {
	return s.m.Size()
}

func (s *set) Iter() <-chan interface{} {
	return s.m.Keys()
}

func (s *set) Iterator() rbt.Iterator {
	return s.m.Iterator()
}

func (s *set) Clone() Set {
	ret := NewSet()
	for i := range s.Iter() {
		ret.Add(i)
	}
	return ret
}

// set operations
// TODO since keys are ordered, can slightly improve performance by traversing both trees at same time
func (s *set) Difference(other Set) Set {
	ret := NewSet()
	for i := range s.Iter() {
		if !other.Contains(i) {
			ret.Add(i)
		}
	}
	return ret
}

func (s *set) Equal(other Set) bool {
	if s.Size() != other.Size() {
		return false
	}

	for i := range s.Iter() {
		if !other.Contains(i) {
			return false
		}
	}
	return true
}

func (s *set) Intersect(other Set) Set {
	ret := NewSet()
	for i := range s.Iter() {
		if other.Contains(i) {
			ret.Add(i)
		}
	}
	return ret
}

func (s *set) IsSubset(other Set) bool {
	for i := range s.Iter() {
		if !other.Contains(i) {
			return false
		}
	}
	return true
}

func (s *set) Union(other Set) Set {
	ret := NewSet()
	for i := range s.Iter() {
		ret.Add(i)
	}
	for i := range other.Iter() {
		ret.Add(i)
	}
	return ret
}

func (s *set) PowerSet() Set {
	ret := NewSet()
	empty := NewSet()
	ret.Add(empty)

	for elt := range s.Iter() {
		// curSubsets stores all subsets with the current elt
		curSubsets := NewSet()
		for sub := range ret.Iter() {
			sub := sub.(Set)
			newSubset := NewSet()
			for i := range sub.Iter() {
				newSubset.Add(i)
			}
			newSubset.Add(elt)
			curSubsets.Add(newSubset)
		}
		ret = ret.Union(curSubsets)
	}
	return ret
}

// Return the Cartesian product s x others1 x others2 x ... x othersn
func (s *set) CartesianProduct(others ...Set) Set {
	ret := NewSet()
	// Recursively iterate over all elements in the cartesian product
	var cur []interface{}
	var iterateOverAllTuples func(int)
	iterateOverAllTuples = func(depth int) {
		if depth == len(others) {
			ret.Add(SliceToTuple(cur))
			return
		}
		for x := range others[depth].Iter() {
			// Iterate over all tuples with prefix cur
			cur = append(cur, x)
			iterateOverAllTuples(depth + 1)
			cur = cur[:len(cur)-1]
		}
	}
	for x := range s.Iter() {
		cur = append(cur, x)
		iterateOverAllTuples(0)
		cur = cur[:len(cur)-1]
	}
	return ret
}

func (s *set) EltUnion() Set {
	ret := NewSet()
	for x := range s.Iter() {
		ret = ret.Union(x.(Set))
	}
	return ret
}

func (s *set) ToSlice() []interface{} {
	ret := make([]interface{}, s.Size())
	i := 0
	for elt := range s.Iter() {
		ret[i] = elt
		i++
	}
	return ret
}

func (s *set) String() string {
	ret := "Set{"
	for i := range s.Iter() {
		ret += fmt.Sprintf("%v, ", i)
	}
	ret += "}"
	return ret
}
