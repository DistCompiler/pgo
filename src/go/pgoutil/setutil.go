package pgoutil

import (
	"mapset"
	"reflect"
)

func EltUnion(S mapset.Set) mapset.Set {
	ret := mapset.NewSet()
	for x := range S.Iter() {
		ret = ret.Union(x.(mapset.Set))
	}
	return ret
}

// Return the elements x in S such that P(x)
func SetConstructor(S mapset.Set, P interface{}) mapset.Set {
	ret := mapset.NewSet()
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if cond[0].Bool() {
			ret.Add(x)
		}
	}
	return ret
}

// Return the image of the function f over the cartesian product of sets
func SetImage(f interface{}, sets ...mapset.Set) mapset.Set {
	ret := mapset.NewSet()
	// Recursively iterate over all possible tuples in the cartesian product of all sets, and add image to set
	// prev stores the current tuple
	var prev []interface{}
	vf := reflect.ValueOf(f)
	var iterateOverAllTuples func(int)
	iterateOverAllTuples = func(depth int) {
		if depth == len(sets) {
			params := make([]reflect.Value, len(sets))
			for i, val := range prev {
				params[i] = reflect.ValueOf(val)
			}
			toAdd := vf.Call(params)
			ret.Add(toAdd[0].Interface())
			return
		}
		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix prev
			prev = append(prev, x)
			iterateOverAllTuples(depth + 1)
			prev = prev[:len(prev)-1]
		}
	}
	iterateOverAllTuples(0)
	return ret
}
