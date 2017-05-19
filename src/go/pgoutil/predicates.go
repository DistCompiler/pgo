package pgoutil

import (
	"mapset"
	"reflect"
)

// Determine whether there exists a combination of variables taken from sets such that P is true
func Exists(P interface{}, sets ...mapset.Set) bool {
	vf := reflect.ValueOf(P)
	// Recursively iterate over all possible combinations of variables, and add image to set
	// prev stores the current tuple
	var prev []interface{}
	var iterateOverAllTuples func(int) bool
	iterateOverAllTuples = func(depth int) bool {
		if depth == len(sets) {
			params := make([]reflect.Value, len(sets))
			for i, val := range prev {
				params[i] = reflect.ValueOf(val)
			}
			result := vf.Call(params)
			return result[0].Bool()
		}

		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix prev
			prev = append(prev, x)
			if iterateOverAllTuples(depth + 1) {
				return true
			}
			prev = prev[:len(prev)-1]
		}
		return false
	}
	return iterateOverAllTuples(0)
}

// Determine whether all possible combinations of variables from sets satisfy P
func ForAll(P interface{}, sets ...mapset.Set) bool {
	vf := reflect.ValueOf(P)
	// Recursively iterate over all possible combinations of variables, and add image to set
	// prev stores the current tuple
	var prev []interface{}
	var iterateOverAllTuples func(int) bool
	iterateOverAllTuples = func(depth int) bool {
		if depth == len(sets) {
			params := make([]reflect.Value, len(sets))
			for i, val := range prev {
				params[i] = reflect.ValueOf(val)
			}
			result := vf.Call(params)
			return result[0].Bool()
		}

		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix prev
			prev = append(prev, x)
			if !iterateOverAllTuples(depth + 1) {
				return false
			}
			prev = prev[:len(prev)-1]
		}
		return true
	}
	return iterateOverAllTuples(0)
}

func Choose(P interface{}, S mapset.Set) interface{} {
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if cond[0].Bool() {
			return x
		}
	}
	return nil
}
