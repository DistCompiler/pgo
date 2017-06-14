package pgoutil

import "reflect"

// Determine whether there exists a combination of variables taken from sets such that P is true
func Exists(P interface{}, sets ...Set) bool {
	vf := reflect.ValueOf(P)
	// Recursively iterate over all possible combinations of variables
	// params stores the current tuple
	var params []reflect.Value
	var iterateOverAllTuples func(int) bool
	iterateOverAllTuples = func(depth int) bool {
		if depth == len(sets) {
			result := vf.Call(params)
			return result[0].Bool()
		}

		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix params
			params = append(params, reflect.ValueOf(x))
			if iterateOverAllTuples(depth + 1) {
				return true
			}
			params = params[:len(params)-1]
		}
		return false
	}
	return iterateOverAllTuples(0)
}

// Determine whether all possible combinations of variables from sets satisfy P
func ForAll(P interface{}, sets ...Set) bool {
	vf := reflect.ValueOf(P)
	// Recursively iterate over all possible combinations of variables
	// params stores the current tuple
	var params []reflect.Value
	var iterateOverAllTuples func(int) bool
	iterateOverAllTuples = func(depth int) bool {
		if depth == len(sets) {
			result := vf.Call(params)
			return result[0].Bool()
		}

		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix params
			params = append(params, reflect.ValueOf(x))
			if !iterateOverAllTuples(depth + 1) {
				return false
			}
			params = params[:len(params)-1]
		}
		return true
	}
	return iterateOverAllTuples(0)
}

// Return the smallest element x of S such that P(x), nil if none exists
func Choose(P interface{}, S Set) interface{} {
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if cond[0].Bool() {
			return x
		}
	}
	return nil
}
