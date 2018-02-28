package datatypes

import "reflect"

// Return the elements x in S such that P(x)
func SetConstructor(S Set, P interface{}) Set {
	ret := NewSet()
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
func SetImage(f interface{}, sets ...Set) Set {
	ret := NewSet()
	// Recursively iterate over all possible tuples in the cartesian product of all sets, and add image to set
	// params stores the current tuple
	var params []reflect.Value
	vf := reflect.ValueOf(f)
	var iterateOverAllTuples func(int)
	iterateOverAllTuples = func(depth int) {
		if depth == len(sets) {
			toAdd := vf.Call(params)
			ret.Add(toAdd[0].Interface())
			return
		}
		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix params
			params = append(params, reflect.ValueOf(x))
			iterateOverAllTuples(depth + 1)
			params = params[:len(params)-1]
		}
	}
	iterateOverAllTuples(0)
	return ret
}
