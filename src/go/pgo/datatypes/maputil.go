package datatypes

import "reflect"

// Create a map which maps the elements in S using the mapping f
func MapsTo(f interface{}, sets ...Set) Map {
	vf := reflect.ValueOf(f)
	ret := NewMap()
	var params []reflect.Value
	var params2 []interface{}
	var iterateOverAllTuples func(int)
	iterateOverAllTuples = func(depth int) {
		if depth == len(sets) {
			result := vf.Call(params)
			if depth == 1 {
				ret.Put(params2[0], result[0].Interface())
			} else {
				ret.Put(SliceToTuple(params2), result[0].Interface())
			}
			return
		}

		for x := range sets[depth].Iter() {
			// Iterate over all tuples with prefix params
			params = append(params, reflect.ValueOf(x))
			params2 = append(params2, x)
			iterateOverAllTuples(depth + 1)
			params = params[:len(params)-1]
			params2 = params2[:len(params2)-1]
		}
	}
	iterateOverAllTuples(0)
	return ret
}

// An "except pair" data structure
type pair struct {
	first  interface{}
	second interface{}
}

func EP(first, second interface{}) pair {
	return pair{first, second}
}

// Create a map based on the existing map f, except each except[i].first is mapped to except[i].second
func Except(f Map, except ...pair) Map {
	ret := NewMap()
	for i := range f.Iter() {
		ret.Put(i.Key, i.Val)
	}
	for _, i := range except {
		ret.Put(i.first, i.second)
	}
	return ret
}
