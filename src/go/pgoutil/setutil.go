package pgoutil

import "mapset"

func EltUnion(S mapset.Set) mapset.Set {
	ret := mapset.NewSet()
	for x := range S.Iter() {
		ret = ret.Union(x.(mapset.Set))
	}
	return ret
}

// Return the elements x in S such that P(x)
func SetConstructor(S mapset.Set, P func(interface{}) bool) mapset.Set {
	ret := mapset.NewSet()
	for x := range S.Iter() {
		if P(x) {
			ret.Add(x)
		}
	}
	return ret
}

// Return the image of the function f over the sets in sets
func SetImage(f func(...interface{}) interface{}, sets ...mapset.Set) mapset.Set {
	ret := mapset.NewSet()
	// Recursively iterate over all possible tuples in the cartesian product of all sets, and add image to set
	// prev stores the current tuple
	var prev []interface{}
	var iterateOverAllTuples func(int)
	iterateOverAllTuples = func(depth int) {
		if depth == len(sets) {
			ret.Add(f(prev...))
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
