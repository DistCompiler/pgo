package pgoutil

type Tuple []interface{}

func NewTuple(elts ...interface{}) Tuple {
	ret := make(Tuple, len(elts))
	for i, elt := range elts {
		ret[i] = elt
	}
	return ret
}

func SliceToTuple(elts []interface{}) Tuple {
	return Tuple(elts)
}
