// A basic tuple type, which is immutable.
package pgoutil

import "fmt"

type Tuple struct {
	data []interface{}
}

func NewTuple(elts ...interface{}) Tuple {
	ret := Tuple{make([]interface{}, len(elts))}
	for i, elt := range elts {
		ret.data[i] = elt
	}
	return ret
}

func SliceToTuple(elts []interface{}) Tuple {
	eltsCopy := make([]interface{}, len(elts))
	copy(eltsCopy, elts)
	return Tuple{eltsCopy}
}

// Return the ith component
func (t *Tuple) At(i int) interface{} {
	if i < 0 || i >= len(t.data) {
		panic(fmt.Sprintf("The index %v is invalid for the tuple %v", i, t.data))
	}
	return t.data[i]
}

func (t *Tuple) Size() int {
	return len(t.data)
}

// Return a new tuple with the components appended.
func (t *Tuple) Append(i ...interface{}) Tuple {
	data := make([]interface{}, 0, t.Size() + len(i))
	data = append(data, t.data...)
	data = append(data, i)
	return Tuple{data}
}

func (t *Tuple) Iter() <-chan interface{} {
	ret := make(chan interface{})
	go func() {
		for _, i := range t.data {
			ret <- i
		}
		close(ret)
	}()
	return ret
}
