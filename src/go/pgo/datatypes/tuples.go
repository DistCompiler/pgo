// A basic tuple type, which is immutable.
package datatypes

import "fmt"

type Tuple interface {
	// Return ith component
	At(i int) interface{}
	// Return new tuple with ith component set to elt
	Set(i int, elt interface{}) Tuple
	Size() int
	// Return new tuple with components appended
	Append(i ...interface{}) Tuple
	// Return first elt
	Head() interface{}
	// Return new tuple with head removed
	Tail() Tuple
	// Can be ranged over
	Iter() <-chan interface{}
	String() string
}

// Type tuple implements Tuple.
type tuple struct {
	Data []interface{}
}

func NewTuple(elts ...interface{}) Tuple {
	ret := tuple{make([]interface{}, len(elts))}
	for i, elt := range elts {
		ret.Data[i] = elt
	}
	return ret
}

func SliceToTuple(elts []interface{}) Tuple {
	eltsCopy := make([]interface{}, len(elts))
	copy(eltsCopy, elts)
	return tuple{eltsCopy}
}

func (t tuple) At(i int) interface{} {
	if i < 0 || i >= len(t.Data) {
		panic(fmt.Sprintf("The index %v is invalid for the tuple %v", i, t.Data))
	}
	return t.Data[i]
}

func (t tuple) Set(i int, elt interface{}) Tuple {
	if i < 0 || i >= len(t.Data) {
		panic(fmt.Sprintf("The index %v is invalid for the tuple %v", i, t.Data))
	}
	ret := SliceToTuple(t.Data)
	ret.(tuple).Data[i] = elt
	return ret
}

func (t tuple) Size() int {
	return len(t.Data)
}

func (t tuple) Append(i ...interface{}) Tuple {
	data := make([]interface{}, 0, t.Size()+len(i))
	data = append(data, t.Data...)
	data = append(data, i)
	return tuple{data}
}

func (t tuple) Head() interface{} {
	if len(t.Data) == 0 {
		panic("Tried to take the Head of an empty tuple")
	}
	return t.Data[0]
}

func (t tuple) Tail() Tuple {
	if len(t.Data) == 0 {
		panic("Tried to take the Tail of an empty tuple")
	}
	// don't need to clone since the data isn't exposed anyway
	return tuple{t.Data[1:]}
}

func (t tuple) Iter() <-chan interface{} {
	ret := make(chan interface{})
	go func() {
		for _, i := range t.Data {
			ret <- i
		}
		close(ret)
	}()
	return ret
}

func (t tuple) String() string {
	ret := "Tuple{"
	for _, i := range t.Data {
		ret += fmt.Sprintf("%v ", i)
	}
	ret += "}"
	return ret
}
