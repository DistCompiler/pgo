package datatypes

import "testing"

func TestNewTuple(t *testing.T) {
	a := NewTuple()
	assertEquals(0, a.Size(), t)

	a = NewTuple(1, 2, "s")
	assertEquals(3, a.Size(), t)
	assertEquals("s", a.At(2), t)

	a = SliceToTuple([]interface{}{"a", "b", NewTuple(1, 2)})
	assertEquals(3, a.Size(), t)
	assertEquals(NewTuple(1, 2), a.At(2), t)
}

func testAppend(t *testing.T) {
	a := NewTuple()
	b := NewTuple(1, 2)
	c := a.Append(b)
	assertEquals(NewTuple(1, 2), c, t)

	a = NewTuple("a", "b", "c")
	c = a.Append(b)
	assertEquals(NewTuple("a", "b", "c", 1, 2), c, t)

	c = b.Append(a)
	assertEquals(NewTuple(1, 2, "a", "b", "c"), c, t)
}

func TestHeadTail(t *testing.T) {
	a := NewTuple(1, 2)
	assertEquals(1, a.Head(), t)
	a = a.Tail()
	assertEquals(NewTuple(2), a, t)
	assertEquals(NewTuple(), a.Tail(), t)
}
