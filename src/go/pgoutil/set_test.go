package pgoutil

import "testing"

func TestNewSet(t *testing.T) {
	a := NewSet()
	assertEquals(0, a.Size(), t)
	assertEquals(true, a.IsEmpty(), t)

	a = NewSet(1, 2, 3, 4, 5)
	assertEquals(5, a.Size(), t)
	assertEquals(true, a.Contains(5), t)
}

func TestAddRemoveSet(t *testing.T) {
	a := NewSet()
	a.Add(1)
	a.Add(2)
	a.Add(3)
	assertEquals(3, a.Size(), t)

	a.Add(3)
	assertEquals(3, a.Size(), t)

	assertEquals(true, a.Contains(1) && a.Contains(2) && a.Contains(3), t)

	a.Remove(3)
	assertEquals(2, a.Size(), t)
	assertEquals(true, a.Contains(1) && a.Contains(2), t)
	assertEquals(false, a.Contains(3), t)

	a.Remove(2)
	a.Remove(1)
	assertEquals(0, a.Size(), t)

	a = NewSet()
	b := NewSet()
	c := NewSet(1, 2, 5)
	a.Add(1)
	a.Add(2)
	a.Add(5)
	b.Add(1, 2, 5)
	assertEquals(true, a.Equal(b), t)
	assertEquals(true, b.Equal(c), t)

	a.Clear()
	assertEquals(0, a.Size(), t)
	assertEquals(true, a.IsEmpty(), t)
}

func TestSubset(t *testing.T) {
	a := NewSet(1, 2, 3, 5, 7)
	assertEquals(true, NewSet().IsSubset(a), t)

	b := NewSet(3, 5, 7)
	assertEquals(true, b.IsSubset(a), t)
	b.Add(9)
	assertEquals(false, b.IsSubset(a), t)
}

func TestUnionIntersect(t *testing.T) {
	a, b := NewSet(), NewSet(1, 2, 3, 4, 5)
	c := a.Union(b)
	assertEquals(5, c.Size(), t)

	d := NewSet(0, 6, 7)
	c = c.Union(d)
	assertEquals(8, c.Size(), t)

	e := NewSet(0, 2, 3)
	c = c.Union(e)
	assertEquals(8, c.Size(), t)

	c = a.Intersect(b)
	assertEquals(0, c.Size(), t)

	a.Add(6, 7, 8)
	c = a.Intersect(b)
	assertEquals(0, c.Size(), t)

	a.Add(1)
	c = a.Intersect(b)
	assertEquals(1, c.Size(), t)
	assertEquals(true, c.Contains(1), t)
}

func TestDifference(t *testing.T) {
	a := NewSet(1, 2, 3)
	b := NewSet(1, 3, 5, 6, 7)
	c := a.Difference(b)
	assertEquals(1, c.Size(), t)
	assertEquals(true, c.Contains(2), t)
}

func TestEqual(t *testing.T) {
	a := NewSet()
	b := NewSet()
	assertEquals(true, a.Equal(b), t)
	assertEquals(true, b.Equal(a), t)

	a.Add(10)
	assertEquals(false, a.Equal(b), t)
	assertEquals(false, b.Equal(a), t)

	b.Add(10)
	assertEquals(true, a.Equal(b), t)

	b.Add(11, 12, 13)
	assertEquals(false, a.Equal(b), t)
	a.Add(11, 12, 13)
	assertEquals(true, a.Equal(b), t)

	a.Remove(11)
	a.Add(8)
	assertEquals(false, a.Equal(b), t)
}

func TestIter(t *testing.T) {
	a := NewSet("D", "A", "C", "B")
	b := a.Iter()
	assertEquals("A", <-b, t)
	assertEquals("B", <-b, t)
	assertEquals("C", <-b, t)
	assertEquals("D", <-b, t)

	c := NewSet()
	for elt := range a.Iter() {
		c.Add(elt)
	}
	assertEquals(true, a.Equal(c), t)
}

func TestPowerSet(t *testing.T) {
	a := NewSet()
	b := a.PowerSet()
	assertEquals(1, b.Size(), t)
	assertEquals(true, b.Contains(NewSet()), t)

	a.Add(1, 2, 3)
	b = a.PowerSet()
	assertEquals(8, b.Size(), t)
	assertEquals(true, b.Contains(NewSet(1, 2)), t)

	a.Add(6, 7)
	b = a.PowerSet()
	assertEquals(32, b.Size(), t)
}

func TestCartProduct(t *testing.T) {
	a := NewSet()
	b := NewSet()
	c := a.CartesianProduct(b)
	assertEquals(0, c.Size(), t)

	a.Add(1, 2)
	c = a.CartesianProduct(b)
	assertEquals(0, c.Size(), t)
	c = b.CartesianProduct(a)
	assertEquals(0, c.Size(), t)

	b.Add(4, 5)
	c = a.CartesianProduct(b)
	assertEquals(4, c.Size(), t)
	it := c.Iter()
	assertEquals(NewTuple(1, 4), <-it, t)
	assertEquals(NewTuple(1, 5), <-it, t)
	assertEquals(NewTuple(2, 4), <-it, t)
	assertEquals(NewTuple(2, 5), <-it, t)

	c = b.CartesianProduct(a)
	assertEquals(4, c.Size(), t)
	it = c.Iter()
	assertEquals(NewTuple(4, 1), <-it, t)
	assertEquals(NewTuple(4, 2), <-it, t)
	assertEquals(NewTuple(5, 1), <-it, t)
	assertEquals(NewTuple(5, 2), <-it, t)

	d := NewSet(7, 8)
	c = a.CartesianProduct(b, d)
	assertEquals(8, c.Size(), t)
	it = c.Iter()
	assertEquals(NewTuple(1, 4, 7), <-it, t)
}

func TestEltUnion(t *testing.T) {
	S := NewSet(
		NewSet(1, 2),
		NewSet(2, 4, 5),
		NewSet())
	assertEquals(true, NewSet(1, 2, 4, 5).Equal(S.EltUnion()), t)
}
