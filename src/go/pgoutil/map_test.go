package pgoutil

import "testing"

func TestComparator(t *testing.T) {
	assertEquals(1, comp(true, false), t)
	assertEquals(-1, comp(false, true), t)
	assertEquals(0, comp(true, true), t)
	assertEquals(0, comp(false, false), t)

	assertEquals(1, comp(2000000, -2000000), t)
	assertEquals(0, comp(135.5, 135.5), t)

	assertEquals(-1, comp("", "a"), t)
	assertEquals(1, comp("a", ""), t)
	assertEquals(0, comp("asdf", "asdf"), t)
	assertEquals(-1, comp("aaaa", "aaab"), t)
	assertEquals(-1, comp("aaaa", "aaaaa"), t)
	assertEquals(1, comp("aaaaa", "aaaa"), t)

	assertEquals(1, comp(NewTuple(1, 2), NewTuple(1)), t)
	assertEquals(-1, comp(NewTuple(1), NewTuple(1, 2)), t)
	assertEquals(0, comp(NewTuple(1, 3, 5), NewTuple(1, 3, 5)), t)

	x := "asdf"
	y := "asdf"
	assertEquals(0, comp(&x, &y), t)
	x = "aaaa"
	y = "aaab"
	a := &x
	b := &y
	assertEquals(-1, comp(&a, &b), t)
	y = "aaaaa"
	assertEquals(-1, comp(&a, &b), t)

	p := struct{A, B interface{}}{1, 3}
	q := struct{A, B interface{}}{2, 2}
	assertEquals(-1, comp(p, q), t)
}

func TestNewMap(t *testing.T) {
	a := NewMap()
	assertEquals(true, a.IsEmpty(), t)
	assertEquals(0, a.Size(), t)
}

func TestAddRemoveMap(t *testing.T) {
	m := NewMap()
	m.Put("s", 5)
	assertEquals(false, m.IsEmpty(), t)
	assertEquals(1, m.Size(), t)
	assertEquals(true, m.Contains("s"), t)
	assertEquals(5, m.Get("s"), t)

	m.Remove("t")
	assertEquals(1, m.Size(), t)
	assertEquals(nil, m.Get("t"), t)

	m.Put("s", 6)
	assertEquals(1, m.Size(), t)
	assertEquals(6, m.Get("s"), t)

	m.Put("sa", 8)
	m.Put("a", 2)
	m.Put("b", 5)
	assertEquals(4, m.Size(), t)

	m.Remove("a")
	assertEquals(3, m.Size(), t)
	assertEquals(false, m.Contains("a"), t)
	assertEquals(nil, m.Get("a"), t)

	m.Clear()
	assertEquals(0, m.Size(), t)
	assertEquals(nil, m.Get("s"), t)

	slice := []int{1, 2, 3}
	m.Put(slice, 1)
	slice = append(slice, 4)
	m.Put(slice, 2)
	assertEquals(2, m.Size(), t)
	assertEquals(1, m.Get([]int{1, 2, 3}), t)
	assertEquals(2, m.Get(slice), t)
}

func TestIteration(t *testing.T) {
	m := NewMap()
	for i := 0; i < 10000; i++ {
		m.Put(i, i*2)
	}
	assertEquals(10000, m.Size(), t)

	keys := m.Keys()
	for i := 0; i < 10000; i++ {
		j := <-keys
		assertEquals(i, j, t)
	}

	vals := m.Values()
	for i := 0; i < 10000; i++ {
		j := <-vals
		assertEquals(i*2, j, t)
	}

	kvpairs := m.Iter()
	for i := 0; i < 10000; i++ {
		j := <-kvpairs
		assertEquals(i, j.Key, t)
		assertEquals(i*2, j.Val, t)
	}
}

func TestDomain(t *testing.T) {
	m := NewMap()
	m.Put(1, 3)
	m.Put(2, 4)
	m.Put(3, 5)
	s := m.Domain()
	assertSetEqual(NewSet(1, 2, 3), s, t)
}
