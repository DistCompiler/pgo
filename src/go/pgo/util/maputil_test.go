package pgoutil

import "testing"

func TestMapsTo(t *testing.T) {
	f := func(i int) int {
		return 2*i
	}
	m := MapsTo(f, NewSet(1, 2, 3))
	assertEquals(true, m.Contains(1), t)
	assertEquals(true, m.Contains(2), t)
	assertEquals(true, m.Contains(3), t)
	assertEquals(2, m.Get(1), t)
	assertEquals(4, m.Get(2), t)
	assertEquals(6, m.Get(3), t)

	f2 := func(i int, j string) bool {
		return i > len(j)
	}
	m = MapsTo(f2, NewSet(1, 2), NewSet("a", "aa", "aaa"))
	assertEquals(6, m.Size(), t)
	assertEquals(false, m.Get(NewTuple(1, "aa")), t)
}

func TestExcept(t *testing.T) {
	m := NewMap()
	m.Put(1, 2)
	m.Put(3, 5)
	m2 := Except(m, EP(1, 3), EP(3, 4))
	assertEquals(2, m2.Size(), t)
	assertEquals(4, m2.Get(3), t)
}
