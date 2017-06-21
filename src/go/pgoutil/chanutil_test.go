package pgoutil

import "testing"

func TestNewChan(t *testing.T) {
	ch := NewChan(1, 2, 3)
	assertEquals(1, <-ch, t)
	assertEquals(2, <-ch, t)
	assertEquals(3, <-ch, t)

	intSlice := make([]interface{}, 1000)
	for i := 1000; i > 0; i-- {
		intSlice[1000 - i] = i
	}
	ch = NewChan(intSlice...)
	for i := 0; i < 1000; i++ {
		assertEquals(1000 - i, <-ch, t)
	}
}
