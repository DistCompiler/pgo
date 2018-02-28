package datatypes

import (
	"bytes"
	"encoding/gob"
	"testing"
)

func TestMap(t *testing.T) {
	m := NewMap()
	m.Put("s", 5)
	m.Put("t", 10)

	buffer := bytes.Buffer{}

	encoder := gob.NewEncoder(&buffer)
	err := encoder.Encode(&m)
	assertEquals(nil, err, t)

	var n Map
	decoder := gob.NewDecoder(&buffer)
	err = decoder.Decode(&n)
	assertEquals(nil, err, t)

	assertEquals(false, n.IsEmpty(), t)
	assertEquals(2, n.Size(), t)
	assertEquals(true, n.Contains("s"), t)
	assertEquals(5, n.Get("s"), t)
	assertEquals(true, n.Contains("t"), t)
	assertEquals(10, n.Get("t"), t)
}
