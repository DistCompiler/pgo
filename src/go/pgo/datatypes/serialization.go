package datatypes

import (
	"bytes"
	"encoding/gob"
)

func GobInit() {
	gob.Register(&mp{})
	gob.Register(&KVPair{})
	gob.Register(&pair{})
	gob.Register(&set{})
	gob.Register(&tuple{})
	gob.Register(&struct{}{})
}

func (m *mp) GobEncode() ([]byte, error) {
	buffer := bytes.Buffer{}
	encoder := gob.NewEncoder(&buffer)

	err := encoder.Encode(m.Size())
	if err != nil {
		return nil, err
	}

	iter := m.Iterator()
	for iter.Next() {
		key := iter.Key()
		val := iter.Value()
		err = encoder.Encode(&key)
		if err != nil {
			return nil, err
		}
		err = encoder.Encode(&val)
		if err != nil {
			return nil, err
		}
	}

	return buffer.Bytes(), nil
}

func (m *mp) GobDecode(buffer []byte) error {
	decoder := gob.NewDecoder(bytes.NewReader(buffer))

	tmp := NewMap()
	size := int(0)
	err := decoder.Decode(&size)
	if err != nil {
		return err
	}

	for i := 0; i < size; i += 1 {
		var key, val interface{}
		err = decoder.Decode(&key)
		if err != nil {
			return err
		}
		err = decoder.Decode(&val)
		if err != nil {
			return err
		}
		tmp.Put(key, val)
	}

	*m = *(tmp).(*mp)

	return nil
}

func (s *set) GobEncode() ([]byte, error) {
	buf, err := s.m.(*mp).GobEncode()
	return buf, err
}

func (s *set) GobDecode(buffer []byte) error {
	m := mp{}
	err := (&m).GobDecode(buffer)
	if err != nil {
		return err
	}
	*s = set{&m}
	return nil
}
