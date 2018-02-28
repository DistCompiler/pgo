package datatypes

import (
	"bytes"
	"encoding/gob"
)

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
	tmp := NewMap()

	decoder := gob.NewDecoder(bytes.NewReader(buffer))

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
