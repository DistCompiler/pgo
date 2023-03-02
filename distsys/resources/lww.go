package resources

import (
	"bytes"
	"encoding/gob"
	"strings"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

func init() {
	gob.Register(LWWSet{})
}

type LWWSet struct {
	addSet *immutable.Map[tla.Value, time.Time]
	remSet *immutable.Map[tla.Value, time.Time]
}

func (s LWWSet) Init() CRDTValue {
	return LWWSet{
		addSet: immutable.NewMap[tla.Value, time.Time](tla.ValueHasher{}),
		remSet: immutable.NewMap[tla.Value, time.Time](tla.ValueHasher{}),
	}
}

func (s LWWSet) isIn(id tla.Value) bool {
	addTimeStamp, ok := s.addSet.Get(id)
	if !ok {
		return false
	}
	remTimeStamp, ok := s.remSet.Get(id)
	if !ok {
		return true
	}
	return !addTimeStamp.Before(remTimeStamp)
}

func (s LWWSet) Read() tla.Value {
	it := s.addSet.Iterator()

	builder := immutable.NewMapBuilder[tla.Value, bool](tla.ValueHasher{})
	for !it.Done() {
		id, _, _ := it.Next()
		if s.isIn(id) {
			builder.Set(id, true)
		}
	}
	return tla.MakeSetFromMap(builder.Map())
}

func (s LWWSet) Write(id tla.Value, value tla.Value) CRDTValue {
	val := value.AsFunction()
	cmd, _ := val.Get(cmdKey)
	elem, _ := val.Get(elemKey)
	switch cmd.AsNumber() {
	case addOp:
		s.addSet = s.addSet.Set(elem, time.Now())
	case remOp:
		s.remSet = s.remSet.Set(elem, time.Now())
	}
	return s
}

func (s LWWSet) Merge(other CRDTValue) CRDTValue {
	// log.Printf("Merge start, s = %v", s)

	otherLWWSet := other.(LWWSet)
	{
		it := otherLWWSet.addSet.Iterator()
		for !it.Done() {
			id, otherVal, _ := it.Next()
			idTLA := id
			otherTimeStamp := otherVal

			selfVal, ok := s.addSet.Get(idTLA)
			if !ok {
				s.addSet = s.addSet.Set(id, otherTimeStamp)
				continue
			}

			selfTimeStamp := selfVal
			if otherTimeStamp.After(selfTimeStamp) {
				s.addSet = s.addSet.Set(id, otherTimeStamp)
			}
		}
	}
	{
		it := otherLWWSet.remSet.Iterator()
		for !it.Done() {
			id, otherVal, _ := it.Next()
			idTLA := id
			otherTimeStamp := otherVal

			selfVal, ok := s.remSet.Get(idTLA)
			if !ok {
				s.remSet.Set(id, otherTimeStamp)
			}

			selfTimeStamp := selfVal
			if otherTimeStamp.After(selfTimeStamp) {
				s.remSet.Set(id, otherTimeStamp)
			}
		}
	}

	return s
}

func (s LWWSet) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	cnt := 0

	it := s.addSet.Iterator()
	for !it.Done() {
		id, _, _ := it.Next()

		if s.isIn(id) {
			if cnt > 0 {
				builder.WriteString(", ")
			}
			builder.WriteString(id.String())
			cnt += 1
		}
	}
	builder.WriteString("}")
	return builder.String()
}

func (s LWWSet) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	{
		if err := encoder.Encode(s.addSet.Len()); err != nil {
			return nil, err
		}

		it := s.addSet.Iterator()
		for !it.Done() {
			elem, timeStamp, _ := it.Next()
			elemV := elem
			err := encoder.Encode(&elemV) // make sure encoded thing is addressable
			if err != nil {
				return nil, err
			}

			timeStampV := timeStamp
			err = encoder.Encode(timeStampV)
			if err != nil {
				return nil, err
			}
		}
	}
	{
		if err := encoder.Encode(s.remSet.Len()); err != nil {
			return nil, err
		}

		it := s.remSet.Iterator()
		for !it.Done() {
			elem, timeStamp, _ := it.Next()
			elemV := elem
			err := encoder.Encode(&elemV) // make sure encoded thing is addressable
			if err != nil {
				return nil, err
			}

			timeStampV := timeStamp
			err = encoder.Encode(timeStampV)
			if err != nil {
				return nil, err
			}
		}
	}
	return buf.Bytes(), nil

}

func (s *LWWSet) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)

	{
		var addSetLen int
		err := decoder.Decode(&addSetLen)
		if err != nil {
			return err
		}

		builder := immutable.NewMapBuilder[tla.Value, time.Time](tla.ValueHasher{})
		for i := 0; i < addSetLen; i++ {
			var elem tla.Value
			err := decoder.Decode(&elem)
			if err != nil {
				return err
			}

			var timeStamp time.Time
			err = decoder.Decode(&timeStamp)
			if err != nil {
				return err
			}
			builder.Set(elem, timeStamp)
		}
		s.addSet = builder.Map()
	}
	{
		var remSetLen int
		err := decoder.Decode(&remSetLen)
		if err != nil {
			return err
		}

		builder := immutable.NewMapBuilder[tla.Value, time.Time](tla.ValueHasher{})
		for i := 0; i < remSetLen; i++ {
			var elem tla.Value
			err := decoder.Decode(&elem)
			if err != nil {
				return err
			}

			var timeStamp time.Time
			err = decoder.Decode(&timeStamp)
			if err != nil {
				return err
			}
			builder.Set(elem, timeStamp)
		}
		s.remSet = builder.Map()
	}

	return nil
}
