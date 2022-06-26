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
	addSet *immutable.Map
	remSet *immutable.Map
}

func (s LWWSet) Init() CRDTValue {
	return LWWSet{
		addSet: immutable.NewMap(tla.TLAValueHasher{}),
		remSet: immutable.NewMap(tla.TLAValueHasher{}),
	}
}

func (s LWWSet) isIn(id tla.TLAValue) bool {
	addTimeStamp, ok := s.addSet.Get(id)
	if !ok {
		return false
	}
	remTimeStamp, ok := s.remSet.Get(id)
	if !ok {
		return true
	}
	return !addTimeStamp.(time.Time).Before(remTimeStamp.(time.Time))
}

func (s LWWSet) Read() tla.TLAValue {
	// start := time.Now()
	// defer func() {
	// 	elapsed := time.Since(start)
	// 	log.Printf("LWW Read took %v", elapsed)
	// }()

	it := s.addSet.Iterator()

	builder := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for !it.Done() {
		id, _ := it.Next()
		idTLA := id.(tla.TLAValue)
		if s.isIn(idTLA) {
			builder.Set(id, true)
		}
	}
	return tla.MakeTLASetFromMap(builder.Map())
}

func (s LWWSet) Write(id tla.TLAValue, value tla.TLAValue) CRDTValue {
	val := value.AsFunction()
	cmd, _ := val.Get(cmdKey)
	elem, _ := val.Get(elemKey)
	switch cmd.(tla.TLAValue).AsNumber() {
	case addOp:
		s.addSet = s.addSet.Set(elem.(tla.TLAValue), time.Now())
	case remOp:
		s.remSet = s.remSet.Set(elem.(tla.TLAValue), time.Now())
	}
	return s
}

func (s LWWSet) Merge(other CRDTValue) CRDTValue {
	// log.Printf("Merge start, s = %v", s)

	otherLWWSet := other.(LWWSet)
	{
		it := otherLWWSet.addSet.Iterator()
		for !it.Done() {
			id, otherVal := it.Next()
			idTLA := id.(tla.TLAValue)
			otherTimeStamp := otherVal.(time.Time)

			selfVal, ok := s.addSet.Get(idTLA)
			if !ok {
				s.addSet = s.addSet.Set(id, otherTimeStamp)
				continue
			}

			selfTimeStamp := selfVal.(time.Time)
			if otherTimeStamp.After(selfTimeStamp) {
				s.addSet = s.addSet.Set(id, otherTimeStamp)
			}
		}
	}
	{
		it := otherLWWSet.remSet.Iterator()
		for !it.Done() {
			id, otherVal := it.Next()
			idTLA := id.(tla.TLAValue)
			otherTimeStamp := otherVal.(time.Time)

			selfVal, ok := s.remSet.Get(idTLA)
			if !ok {
				s.remSet.Set(id, otherTimeStamp)
			}

			selfTimeStamp := selfVal.(time.Time)
			if otherTimeStamp.After(selfTimeStamp) {
				s.remSet.Set(id, otherTimeStamp)
			}
		}
	}

	// log.Println("LWWSet Merge end", s, other)

	return s
}

func (s LWWSet) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	cnt := 0

	it := s.addSet.Iterator()
	for !it.Done() {
		id, _ := it.Next()
		idTLA := id.(tla.TLAValue)

		if s.isIn(idTLA) {
			if cnt > 0 {
				builder.WriteString(", ")
			}
			builder.WriteString(idTLA.String())
			cnt += 1
		}
	}
	builder.WriteString("}")
	return builder.String()
}

func (s LWWSet) GobEncode() ([]byte, error) {
	// start := time.Now()
	// defer func() {
	// 	elapsed := time.Since(start)
	// 	log.Printf("GobEncode took %v", elapsed)
	// }()

	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	{
		if err := encoder.Encode(s.addSet.Len()); err != nil {
			return nil, err
		}

		it := s.addSet.Iterator()
		for !it.Done() {
			elem, timeStamp := it.Next()
			elemV := elem.(tla.TLAValue)
			err := encoder.Encode(&elemV) // make sure encoded thing is addressable
			if err != nil {
				return nil, err
			}

			timeStampV := timeStamp.(time.Time)
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
			elem, timeStamp := it.Next()
			elemV := elem.(tla.TLAValue)
			err := encoder.Encode(&elemV) // make sure encoded thing is addressable
			if err != nil {
				return nil, err
			}

			timeStampV := timeStamp.(time.Time)
			err = encoder.Encode(timeStampV)
			if err != nil {
				return nil, err
			}
		}
	}
	return buf.Bytes(), nil

}

func (s *LWWSet) GobDecode(input []byte) error {
	// start := time.Now()
	// defer func() {
	// 	elapsed := time.Since(start)
	// 	log.Printf("GobDecode took %v", elapsed)
	// }()

	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)

	{
		var addSetLen int
		err := decoder.Decode(&addSetLen)
		if err != nil {
			return err
		}

		builder := immutable.NewMapBuilder(tla.TLAValueHasher{})
		for i := 0; i < addSetLen; i++ {
			var elem tla.TLAValue
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

		builder := immutable.NewMapBuilder(tla.TLAValueHasher{})
		for i := 0; i < remSetLen; i++ {
			var elem tla.TLAValue
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
