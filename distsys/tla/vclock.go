package tla

import (
	"bytes"
	"encoding/gob"
	"encoding/json"
	"fmt"
	"strings"

	"github.com/benbjohnson/immutable"
)

type VClock struct {
	clock *immutable.Map[Value, Value]
}

var _ json.Marshaler = &VClock{}
var _ gob.GobEncoder = &VClock{}
var _ gob.GobDecoder = &VClock{}
var _ fmt.Stringer = &VClock{}

func (clock *VClock) ensureMap() {
	if clock.clock == nil {
		clock.clock = immutable.NewMap[Value, Value](ValueHasher{})
	}
}

func (clock VClock) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	if clock.clock != nil {
		it := clock.clock.Iterator()
		first := true
		for !it.Done() {
			key, value, _ := it.Next()
			if first {
				first = false
			} else {
				builder.WriteString(", ")
			}
			builder.WriteString(key.String())
			builder.WriteString(" -> ")
			builder.WriteString(value.String())
		}
	}
	builder.WriteString("}")
	return builder.String()
}

func (clock VClock) MarshalJSON() ([]byte, error) {
	pairs := [][]interface{}{}
	if clock.clock != nil {
		it := clock.clock.Iterator()
		for !it.Done() {
			key, value, _ := it.Next()
			pairs = append(pairs, []interface{}{
				[]interface{}{
					key.ApplyFunction(MakeNumber(1)).AsString(),
					key.ApplyFunction(MakeNumber(2)).String(),
				},
				value.AsNumber(),
			})
		}
	}
	return json.Marshal(pairs)
}

func (clock VClock) Inc(archetypeName string, self Value) VClock {
	clock.ensureMap()
	keyTuple := MakeTuple(MakeString(archetypeName), self)
	idxVal, ok := clock.clock.Get(keyTuple)
	if !ok {
		idxVal = MakeNumber(0)
	}
	return VClock{
		clock: clock.clock.Set(keyTuple, MakeNumber(idxVal.AsNumber()+1)),
	}
}

func (clock VClock) Merge(other VClock) VClock {
	if clock.clock == nil {
		return other
	} else if other.clock == nil {
		return clock
	}
	self := clock
	// optimisation: potentially swap self/other, to iterate over the smaller VClock
	if self.clock.Len() < other.clock.Len() {
		self, other = other, self
	}
	acc := self.clock
	it := other.clock.Iterator()
	for !it.Done() {
		keyVal, idx1Val, _ := it.Next()
		idx2Val, ok := acc.Get(keyVal)
		if !ok {
			idx2Val = MakeNumber(0)
		}
		if idx1Val.AsNumber() > idx2Val.AsNumber() {
			acc = acc.Set(keyVal, idx1Val)
		}
	}
	return VClock{
		clock: acc,
	}
}

func (clock VClock) Get(archetypeId string, self Value) int {
	if clock.clock == nil {
		return 0
	}
	idxVal, ok := clock.clock.Get(MakeTuple(MakeString(archetypeId), self))
	if !ok {
		return 0
	}
	return int(idxVal.AsNumber())
}

func (clock *VClock) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	var pairCount int
	if clock.clock != nil {
		pairCount = clock.clock.Len()
	}
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(pairCount)
	if err != nil {
		return nil, err
	}
	if clock.clock != nil {
		it := clock.clock.Iterator()
		for !it.Done() {
			key, value, _ := it.Next()
			// make encoded thing addressable to keep gob happy
			keyV, valueV := key, value
			err = encoder.Encode(&keyV)
			if err != nil {
				return nil, err
			}
			err = encoder.Encode(&valueV)
			if err != nil {
				return nil, err
			}
		}
	}
	return buf.Bytes(), nil
}

func (clock *VClock) GobDecode(b []byte) error {
	decoder := gob.NewDecoder(bytes.NewBuffer(b))
	var pairCount int
	err := decoder.Decode(&pairCount)
	if err != nil {
		return err
	}
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})
	for i := 0; i < pairCount; i++ {
		var key, value Value
		err = decoder.Decode(&key)
		if err != nil {
			return err
		}
		err = decoder.Decode(&value)
		if err != nil {
			return err
		}
		builder.Set(key, value)
	}
	clock.clock = builder.Map()
	return nil
}
