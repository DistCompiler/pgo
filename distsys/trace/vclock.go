package trace

import (
	"bytes"
	"encoding/gob"
	"encoding/json"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"strings"
)

type VClock struct {
	clock *immutable.Map
}

var _ json.Marshaler = &VClock{}
var _ gob.GobEncoder = &VClock{}
var _ gob.GobDecoder = &VClock{}
var _ fmt.Stringer = &VClock{}

func (clock *VClock) ensureMap() {
	if clock.clock == nil {
		clock.clock = immutable.NewMap(tla.ValueHasher{})
	}
}

func (clock VClock) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	if clock.clock != nil {
		it := clock.clock.Iterator()
		first := true
		for !it.Done() {
			key, value := it.Next()
			if first {
				first = false
			} else {
				builder.WriteString(", ")
			}
			builder.WriteString(key.(tla.Value).String())
			builder.WriteString(" -> ")
			builder.WriteString(value.(tla.Value).String())
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
			key, value := it.Next()
			pairs = append(pairs, []interface{}{
				[]interface{}{
					key.(tla.Value).ApplyFunction(tla.MakeNumber(1)).AsString(),
					key.(tla.Value).ApplyFunction(tla.MakeNumber(2)).String(),
				},
				value.(tla.Value).AsNumber(),
			})
		}
	}
	return json.Marshal(pairs)
}

func (clock VClock) Inc(archetypeName string, self tla.Value) VClock {
	clock.ensureMap()
	keyTuple := tla.MakeTuple(tla.MakeString(archetypeName), self)
	idxVal, ok := clock.clock.Get(keyTuple)
	if !ok {
		idxVal = tla.MakeNumber(0)
	}
	return VClock{
		clock: clock.clock.Set(keyTuple, tla.MakeNumber(idxVal.(tla.Value).AsNumber()+1)),
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
		keyVal, idx1Val := it.Next()
		idx2Val, ok := acc.Get(keyVal)
		if !ok {
			idx2Val = tla.MakeNumber(0)
		}
		if idx1Val.(tla.Value).AsNumber() > idx2Val.(tla.Value).AsNumber() {
			acc = acc.Set(keyVal, idx1Val)
		}
	}
	return VClock{
		clock: acc,
	}
}

func (clock VClock) Get(archetypeId string, self tla.Value) int {
	if clock.clock == nil {
		return 0
	}
	idxVal, ok := clock.clock.Get(tla.MakeTuple(tla.MakeString(archetypeId), self))
	if !ok {
		return 0
	}
	return int(idxVal.(tla.Value).AsNumber())
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
			key, value := it.Next()
			// make encoded thing addressable to keep gob happy
			keyV, valueV := key.(tla.Value), value.(tla.Value)
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

func (vclock *VClock) GobDecode(b []byte) error {
	decoder := gob.NewDecoder(bytes.NewBuffer(b))
	var pairCount int
	err := decoder.Decode(&pairCount)
	if err != nil {
		return err
	}
	builder := immutable.NewMapBuilder(tla.ValueHasher{})
	for i := 0; i < pairCount; i++ {
		var key, value tla.Value
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
	vclock.clock = builder.Map()
	return nil
}
