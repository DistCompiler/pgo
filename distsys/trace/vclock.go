package trace

import (
	"encoding/json"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

type VClock struct {
	clock *immutable.Map
}

var _ json.Marshaler = &VClock{}

func (clock *VClock) ensureMap() {
	if clock.clock == nil {
		clock.clock = immutable.NewMap(tla.TLAValueHasher{})
	}
}

func (clock VClock) MarshalJSON() ([]byte, error) {
	pairs := [][]interface{}{}
	if clock.clock != nil {
		it := clock.clock.Iterator()
		for !it.Done() {
			key, value := it.Next()
			pairs = append(pairs, []interface{}{
				[]interface{}{
					key.(tla.TLAValue).ApplyFunction(tla.MakeTLANumber(1)).AsString(),
					key.(tla.TLAValue).ApplyFunction(tla.MakeTLANumber(2)).String(),
				},
				value.(tla.TLAValue).AsNumber(),
			})
		}
	}
	return json.Marshal(pairs)
}

func (clock VClock) Inc(archetypeName string, self tla.TLAValue) VClock {
	clock.ensureMap()
	keyTuple := tla.MakeTLATuple(tla.MakeTLAString(archetypeName), self)
	idxVal, ok := clock.clock.Get(keyTuple)
	if !ok {
		idxVal = tla.MakeTLANumber(0)
	}
	return VClock{
		clock: clock.clock.Set(keyTuple, tla.MakeTLANumber(idxVal.(tla.TLAValue).AsNumber()+1)),
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
			idx2Val = tla.MakeTLANumber(0)
		}
		if idx1Val.(tla.TLAValue).AsNumber() > idx2Val.(tla.TLAValue).AsNumber() {
			acc = acc.Set(keyVal, idx1Val)
		}
	}
	return VClock{
		clock: acc,
	}
}

func (clock VClock) Get(archetypeId string, self tla.TLAValue) int {
	if clock.clock == nil {
		return 0
	}
	idxVal, ok := clock.clock.Get(tla.MakeTLATuple(tla.MakeTLAString(archetypeId), self))
	if !ok {
		return 0
	}
	return int(idxVal.(tla.TLAValue).AsNumber())
}
