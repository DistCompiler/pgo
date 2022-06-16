package resources

import (
	"encoding/gob"
	"strings"
	"time"

	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func init() {
	gob.Register(&LWWSet{})
}

type LWWSet struct {
	AddSet *hashmap.HashMap[time.Time]
	RemSet *hashmap.HashMap[time.Time]
}

func (s *LWWSet) Init() CRDTValue {
	s = &LWWSet{
		AddSet: hashmap.New[time.Time](),
		RemSet: hashmap.New[time.Time](),
	}
	return s
}

func (s *LWWSet) isIn(id tla.TLAValue) bool {
	addTimeStamp, ok := s.AddSet.Get(id)
	if !ok {
		return false
	}
	remTimeStamp, ok := s.RemSet.Get(id)
	if !ok {
		return true
	}
	return !addTimeStamp.Before(remTimeStamp)
}

func (s *LWWSet) Read() tla.TLAValue {
	var result []tla.TLAValue
	for _, id := range s.AddSet.Keys {
		if s.isIn(id) {
			result = append(result, id)
		}
	}
	return tla.MakeTLASet(result...)
}

func (s *LWWSet) Write(id tla.TLAValue, value tla.TLAValue) CRDTValue {
	val := value.AsFunction()
	cmd, _ := val.Get(cmdKey)
	elem, _ := val.Get(elemKey)
	switch cmd.(tla.TLAValue).AsNumber() {
	case addOp:
		s.AddSet.Set(elem.(tla.TLAValue), time.Now())
	case remOp:
		s.RemSet.Set(elem.(tla.TLAValue), time.Now())
	}

	return s
}

func (s *LWWSet) Merge(other CRDTValue) CRDTValue {
	// log.Println("LWWSet Merge start", s, other)

	otherLWWSet := other.(*LWWSet)
	for _, id := range otherLWWSet.AddSet.Keys {
		otherTimeStamp, _ := otherLWWSet.AddSet.Get(id)
		selfTimeStamp, ok := s.AddSet.Get(id)

		// log.Println(s, id, otherTimeStamp, selfTimeStamp, ok)

		if !ok || otherTimeStamp.After(selfTimeStamp) {
			s.AddSet.Set(id, otherTimeStamp)
		}
	}

	for _, id := range otherLWWSet.RemSet.Keys {
		otherTimeStamp, _ := otherLWWSet.RemSet.Get(id)
		selfTimeStamp, ok := s.RemSet.Get(id)
		if !ok || otherTimeStamp.After(selfTimeStamp) {
			s.RemSet.Set(id, otherTimeStamp)
		}
	}

	// log.Println("LWWSet Merge end", s, other)

	return s
}

func (s *LWWSet) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	cnt := 0
	for _, id := range s.AddSet.Keys {
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
