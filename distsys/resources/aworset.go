package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"strings"

	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

const (
	addOp = 1 // Add operation
	remOp = 2 // Remove operation
)

var cmdKey = tla.MakeTLAString("cmd")
var elemKey = tla.MakeTLAString("elem")

type AWORSet struct {
	id     tla.TLAValue
	addMap *immutable.Map
	remMap *immutable.Map
}

var _ CRDTValue = new(AWORSet)

// vclock is a vector clock implemented with GCounter
type vclock = gcounter

const (
	LT = -1 // less than
	EQ = 0  // equal
	GT = 1  // greater
	CC = 2  // concurrent
)

func MakeVClock() vclock {
	return gcounter{}.Init().(vclock)
}

func (vc vclock) inc(id tla.TLAValue) vclock {
	return vc.Write(id, tla.MakeTLANumber(1)).(vclock)
}

func (vc vclock) merge(other vclock) vclock {
	return vc.Merge(other).(vclock)
}

func (vc vclock) compare(other vclock) int {
	i1 := vc.Iterator()
	i2 := other.Iterator()
	kB := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for !i1.Done() || !i2.Done() {
		elem1, _ := i1.Next()
		elem2, _ := i2.Next()
		if elem1 != nil {
			kB.Set(elem1, true)
		}
		if elem2 != nil {
			kB.Set(elem2, true)
		}
	}

	res := EQ
	i := kB.Iterator()
	for !i.Done() {
		k, _ := i.Next()
		v1 := vc.getOrDefault(k.(tla.TLAValue))
		v2 := other.getOrDefault(k.(tla.TLAValue))
		if res == EQ && v1 > v2 {
			res = GT
		} else if res == EQ && v1 < v2 {
			res = LT
		} else if res == LT && v1 > v2 {
			res = CC
		} else if res == GT && v1 < v2 {
			res = CC
		}
	}
	return res
}

func (vc vclock) getOrDefault(id tla.TLAValue) int32 {
	if v, ok := vc.Get(id); !ok {
		return 0
	} else {
		return v.(int32)
	}
}

func (s AWORSet) Init() CRDTValue {
	return AWORSet{
		addMap: immutable.NewMap(tla.TLAValueHasher{}),
		remMap: immutable.NewMap(tla.TLAValueHasher{}),
	}
}

// Read returns the current value of the set.
// An element is in the set if it is in the add map, and its clock is less than
// that in remove map (if existing).
func (s AWORSet) Read() tla.TLAValue {
	set := make([]tla.TLAValue, 0)
	i := s.addMap.Iterator()
	for !i.Done() {
		elem, addVC := i.Next()
		if remVC, remOK := s.remMap.Get(elem.(tla.TLAValue)); !remOK || addVC.(vclock).compare(remVC.(vclock)) != LT {
			set = append(set, elem.(tla.TLAValue))
		}
	}
	return tla.MakeTLASet(set...)
}

// Write performs the command given by value
// If add: add the element to the add map, incremeting the clock for the node
// If remove: add the elemnt to the remove map, incremeting the clock for the node
func (s AWORSet) Write(id tla.TLAValue, value tla.TLAValue) CRDTValue {
	val := value.AsFunction()
	cmd, _ := val.Get(cmdKey)
	elem, _ := val.Get(elemKey)
	switch cmd.(tla.TLAValue).AsNumber() {
	case addOp:
		if addVC, addOk := s.addMap.Get(elem); addOk {
			s.addMap = s.addMap.Set(elem, addVC.(vclock).inc(id))
			s.remMap = s.remMap.Delete(elem)
		} else if remVC, remOk := s.remMap.Get(elem); remOk {
			s.addMap = s.addMap.Set(elem, remVC.(vclock).inc(id))
			s.remMap = s.remMap.Delete(elem)
		} else {
			s.addMap = s.addMap.Set(elem, MakeVClock().inc(id))
		}
	case remOp:
		if addVC, addOk := s.addMap.Get(elem); addOk {
			s.remMap = s.remMap.Set(elem, addVC.(vclock).inc(id))
			s.addMap = s.addMap.Delete(elem)
		} else if remVC, remOk := s.remMap.Get(elem); remOk {
			s.remMap = s.remMap.Set(elem, remVC.(vclock).inc(id))
			s.addMap = s.addMap.Delete(elem)
		} else {
			s.remMap = s.remMap.Set(elem, MakeVClock().inc(id))
		}
	}
	return s
}

// merges this set and that set.
// 1. Merge the two add maps, merging the vector clocks if an element is present in both --> addK.
// 2. Merge the two rem maps, merging the vector clocks if an element is present in both --> remK.
// 3. From each element in merged addK, keep the element if remK does not have the same element
// with a greater vector timestamp.
// 4. From each element in merged remK, keep the element if addK does not have the same element
// with a larger, equal, or concurrent vector timestamp.
func (s AWORSet) Merge(other CRDTValue) CRDTValue {
	thisAdd := s.addMap
	thatAdd := other.(AWORSet).addMap
	thisRem := s.remMap
	thatRem := other.(AWORSet).remMap

	addK := mergeKeys(thisAdd, thatAdd)
	remK := mergeKeys(thisRem, thatRem)

	addB := immutable.NewMapBuilder(tla.TLAValueHasher{})
	i := addK.Iterator()
	for !i.Done() {
		elem, addVC := i.Next()
		if remVC, remOk := remK.Get(elem); !remOk || addVC.(vclock).compare(remVC.(vclock)) != LT {
			addB.Set(elem, addVC)
		}
	}

	remB := immutable.NewMapBuilder(tla.TLAValueHasher{})
	i = remK.Iterator()
	for !i.Done() {
		elem, remVC := i.Next()
		if addVC, addOk := addK.Get(elem); !addOk || addVC.(vclock).compare(remVC.(vclock)) == LT {
			remB.Set(elem, remVC)
		}
	}
	return AWORSet{
		addMap: addB.Map(),
		remMap: remB.Map(),
	}
}

func mergeKeys(a *immutable.Map, b *immutable.Map) *immutable.Map {
	acc := a
	i := b.Iterator()
	for !i.Done() {
		elem, bVC := i.Next()
		if accVC, accOk := acc.Get(elem); accOk {
			acc = acc.Set(elem, accVC.(vclock).merge(bVC.(vclock)))
		} else {
			acc = acc.Set(elem, bVC)
		}
	}
	return acc
}

type AWORSetKeyVal struct {
	K tla.TLAValue
	V vclock
}

type AddRemMaps struct {
	AddMap []AWORSetKeyVal
	RemMap []AWORSetKeyVal
}

func (s AWORSet) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	maps := AddRemMaps{}
	it := s.addMap.Iterator()
	for !it.Done() {
		k, v := it.Next()
		maps.AddMap = append(maps.AddMap, AWORSetKeyVal{K: k.(tla.TLAValue), V: v.(vclock)})
	}
	it = s.remMap.Iterator()
	for !it.Done() {
		k, v := it.Next()
		maps.RemMap = append(maps.RemMap, AWORSetKeyVal{K: k.(tla.TLAValue), V: v.(vclock)})
	}
	err := encoder.Encode(&maps)
	if err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func (s *AWORSet) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	var maps AddRemMaps
	if err := decoder.Decode(&maps); err != nil {
		return err
	}
	addMap := immutable.NewMapBuilder(tla.TLAValueHasher{})
	remMap := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for _, kv := range maps.AddMap {
		addMap.Set(kv.K, kv.V)
	}
	for _, kv := range maps.RemMap {
		remMap.Set(kv.K, kv.V)
	}
	s.addMap = addMap.Map()
	s.remMap = remMap.Map()
	return nil
}

func (s AWORSet) String() string {
	b := strings.Builder{}

	it := s.addMap.Iterator()
	b.WriteString("addMap[")
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			b.WriteString(" ")
		}
		k, v := it.Next()
		b.WriteString(k.(tla.TLAValue).String())
		b.WriteString(":")
		b.WriteString(fmt.Sprint(v))
	}
	b.WriteString("] ")

	it = s.remMap.Iterator()
	b.WriteString("remMap[")
	first = true
	for !it.Done() {
		if first {
			first = false
		} else {
			b.WriteString(" ")
		}
		k, v := it.Next()
		b.WriteString(k.(tla.TLAValue).String())
		b.WriteString(":")
		b.WriteString(fmt.Sprint(v))
	}
	b.WriteString("]")
	return b.String()
}

func init() {
	gob.Register(AWORSet{})
	gob.Register(vclock{})
}
