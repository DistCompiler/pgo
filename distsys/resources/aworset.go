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

var cmdKey = tla.MakeString("cmd")
var elemKey = tla.MakeString("elem")

type AWORSet struct {
	id     tla.Value
	addMap *immutable.Map[tla.Value, vclock]
	remMap *immutable.Map[tla.Value, vclock]
}

var _ CRDTValue = new(AWORSet)

// vclock is a vector clock implemented with GCounter
type vclock = GCounter

const (
	LT = -1 // less than
	EQ = 0  // equal
	GT = 1  // greater
	CC = 2  // concurrent
)

func MakeVClock() vclock {
	return GCounter{}.Init().(vclock)
}

func (vc vclock) inc(id tla.Value) vclock {
	return vc.Write(id, tla.MakeNumber(1)).(vclock)
}

func (vc vclock) merge(other vclock) vclock {
	return vc.Merge(other).(vclock)
}

func (vc vclock) compare(other vclock) int {
	i1 := vc.Iterator()
	i2 := other.Iterator()
	kB := immutable.NewMapBuilder[tla.Value, bool](tla.ValueHasher{})
	for !i1.Done() || !i2.Done() {
		elem1, _, _ := i1.Next()
		elem2, _, _ := i2.Next()
		kB.Set(elem1, true)
		kB.Set(elem2, true)
	}

	res := EQ
	i := kB.Iterator()
	for !i.Done() {
		k, _, _ := i.Next()
		v1 := vc.getOrDefault(k)
		v2 := other.getOrDefault(k)
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

func (vc vclock) getOrDefault(id tla.Value) int32 {
	if v, ok := vc.Get(id); !ok {
		return 0
	} else {
		return v
	}
}

func (s AWORSet) Init() CRDTValue {
	return AWORSet{
		addMap: immutable.NewMap[tla.Value, vclock](tla.ValueHasher{}),
		remMap: immutable.NewMap[tla.Value, vclock](tla.ValueHasher{}),
	}
}

// Read returns the current value of the set.
// An element is in the set if it is in the add map, and its clock is less than
// that in remove map (if existing).
func (s AWORSet) Read() tla.Value {
	set := make([]tla.Value, 0)
	i := s.addMap.Iterator()
	for !i.Done() {
		elem, addVC, _ := i.Next()
		if remVC, remOK := s.remMap.Get(elem); !remOK || addVC.compare(remVC) != LT {
			set = append(set, elem)
		}
	}
	return tla.MakeSet(set...)
}

// Write performs the command given by value
// If add: add the element to the add map, incremeting the clock for the node
// If remove: add the elemnt to the remove map, incremeting the clock for the node
func (s AWORSet) Write(id tla.Value, value tla.Value) CRDTValue {
	val := value.AsFunction()
	cmd, _ := val.Get(cmdKey)
	elem, _ := val.Get(elemKey)
	switch cmd.AsNumber() {
	case addOp:
		if addVC, addOk := s.addMap.Get(elem); addOk {
			s.addMap = s.addMap.Set(elem, addVC.inc(id))
			s.remMap = s.remMap.Delete(elem)
		} else if remVC, remOk := s.remMap.Get(elem); remOk {
			s.addMap = s.addMap.Set(elem, remVC.inc(id))
			s.remMap = s.remMap.Delete(elem)
		} else {
			s.addMap = s.addMap.Set(elem, MakeVClock().inc(id))
		}
	case remOp:
		if addVC, addOk := s.addMap.Get(elem); addOk {
			s.remMap = s.remMap.Set(elem, addVC.inc(id))
			s.addMap = s.addMap.Delete(elem)
		} else if remVC, remOk := s.remMap.Get(elem); remOk {
			s.remMap = s.remMap.Set(elem, remVC.inc(id))
			s.addMap = s.addMap.Delete(elem)
		} else {
			s.remMap = s.remMap.Set(elem, MakeVClock().inc(id))
		}
	}
	return s
}

// Merge merges this set and that set.
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

	addB := immutable.NewMapBuilder[tla.Value, vclock](tla.ValueHasher{})
	i := addK.Iterator()
	for !i.Done() {
		elem, addVC, _ := i.Next()
		if remVC, remOk := remK.Get(elem); !remOk || addVC.compare(remVC) != LT {
			addB.Set(elem, addVC)
		}
	}

	remB := immutable.NewMapBuilder[tla.Value, vclock](tla.ValueHasher{})
	i = remK.Iterator()
	for !i.Done() {
		elem, remVC, _ := i.Next()
		if addVC, addOk := addK.Get(elem); !addOk || addVC.compare(remVC) == LT {
			remB.Set(elem, remVC)
		}
	}
	return AWORSet{
		addMap: addB.Map(),
		remMap: remB.Map(),
	}
}

func mergeKeys(a *immutable.Map[tla.Value, vclock], b *immutable.Map[tla.Value, vclock]) *immutable.Map[tla.Value, vclock] {
	acc := a
	i := b.Iterator()
	for !i.Done() {
		elem, bVC, _ := i.Next()
		if accVC, accOk := acc.Get(elem); accOk {
			acc = acc.Set(elem, accVC.merge(bVC))
		} else {
			acc = acc.Set(elem, bVC)
		}
	}
	return acc
}

type AWORSetKeyVal struct {
	K tla.Value
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
		k, v, _ := it.Next()
		maps.AddMap = append(maps.AddMap, AWORSetKeyVal{K: k, V: v})
	}
	it = s.remMap.Iterator()
	for !it.Done() {
		k, v, _ := it.Next()
		maps.RemMap = append(maps.RemMap, AWORSetKeyVal{K: k, V: v})
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
	addMap := immutable.NewMapBuilder[tla.Value, vclock](tla.ValueHasher{})
	remMap := immutable.NewMapBuilder[tla.Value, vclock](tla.ValueHasher{})
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
		k, v, _ := it.Next()
		b.WriteString(k.String())
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
		k, v, _ := it.Next()
		b.WriteString(k.String())
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
