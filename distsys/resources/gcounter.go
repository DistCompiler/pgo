package resources

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"io"
	"strings"
)

type counters struct {
	*immutable.Map
}

var _ crdtValue = new(counters)

func MakeGCounter() crdtValue {
	return counters{immutable.NewMap(tla.TLAValueHasher{})}
}

func (s counters) Read() tla.TLAValue {
	var value int32 = 0
	it := s.Iterator()
	for !it.Done() {
		_, v := it.Next()
		value += v.(int32)
	}
	return tla.MakeTLANumber(value)
}

func (s counters) Write(id tla.TLAValue, value tla.TLAValue) crdtValue {
	return counters{s.Set(id, value.AsNumber())}
}

// merge current state value with other by taking the greater of each node's partial counts.
func (s counters) Merge(other crdtValue) crdtValue {
	it := other.(counters).Iterator()
	for !it.Done() {
		id, val := it.Next()
		if v, ok := s.Get(id); !ok || v.(int32) > val.(int32) {
			s = counters{s.Set(id, val)}
		}
	}
	return s
}

func (s counters) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := s.Iterator()
	for !it.Done() {
		k, v := it.Next()
		pair := KeyVal{K: k.(tla.TLAValue), V: v.(int32)}
		err := encoder.Encode(&pair)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

type KeyVal struct {
	K tla.TLAValue
	V int32
}

func (s *counters) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	b := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for {
		var pair KeyVal
		err := decoder.Decode(&pair)
		if err != nil {
			if errors.Is(err, io.EOF) {
				s.Map = b.Map()
				return nil
			} else {
				return err
			}
		}
		b.Set(pair.K, pair.V)
	}
}

func (s counters) String() string {
	it := s.Iterator()
	b := strings.Builder{}
	b.WriteString("map[")
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
	b.WriteString("]")
	return b.String()
}

func init(){
	gob.Register(counters{})
}