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

type gcounter struct {
	*immutable.Map
}

var _ crdtValue = new(gcounter)

func MakeGCounter() crdtValue {
	return gcounter{immutable.NewMap(tla.TLAValueHasher{})}
}

func (c gcounter) Read() tla.TLAValue {
	var value int32 = 0
	it := c.Iterator()
	for !it.Done() {
		_, v := it.Next()
		value += v.(int32)
	}
	return tla.MakeTLANumber(value)
}

func (c gcounter) Write(id tla.TLAValue, value tla.TLAValue) crdtValue {
	return gcounter{c.Set(id, value.AsNumber())}
}

// merge current state value with other by taking the greater of each node's partial counts.
func (c gcounter) Merge(other crdtValue) crdtValue {
	it := other.(gcounter).Iterator()
	for !it.Done() {
		id, val := it.Next()
		if v, ok := c.Get(id); !ok || v.(int32) > val.(int32) {
			c = gcounter{c.Set(id, val)}
		}
	}
	return c
}

type GCounterKeyVal struct {
	K tla.TLAValue
	V int32
}

func (c gcounter) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := c.Iterator()
	for !it.Done() {
		k, v := it.Next()
		pair := GCounterKeyVal{K: k.(tla.TLAValue), V: v.(int32)}
		err := encoder.Encode(&pair)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (c *gcounter) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	b := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for {
		var pair GCounterKeyVal
		err := decoder.Decode(&pair)
		if err != nil {
			if errors.Is(err, io.EOF) {
				c.Map = b.Map()
				return nil
			} else {
				return err
			}
		}
		b.Set(pair.K, pair.V)
	}
}

func (c gcounter) String() string {
	it := c.Iterator()
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

func init() {
	gob.Register(gcounter{})
}
