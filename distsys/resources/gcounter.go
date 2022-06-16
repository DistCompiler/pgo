package resources

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"strings"

	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

type gcounter struct {
	*immutable.Map
}

var _ CRDTValue = new(gcounter)

func (c gcounter) Init() CRDTValue {
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

func (c gcounter) Write(id tla.TLAValue, value tla.TLAValue) CRDTValue {
	oldValue, ok := c.Get(id)
	if !ok {
		oldValue = int32(0)
	}
	newValue := oldValue.(int32) + value.AsNumber()
	return gcounter{c.Set(id, newValue)}
}

// Merge current state value with other by taking the greater of each node's partial counts.
func (c gcounter) Merge(other CRDTValue) CRDTValue {
	it := other.(gcounter).Iterator()
	for !it.Done() {
		id, val := it.Next()
		if v, ok := c.Get(id); !ok || v.(int32) < val.(int32) {
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
