package distsys

import (
	"bytes"
	"encoding/binary"
	"encoding/gob"
	"errors"
	"fmt"
	"github.com/benbjohnson/immutable"
	"hash/fnv"
	"io"
	"strconv"
	"strings"
)

var TLATypeError = errors.New("TLA+ type error")

func init() {
	gob.Register(tlaValueBool(false))
	gob.Register(tlaValueNumber(0))
	gob.Register(tlaValueString(""))
	gob.Register(&tlaValueSet{})
	gob.Register(&tlaValueTuple{})
}

type TLAValue struct {
	data tlaValueImpl
}

var _ fmt.Stringer = TLAValue{}

func (v TLAValue) Hash() uint32 {
	if v.data == nil {
		return 0
	} else {
		return v.data.Hash()
	}
}

func (v TLAValue) Equal(other TLAValue) bool {
	if v.data == nil && other.data == nil {
		return true
	} else if v.data == nil || other.data == nil {
		return false
	} else {
		return v.data.Equal(other)
	}
}

func (v TLAValue) String() string {
	if v.data == nil {
		return "defaultInitValue"
	} else {
		return v.data.String()
	}
}

func (v *TLAValue) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	return decoder.Decode(&v.data)
}

func (v *TLAValue) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&v.data)
	return buf.Bytes(), err
}

func (v TLAValue) AsBool() bool {
	switch data := v.data.(type) {
	case tlaValueBool:
		return bool(data)
	default:
		panic(fmt.Errorf("%w: %v is not a boolean", TLATypeError, v))
	}
}

func (v TLAValue) AsNumber() int32 {
	switch data := v.data.(type) {
	case tlaValueNumber:
		return int32(data)
	default:
		panic(fmt.Errorf("%w: %v is not a number", TLATypeError, v))
	}
}

func (v TLAValue) AsString() string {
	switch data := v.data.(type) {
	case tlaValueString:
		return string(data)
	default:
		panic(fmt.Errorf("%w: %v is not a string", TLATypeError, v))
	}
}

func (v TLAValue) AsSet() *immutable.Map {
	switch data := v.data.(type) {
	case *tlaValueSet:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a set", TLATypeError, v))
	}
}

func (v TLAValue) AsTuple() *immutable.List {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		return data.List
	default:
		panic(fmt.Errorf("%w: %v is not a tuple", TLATypeError, v))
	}
}

func (v TLAValue) AsFunction() *tlaValueFunction {
	switch data := v.data.(type) {
	case *tlaValueFunction:
		return data
	default:
		panic(fmt.Errorf("%w: %v is not a function", TLATypeError, v))
	}
}

func (v TLAValue) SelectElement() TLAValue {
	set := v.AsSet()
	it := set.Iterator()
	if !it.Done() {
		key, _ := it.Next()
		return key.(TLAValue)
	} else {
		panic(fmt.Errorf("tried to select an element of %v, which was an empty set", v))
	}
}

func (v TLAValue) ApplyFunction(argument TLAValue) TLAValue {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		return data.Get(int(argument.AsNumber())).(TLAValue)
	case *tlaValueFunction:
		value, ok := data.Get(argument)
		if !ok {
			panic(fmt.Errorf("function %v's domain does not contain index %v", v, argument))
		}
		return value.(TLAValue)
	default:
		panic(fmt.Errorf("%w: could not apply %v", TLATypeError, v))
	}
}

func TLA_EqualsSymbol(lhs, rhs TLAValue) TLAValue {
	if lhs.Equal(rhs) {
		return TLA_TRUE
	} else {
		return TLA_FALSE
	}
}

type TLAValueHasher struct{}

var _ immutable.Hasher = TLAValueHasher{}

func (TLAValueHasher) Hash(key interface{}) uint32 {
	return key.(TLAValue).Hash()
}

func (TLAValueHasher) Equal(a, b interface{}) bool {
	return a.(TLAValue).Equal(b.(TLAValue))
}

type tlaValueImpl interface {
	Hash() uint32
	Equal(other TLAValue) bool
	String() string
}

type tlaValueBool bool

var _ tlaValueImpl = tlaValueBool(false)

var TLA_TRUE = TLAValue{tlaValueBool(true)}
var TLA_FALSE = TLAValue{tlaValueBool(false)}

func (v tlaValueBool) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, bool(v))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueBool) Equal(other TLAValue) bool {
	return bool(v) == other.AsBool()
}

func (v tlaValueBool) String() string {
	if v {
		return "TRUE"
	} else {
		return "FALSE"
	}
}

type tlaValueNumber int32

var _ tlaValueImpl = tlaValueNumber(0)

func NewTLANumber(num int32) TLAValue {
	return TLAValue{tlaValueNumber(num)}
}

func (v tlaValueNumber) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, int32(v))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueNumber) Equal(other TLAValue) bool {
	return int32(v) == other.AsNumber()
}

func (v tlaValueNumber) String() string {
	return strconv.FormatInt(int64(v), 10)
}

func TLA_PlusSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(lhs.AsNumber() + rhs.AsNumber())
}

func TLA_PercentSymbol(lhs, rhs TLAValue) TLAValue {
	return NewTLANumber(lhs.AsNumber() % rhs.AsNumber())
}

type tlaValueString string

var _ tlaValueImpl = tlaValueString("")

func NewTLAString(value string) TLAValue {
	return TLAValue{tlaValueString(value)}
}

func (v tlaValueString) Hash() uint32 {
	vC := string(v)
	h := fnv.New32()
	_, err := h.Write([]byte(vC))
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v tlaValueString) Equal(other TLAValue) bool {
	return string(v) == other.AsString()
}

func (v tlaValueString) String() string {
	return strconv.Quote(string(v))
}

type tlaValueSet struct {
	*immutable.Map
}

var _ tlaValueImpl = new(tlaValueSet)

func NewTLASet(members ...TLAValue) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, member := range members {
		builder.Set(member, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func (v *tlaValueSet) Hash() uint32 {
	var hash uint32 = 0
	it := v.Iterator()
	for !it.Done() {
		key, _ := it.Next()
		keyV := key.(TLAValue)
		// use XOR combination, so that all the set members are hashed out of order
		hash ^= keyV.Hash()
	}
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, hash)
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v *tlaValueSet) Equal(other TLAValue) bool {
	oC := other.AsSet()
	if v.Len() != oC.Len() {
		return false
	} else {
		it := v.Iterator()
		for !it.Done() {
			k, _ := it.Next()
			_, ok := oC.Get(k)
			if !ok {
				return false
			}
		}
		it = oC.Iterator()
		for !it.Done() {
			k, _ := it.Next()
			_, ok := v.Get(k)
			if !ok {
				return false
			}
		}
		return true
	}
}

func (v *tlaValueSet) String() string {
	builder := strings.Builder{}
	builder.WriteString("{")
	it := v.Iterator()
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			builder.WriteString(", ")
		}
		elem, _ := it.Next()
		builder.WriteString(elem.(TLAValue).String())
	}
	builder.WriteString("}")
	return builder.String()
}

func (v *tlaValueSet) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		err := encoder.Encode(elem.(TLAValue))
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueSet) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for {
		var elem TLAValue
		err := decoder.Decode(&elem)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.Map = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(elem, true)
	}
}

type tlaValueTuple struct {
	*immutable.List
}

var _ tlaValueImpl = new(tlaValueTuple)

func NewTLATuple(members ...TLAValue) TLAValue {
	builder := immutable.NewListBuilder()
	for _, member := range members {
		builder.Append(member)
	}
	return TLAValue{&tlaValueTuple{builder.List()}}
}

func (v *tlaValueTuple) Hash() uint32 {
	h := fnv.New32()
	it := v.Iterator()
	for !it.Done() {
		_, member := it.Next()
		memberV := member.(TLAValue)
		err := binary.Write(h, binary.LittleEndian, memberV.Hash())
		if err != nil {
			panic(err)
		}
	}
	return h.Sum32()
}

func (v *tlaValueTuple) Equal(other TLAValue) bool {
	otherTuple := other.AsTuple()
	if v.Len() != otherTuple.Len() {
		return false
	}
	it1, it2 := v.Iterator(), otherTuple.Iterator()
	for !it1.Done() || !it2.Done() {
		_, elem1 := it1.Next()
		_, elem2 := it2.Next()
		if !elem1.(TLAValue).data.Equal(elem2.(TLAValue)) {
			return false
		}
	}
	return true
}

func (v *tlaValueTuple) String() string {
	builder := strings.Builder{}
	builder.WriteString("<<")
	it := v.Iterator()
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			builder.WriteString(", ")
		}
		_, elem := it.Next()
		builder.WriteString(elem.(TLAValue).String())
	}
	builder.WriteString(">>")
	return builder.String()
}

func (v *tlaValueTuple) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		err := encoder.Encode(elem)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueTuple) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewListBuilder()
	for {
		var elem TLAValue
		err := decoder.Decode(&elem)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.List = builder.List()
				return nil
			} else {
				return err
			}
		}
		builder.Append(elem)
	}
}

type tlaValueFunction struct {
	*immutable.Map
	domain, rng *TLAValue
}

type TLARecordField struct {
	Key, Value TLAValue
}

func (field TLARecordField) Hash() uint32 {
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, field.Key.Hash())
	if err != nil {
		panic(err)
	}
	err = binary.Write(h, binary.LittleEndian, field.Value.Hash())
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

var _ tlaValueImpl = &tlaValueFunction{}

func NewTLARecord(pairs []TLARecordField) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, pair := range pairs {
		builder.Set(pair.Key, pair.Value)
	}
	return TLAValue{&tlaValueFunction{Map: builder.Map()}}
}

func (v *tlaValueFunction) Hash() uint32 {
	var hash uint32
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		hash ^= TLARecordField{Key: key.(TLAValue), Value: value.(TLAValue)}.Hash()
	}
	h := fnv.New32()
	err := binary.Write(h, binary.LittleEndian, hash)
	if err != nil {
		panic(err)
	}
	return h.Sum32()
}

func (v *tlaValueFunction) Equal(other TLAValue) bool {
	otherFunction := other.AsFunction()
	if v.Len() != otherFunction.Len() {
		return false
	}
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		otherValue, ok := otherFunction.Get(key)
		if !ok || !value.(TLAValue).Equal(otherValue.(TLAValue)) {
			return false
		}
	}
	return true
}

func (v *tlaValueFunction) String() string {
	builder := strings.Builder{}
	builder.WriteString("[")
	first := true
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		if first {
			first = false
		} else {
			builder.WriteString(", ")
		}
		builder.WriteString(key.(TLAValue).String())
		builder.WriteString(" |-> ")
		builder.WriteString(value.(TLAValue).String())
	}
	builder.WriteString("]")
	return builder.String()
}

func (v *tlaValueFunction) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		err := encoder.Encode(TLARecordField{
			Key:   key.(TLAValue),
			Value: value.(TLAValue),
		})
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *tlaValueFunction) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for {
		var field TLARecordField
		err := decoder.Decode(&field)
		if err != nil {
			if errors.Is(err, io.EOF) {
				v.Map = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(field.Key, field.Value)
	}
}
