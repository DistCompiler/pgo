package tla

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"

	"github.com/benbjohnson/immutable"
	"github.com/segmentio/fasthash/fnv1a"
)

var ErrTLAType = errors.New("TLA+ type error")

func init() {
	gob.Register(tlaValueBool(false))
	gob.Register(tlaValueNumber(0))
	gob.Register(tlaValueString(""))
	gob.Register(&tlaValueSet{})
	gob.Register(&tlaValueTuple{})
	gob.Register(&tlaValueFunction{})
}

type TLAValue struct {
	data tlaValueImpl
}

var _ fmt.Stringer = TLAValue{}
var _ gob.GobDecoder = &TLAValue{}
var _ gob.GobEncoder = &TLAValue{}

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

func require(req bool, msg string) {
	if !req {
		panic(fmt.Errorf("%w: %s", ErrTLAType, msg))
	}
}

func (v TLAValue) IsBool() bool {
	switch v.data.(type) {
	case tlaValueBool:
		return true
	default:
		return false
	}
}

func (v TLAValue) IsNumber() bool {
	switch v.data.(type) {
	case tlaValueNumber:
		return true
	default:
		return false
	}
}

func (v TLAValue) IsString() bool {
	switch v.data.(type) {
	case tlaValueString:
		return true
	default:
		return false
	}
}

func (v TLAValue) IsSet() bool {
	switch v.data.(type) {
	case *tlaValueSet:
		return true
	default:
		return false
	}
}

func (v TLAValue) IsTuple() bool {
	switch v.data.(type) {
	case *tlaValueTuple:
		return true
	default:
		return false
	}
}

func (v TLAValue) IsFunction() bool {
	switch v.data.(type) {
	case *tlaValueFunction:
		return true
	default:
		return false
	}
}

func (v TLAValue) AsBool() bool {
	switch data := v.data.(type) {
	case tlaValueBool:
		return bool(data)
	default:
		panic(fmt.Errorf("%w: %v is not a boolean", ErrTLAType, v))
	}
}

func (v TLAValue) AsNumber() int32 {
	switch data := v.data.(type) {
	case tlaValueNumber:
		return int32(data)
	default:
		panic(fmt.Errorf("%w: %v is not a number", ErrTLAType, v))
	}
}

func (v TLAValue) AsString() string {
	switch data := v.data.(type) {
	case tlaValueString:
		return string(data)
	default:
		panic(fmt.Errorf("%w: %v is not a string", ErrTLAType, v))
	}
}

func (v TLAValue) AsSet() *immutable.Map {
	switch data := v.data.(type) {
	case *tlaValueSet:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a set", ErrTLAType, v))
	}
}

func (v TLAValue) AsTuple() *immutable.List {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		return data.List
	default:
		panic(fmt.Errorf("%w: %v is not a tuple", ErrTLAType, v))
	}
}

func (v TLAValue) AsFunction() *immutable.Map {
	switch data := v.data.(type) {
	case *tlaValueFunction:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a function", ErrTLAType, v))
	}
}

func (v TLAValue) SelectElement(idx uint) TLAValue {
	set := v.AsSet()
	it := set.Iterator()
	var i uint = 0
	for ; i < idx && !it.Done(); i++ {
		_, _ = it.Next()
	}
	if !it.Done() && i == idx {
		key, _ := it.Next()
		return key.(TLAValue)
	} else {
		panic(fmt.Errorf("%w: tried to select element %d of %v, which does not exist", ErrTLAType, idx, v))
	}
}

func (v TLAValue) ApplyFunction(argument TLAValue) TLAValue {
	switch data := v.data.(type) {
	case *tlaValueTuple:
		idx := int(argument.AsNumber())
		require(idx >= 1 && idx <= data.Len(),
			fmt.Sprintf("tuple indices must be in range; note that tuples are 1-indexed in TLA+; idx=%v, data.Len()=%v", idx, data.Len()),
		)
		return data.Get(idx - 1).(TLAValue)
	case *tlaValueFunction:
		value, ok := data.Get(argument)
		if !ok {
			panic(fmt.Errorf("%w: function %v's domain does not contain index %v", ErrTLAType, v, argument))
		}
		return value.(TLAValue)
	default:
		panic(fmt.Errorf("%w: could not apply %v", ErrTLAType, v))
	}
}

func (v TLAValue) PCalPrint() {
	fmt.Println(v)
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

func MakeTLABool(v bool) TLAValue {
	if v {
		return TLA_TRUE
	} else {
		return TLA_FALSE
	}
}

func (v tlaValueBool) Hash() uint32 {
	if bool(v) {
		return fnv1a.HashUint32(1)
	}
	return fnv1a.HashUint32(0)
}

func (v tlaValueBool) Equal(other TLAValue) bool {
	return other.IsBool() && bool(v) == other.AsBool()
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

func MakeTLANumber(num int32) TLAValue {
	return TLAValue{tlaValueNumber(num)}
}

func (v tlaValueNumber) Hash() uint32 {
	return fnv1a.HashUint32(uint32(v))
}

func (v tlaValueNumber) Equal(other TLAValue) bool {
	return other.IsNumber() && int32(v) == other.AsNumber()
}

func (v tlaValueNumber) String() string {
	return strconv.FormatInt(int64(v), 10)
}

type tlaValueString string

var _ tlaValueImpl = tlaValueString("")

func MakeTLAString(value string) TLAValue {
	return TLAValue{tlaValueString(value)}
}

func (v tlaValueString) Hash() uint32 {
	return fnv1a.HashString32(string(v))
}

func (v tlaValueString) Equal(other TLAValue) bool {
	return other.IsString() && string(v) == other.AsString()
}

func (v tlaValueString) String() string {
	return strconv.Quote(string(v))
}

type tlaValueSet struct {
	*immutable.Map
}

var _ tlaValueImpl = new(tlaValueSet)

func MakeTLASet(members ...TLAValue) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, member := range members {
		builder.Set(member, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func MakeTLASetFromMap(m *immutable.Map) TLAValue {
	return TLAValue{&tlaValueSet{m}}
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
	return fnv1a.HashUint32(hash)
}

func (v *tlaValueSet) Equal(other TLAValue) bool {
	if !other.IsSet() {
		return false
	}
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
		elemV := elem.(TLAValue)
		err := encoder.Encode(&elemV) // make sure encoded thing is addressable
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

func MakeTLATuple(members ...TLAValue) TLAValue {
	builder := immutable.NewListBuilder()
	for _, member := range members {
		builder.Append(member)
	}
	return TLAValue{&tlaValueTuple{builder.List()}}
}

func MakeTLATupleFromList(list *immutable.List) TLAValue {
	return TLAValue{&tlaValueTuple{list}}
}

func (v *tlaValueTuple) Hash() uint32 {
	h := fnv1a.Init32
	it := v.Iterator()
	for !it.Done() {
		_, member := it.Next()
		memberV := member.(TLAValue)
		fnv1a.AddUint32(h, memberV.Hash())
	}
	return h
}

func (v *tlaValueTuple) Equal(other TLAValue) bool {
	if !other.IsTuple() {
		return false
	}

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
		elemV := elem.(TLAValue)
		err := encoder.Encode(&elemV)
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
}

type TLARecordField struct {
	Key, Value TLAValue
}

func (field TLARecordField) Hash() uint32 {
	h := fnv1a.Init32
	fnv1a.AddUint32(h, field.Key.Hash())
	fnv1a.AddUint32(h, field.Value.Hash())
	return h
}

var _ tlaValueImpl = &tlaValueFunction{}

func MakeTLAFunction(setVals []TLAValue, body func([]TLAValue) TLAValue) TLAValue {
	require(len(setVals) > 0, "the domain of a TLA+ function cannot be the product of no sets")
	builder := immutable.NewMapBuilder(TLAValueHasher{})

	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	bodyArgs := make([]TLAValue, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(bodyArgs) {
			if len(bodyArgs) == 1 {
				builder.Set(bodyArgs[0], body(bodyArgs))
			} else {
				builder.Set(MakeTLATuple(bodyArgs...), body(bodyArgs))
			}
		} else {
			it := sets[idx].Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				bodyArgs[idx] = elem.(TLAValue)
				helper(idx + 1)
			}
		}
	}
	helper(0)

	return TLAValue{&tlaValueFunction{builder.Map()}}
}

func MakeTLARecord(pairs []TLARecordField) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for _, pair := range pairs {
		builder.Set(pair.Key, pair.Value)
	}
	return TLAValue{&tlaValueFunction{builder.Map()}}
}

func MakeTLARecordFromMap(m *immutable.Map) TLAValue {
	return TLAValue{&tlaValueFunction{m}}
}

func MakeTLARecordSet(pairs []TLARecordField) TLAValue {
	recordSet := immutable.NewMap(TLAValueHasher{})
	// start with a set of one empty map
	recordSet = recordSet.Set(TLAValue{&tlaValueFunction{immutable.NewMap(TLAValueHasher{})}}, true)
	for _, pair := range pairs {
		fieldValueSet := pair.Value.AsSet()
		builder := immutable.NewMapBuilder(TLAValueHasher{})
		// iterate over accumulated set of records, and add every possible value for this field, from fieldValueSet
		it := recordSet.Iterator()
		for !it.Done() {
			acc, _ := it.Next()
			accFn := acc.(TLAValue).AsFunction()
			valIt := fieldValueSet.Iterator()
			for !valIt.Done() {
				val, _ := valIt.Next()
				builder.Set(TLAValue{&tlaValueFunction{accFn.Set(pair.Key, val)}}, true)
			}
		}
		recordSet = builder.Map()
	}
	return TLAValue{&tlaValueSet{recordSet}}
}

func MakeTLAFunctionSet(from, to TLAValue) TLAValue {
	fromSet, _ := from.AsSet(), to.AsSet()
	var pairs []TLARecordField
	it := fromSet.Iterator()
	for !it.Done() {
		key, _ := it.Next()
		pairs = append(pairs, TLARecordField{
			Key:   key.(TLAValue),
			Value: to,
		})
	}
	return MakeTLARecordSet(pairs)
}

func (v *tlaValueFunction) Hash() uint32 {
	var hash uint32
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		hash ^= TLARecordField{Key: key.(TLAValue), Value: value.(TLAValue)}.Hash()
	}
	return fnv1a.HashUint32(hash)
}

func (v *tlaValueFunction) Equal(other TLAValue) bool {
	if !other.IsFunction() {
		return false
	}

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
	// special case the empty function; a concatenation of 0 functions looks like `()`, which doesn't parse
	// but this trivially empty function expression should do the trick
	if v.Map.Len() == 0 {
		return "[x \\in {} |-> x]"
	}
	builder := strings.Builder{}
	builder.WriteString("(")
	first := true
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		if first {
			first = false
		} else {
			builder.WriteString(" @@ ")
		}
		builder.WriteString("(")
		builder.WriteString(key.(TLAValue).String())
		builder.WriteString(") :> (")
		builder.WriteString(value.(TLAValue).String())
		builder.WriteString(")")
	}
	builder.WriteString(")")
	return builder.String()
}

func (v *tlaValueFunction) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		key, value := it.Next()
		field := TLARecordField{
			Key:   key.(TLAValue),
			Value: value.(TLAValue),
		}
		err := encoder.Encode(&field)
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
