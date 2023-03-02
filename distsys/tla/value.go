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
	gob.Register(valueBool(false))
	gob.Register(valueNumber(0))
	gob.Register(valueString(""))
	gob.Register(&valueSet{})
	gob.Register(&valueTuple{})
	gob.Register(&valueFunction{})
}

type Value struct {
	data impl
}

var _ fmt.Stringer = Value{}
var _ gob.GobDecoder = &Value{}
var _ gob.GobEncoder = &Value{}

func (v Value) Hash() uint32 {
	if v.data == nil {
		return 0
	} else {
		return v.data.Hash()
	}
}

func (v Value) Equal(other Value) bool {
	if v.data == nil && other.data == nil {
		return true
	} else if v.data == nil || other.data == nil {
		return false
	} else {
		return v.data.Equal(other)
	}
}

func (v Value) String() string {
	if v.data == nil {
		return "defaultInitValue"
	} else {
		return v.data.String()
	}
}

func (v *Value) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	return decoder.Decode(&v.data)
}

func (v *Value) GobEncode() ([]byte, error) {
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

func (v Value) IsBool() bool {
	switch v.data.(type) {
	case valueBool:
		return true
	default:
		return false
	}
}

func (v Value) IsNumber() bool {
	switch v.data.(type) {
	case valueNumber:
		return true
	default:
		return false
	}
}

func (v Value) IsString() bool {
	switch v.data.(type) {
	case valueString:
		return true
	default:
		return false
	}
}

func (v Value) IsSet() bool {
	switch v.data.(type) {
	case *valueSet:
		return true
	default:
		return false
	}
}

func (v Value) IsTuple() bool {
	switch v.data.(type) {
	case *valueTuple:
		return true
	default:
		return false
	}
}

func (v Value) IsFunction() bool {
	switch v.data.(type) {
	case *valueFunction:
		return true
	default:
		return false
	}
}

func (v Value) AsBool() bool {
	switch data := v.data.(type) {
	case valueBool:
		return bool(data)
	default:
		panic(fmt.Errorf("%w: %v is not a boolean", ErrTLAType, v))
	}
}

func (v Value) AsNumber() int32 {
	switch data := v.data.(type) {
	case valueNumber:
		return int32(data)
	default:
		panic(fmt.Errorf("%w: %v is not a number", ErrTLAType, v))
	}
}

func (v Value) AsString() string {
	switch data := v.data.(type) {
	case valueString:
		return string(data)
	default:
		panic(fmt.Errorf("%w: %v is not a string", ErrTLAType, v))
	}
}

func (v Value) AsSet() *immutable.Map[Value, bool] {
	switch data := v.data.(type) {
	case *valueSet:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a set", ErrTLAType, v))
	}
}

func (v Value) AsTuple() *immutable.List[Value] {
	switch data := v.data.(type) {
	case *valueTuple:
		return data.List
	default:
		panic(fmt.Errorf("%w: %v is not a tuple", ErrTLAType, v))
	}
}

func (v Value) AsFunction() *immutable.Map[Value, Value] {
	switch data := v.data.(type) {
	case *valueFunction:
		return data.Map
	default:
		panic(fmt.Errorf("%w: %v is not a function", ErrTLAType, v))
	}
}

func (v Value) SelectElement(idx uint) Value {
	set := v.AsSet()
	it := set.Iterator()
	var i uint = 0
	for ; i < idx && !it.Done(); i++ {
		_, _, _ = it.Next()
	}
	if !it.Done() && i == idx {
		key, _, _ := it.Next()
		return key
	} else {
		panic(fmt.Errorf("%w: tried to select element %d of %v, which does not exist", ErrTLAType, idx, v))
	}
}

func (v Value) ApplyFunction(argument Value) Value {
	switch data := v.data.(type) {
	case *valueTuple:
		idx := int(argument.AsNumber())
		require(idx >= 1 && idx <= data.Len(),
			fmt.Sprintf("tuple indices must be in range; note that tuples are 1-indexed in TLA+; idx=%v, data.Len()=%v", idx, data.Len()),
		)
		return data.Get(idx - 1)
	case *valueFunction:
		value, ok := data.Get(argument)
		if !ok {
			panic(fmt.Errorf("%w: function %v's domain does not contain index %v", ErrTLAType, v, argument))
		}
		return value
	default:
		panic(fmt.Errorf("%w: could not apply %v", ErrTLAType, v))
	}
}

func (v Value) PCalPrint() {
	fmt.Println(v)
}

type ValueHasher struct{}

var _ immutable.Hasher[Value] = ValueHasher{}

func (ValueHasher) Hash(key Value) uint32 {
	return key.Hash()
}

func (ValueHasher) Equal(a, b Value) bool {
	return a.Equal(b)
}

type impl interface {
	Hash() uint32
	Equal(other Value) bool
	String() string
}

type valueBool bool

var _ impl = valueBool(false)

func MakeBool(v bool) Value {
	if v {
		return ModuleTRUE
	} else {
		return ModuleFALSE
	}
}

func (v valueBool) Hash() uint32 {
	if v {
		return fnv1a.HashUint32(1)
	}
	return fnv1a.HashUint32(0)
}

func (v valueBool) Equal(other Value) bool {
	return other.IsBool() && bool(v) == other.AsBool()
}

func (v valueBool) String() string {
	if v {
		return "TRUE"
	} else {
		return "FALSE"
	}
}

type valueNumber int32

var _ impl = valueNumber(0)

func MakeNumber(num int32) Value {
	return Value{valueNumber(num)}
}

func (v valueNumber) Hash() uint32 {
	return fnv1a.HashUint32(uint32(v))
}

func (v valueNumber) Equal(other Value) bool {
	return other.IsNumber() && int32(v) == other.AsNumber()
}

func (v valueNumber) String() string {
	return strconv.FormatInt(int64(v), 10)
}

type valueString string

var _ impl = valueString("")

func MakeString(value string) Value {
	return Value{valueString(value)}
}

func (v valueString) Hash() uint32 {
	return fnv1a.HashString32(string(v))
}

func (v valueString) Equal(other Value) bool {
	return other.IsString() && string(v) == other.AsString()
}

func (v valueString) String() string {
	return strconv.Quote(string(v))
}

type valueSet struct {
	*immutable.Map[Value, bool]
}

var _ impl = new(valueSet)

func MakeSet(members ...Value) Value {
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	for _, member := range members {
		builder.Set(member, true)
	}
	return Value{&valueSet{builder.Map()}}
}

func MakeSetFromMap(m *immutable.Map[Value, bool]) Value {
	return Value{&valueSet{m}}
}

func (v *valueSet) Hash() uint32 {
	var hash uint32 = 0
	it := v.Iterator()
	for !it.Done() {
		key, _, _ := it.Next()
		keyV := key
		// use XOR combination, so that all the set members are hashed out of order
		hash ^= keyV.Hash()
	}
	return fnv1a.HashUint32(hash)
}

func (v *valueSet) Equal(other Value) bool {
	if !other.IsSet() {
		return false
	}
	oC := other.AsSet()
	if v.Len() != oC.Len() {
		return false
	} else {
		it := v.Iterator()
		for !it.Done() {
			k, _, _ := it.Next()
			_, ok := oC.Get(k)
			if !ok {
				return false
			}
		}
		it = oC.Iterator()
		for !it.Done() {
			k, _, _ := it.Next()
			_, ok := v.Get(k)
			if !ok {
				return false
			}
		}
		return true
	}
}

func (v *valueSet) String() string {
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
		elem, _, _ := it.Next()
		builder.WriteString(elem.String())
	}
	builder.WriteString("}")
	return builder.String()
}

func (v *valueSet) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		elemV := elem
		err := encoder.Encode(&elemV) // make sure encoded thing is addressable
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *valueSet) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	for {
		var elem Value
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

type valueTuple struct {
	*immutable.List[Value]
}

var _ impl = new(valueTuple)

func MakeTuple(members ...Value) Value {
	builder := immutable.NewListBuilder[Value]()
	for _, member := range members {
		builder.Append(member)
	}
	return Value{&valueTuple{builder.List()}}
}

func MakeTupleFromList(list *immutable.List[Value]) Value {
	return Value{&valueTuple{list}}
}

func (v *valueTuple) Hash() uint32 {
	h := fnv1a.Init32
	it := v.Iterator()
	for !it.Done() {
		_, member := it.Next()
		memberV := member
		fnv1a.AddUint32(h, memberV.Hash())
	}
	return h
}

func (v *valueTuple) Equal(other Value) bool {
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
		if !elem1.data.Equal(elem2) {
			return false
		}
	}
	return true
}

func (v *valueTuple) String() string {
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
		builder.WriteString(elem.String())
	}
	builder.WriteString(">>")
	return builder.String()
}

func (v *valueTuple) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		elemV := elem
		err := encoder.Encode(&elemV)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *valueTuple) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewListBuilder[Value]()
	for {
		var elem Value
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

type valueFunction struct {
	*immutable.Map[Value, Value]
}

type RecordField struct {
	Key, Value Value
}

func (field RecordField) Hash() uint32 {
	h := fnv1a.Init32
	fnv1a.AddUint32(h, field.Key.Hash())
	fnv1a.AddUint32(h, field.Value.Hash())
	return h
}

var _ impl = &valueFunction{}

func MakeFunction(setVals []Value, body func([]Value) Value) Value {
	require(len(setVals) > 0, "the domain of a TLA+ function cannot be the product of no sets")
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})

	var sets []*immutable.Map[Value, bool]
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	bodyArgs := make([]Value, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(bodyArgs) {
			if len(bodyArgs) == 1 {
				builder.Set(bodyArgs[0], body(bodyArgs))
			} else {
				builder.Set(MakeTuple(bodyArgs...), body(bodyArgs))
			}
		} else {
			it := sets[idx].Iterator()
			for !it.Done() {
				elem, _, _ := it.Next()
				bodyArgs[idx] = elem
				helper(idx + 1)
			}
		}
	}
	helper(0)

	return Value{&valueFunction{builder.Map()}}
}

func MakeRecord(pairs []RecordField) Value {
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})
	for _, pair := range pairs {
		builder.Set(pair.Key, pair.Value)
	}
	return Value{&valueFunction{builder.Map()}}
}

func MakeRecordFromMap(m *immutable.Map[Value, Value]) Value {
	return Value{&valueFunction{m}}
}

func MakeRecordSet(pairs []RecordField) Value {
	recordSet := immutable.NewMap[Value, bool](ValueHasher{})
	// start with a set of one empty map
	recordSet = recordSet.Set(Value{&valueFunction{immutable.NewMap[Value, Value](ValueHasher{})}}, true)
	for _, pair := range pairs {
		fieldValueSet := pair.Value.AsSet()
		builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
		// iterate over accumulated set of records, and add every possible value for this field, from fieldValueSet
		it := recordSet.Iterator()
		for !it.Done() {
			acc, _, _ := it.Next()
			accFn := acc.AsFunction()
			valIt := fieldValueSet.Iterator()
			for !valIt.Done() {
				val, _, _ := valIt.Next()
				builder.Set(Value{&valueFunction{accFn.Set(pair.Key, val)}}, true)
			}
		}
		recordSet = builder.Map()
	}
	return Value{&valueSet{recordSet}}
}

func MakeFunctionSet(from, to Value) Value {
	fromSet, _ := from.AsSet(), to.AsSet()
	var pairs []RecordField
	it := fromSet.Iterator()
	for !it.Done() {
		key, _, _ := it.Next()
		pairs = append(pairs, RecordField{
			Key:   key,
			Value: to,
		})
	}
	return MakeRecordSet(pairs)
}

func (v *valueFunction) Hash() uint32 {
	var hash uint32
	it := v.Iterator()
	for !it.Done() {
		key, value, _ := it.Next()
		hash ^= RecordField{Key: key, Value: value}.Hash()
	}
	return fnv1a.HashUint32(hash)
}

func (v *valueFunction) Equal(other Value) bool {
	if !other.IsFunction() {
		return false
	}

	otherFunction := other.AsFunction()
	if v.Len() != otherFunction.Len() {
		return false
	}
	it := v.Iterator()
	for !it.Done() {
		key, value, _ := it.Next()
		otherValue, ok := otherFunction.Get(key)
		if !ok || !value.Equal(otherValue) {
			return false
		}
	}
	return true
}

func (v *valueFunction) String() string {
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
		key, value, _ := it.Next()
		if first {
			first = false
		} else {
			builder.WriteString(" @@ ")
		}
		builder.WriteString("(")
		builder.WriteString(key.String())
		builder.WriteString(") :> (")
		builder.WriteString(value.String())
		builder.WriteString(")")
	}
	builder.WriteString(")")
	return builder.String()
}

func (v *valueFunction) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := v.Iterator()
	for !it.Done() {
		key, value, _ := it.Next()
		field := RecordField{
			Key:   key,
			Value: value,
		}
		err := encoder.Encode(&field)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (v *valueFunction) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})
	for {
		var field RecordField
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
