package tla

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"

	"github.com/benbjohnson/immutable"
	"github.com/segmentio/fasthash/fnv1a"
)

var ErrTLAType = errors.New("TLA+ type error")

func init() {
	gob.Register(&valueBool{})
	gob.Register(&valueNumber{})
	gob.Register(&valueString{})
	gob.Register(&valueSet{})
	gob.Register(&valueTuple{})
	gob.Register(&valueFunction{})
	gob.Register(&valueCausalWrapped{})
}

type Value struct {
	data impl
}

var _ fmt.Stringer = Value{}
var _ gob.GobDecoder = &Value{}
var _ gob.GobEncoder = &Value{}

func MakeValueFromImpl(impl impl) Value {
	return Value{data: impl}
}

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

func (v Value) checkNil() {
	if v.data == nil {
		panic(fmt.Errorf("%w: %v is nil", ErrTLAType, v))
	}
}

func (v Value) IsBool() bool {
	if v.data != nil {
		return v.data.IsBool()
	}
	return false
}

func (v Value) IsNumber() bool {
	if v.data != nil {
		return v.data.IsNumber()
	}
	return false
}

func (v Value) IsString() bool {
	if v.data != nil {
		return v.data.IsString()
	}
	return false
}

func (v Value) IsSet() bool {
	if v.data != nil {
		return v.data.IsSet()
	}
	return false
}

func (v Value) IsTuple() bool {
	if v.data != nil {
		return v.data.IsTuple()
	}
	return false
}

func (v Value) IsFunction() bool {
	if v.data != nil {
		return v.data.IsFunction()
	}
	return false
}

func (v Value) AsBool() bool {
	v.checkNil()
	return v.data.AsBool()
}

func (v Value) AsNumber() int32 {
	v.checkNil()
	return v.data.AsNumber()
}

func (v Value) AsString() string {
	v.checkNil()
	return v.data.AsString()
}

func (v Value) AsSet() *immutable.Map[Value, bool] {
	v.checkNil()
	return v.data.AsSet()
}

func (v Value) AsTuple() *immutable.List[Value] {
	v.checkNil()
	return v.data.AsTuple()
}

func (v Value) AsFunction() *immutable.Map[Value, Value] {
	v.checkNil()
	return v.data.AsFunction()
}

func (v Value) GetVClock() *VClock {
	if v.data == nil {
		return nil
	}
	return v.data.GetVClock()
}

func (v Value) StripVClock() Value {
	if v.data == nil {
		return v
	}
	return v.data.StripVClock()
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
	switch {
	case v.IsTuple():
		data := v.AsTuple()
		idx := int(argument.AsNumber())
		require(idx >= 1 && idx <= data.Len(),
			fmt.Sprintf("tuple indices must be in range; note that tuples are 1-indexed in TLA+; idx=%v, data.Len()=%v", idx, data.Len()),
		)
		return data.Get(idx - 1)
	case v.IsFunction():
		data := v.AsFunction()
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

	IsBool() bool
	IsNumber() bool
	IsString() bool
	IsSet() bool
	IsTuple() bool
	IsFunction() bool

	AsBool() bool
	AsNumber() int32
	AsString() string
	AsSet() *immutable.Map[Value, bool]
	AsTuple() *immutable.List[Value]
	AsFunction() *immutable.Map[Value, Value]

	GetVClock() *VClock
	StripVClock() Value
}

type ImplStubs struct{}

func (ImplStubs) IsBool() bool {
	return false
}

func (ImplStubs) IsNumber() bool {
	return false
}

func (ImplStubs) IsString() bool {
	return false
}

func (ImplStubs) IsSet() bool {
	return false
}

func (ImplStubs) IsTuple() bool {
	return false
}

func (ImplStubs) IsFunction() bool {
	return false
}

func (ImplStubs) AsBool() bool {
	panic(fmt.Errorf("%w: is not a boolean", ErrTLAType))
}

func (ImplStubs) AsNumber() int32 {
	panic(fmt.Errorf("%w: is not a number", ErrTLAType))
}

func (ImplStubs) AsString() string {
	panic(fmt.Errorf("%w: is not a string", ErrTLAType))
}

func (ImplStubs) AsSet() *immutable.Map[Value, bool] {
	panic(fmt.Errorf("%w: is not a set", ErrTLAType))
}

func (ImplStubs) AsTuple() *immutable.List[Value] {
	panic(fmt.Errorf("%w: is not a tuple", ErrTLAType))
}

func (ImplStubs) AsFunction() *immutable.Map[Value, Value] {
	panic(fmt.Errorf("%w: is not a function", ErrTLAType))
}

func (ImplStubs) GetVClock() *VClock {
	return nil
}

type valueBool struct {
	ImplStubs
	V bool // public or gob doesn't work!
}

var _ impl = &valueBool{}

func MakeBool(v bool) Value {
	if v {
		return ModuleTRUE
	} else {
		return ModuleFALSE
	}
}

func (v *valueBool) Hash() uint32 {
	if v.AsBool() {
		return fnv1a.HashUint32(1)
	}
	return fnv1a.HashUint32(0)
}

func (v *valueBool) Equal(other Value) bool {
	return other.IsBool() && v.AsBool() == other.AsBool()
}

func (v *valueBool) String() string {
	if v.AsBool() {
		return "TRUE"
	} else {
		return "FALSE"
	}
}

func (v *valueBool) IsBool() bool {
	return true
}

func (v *valueBool) AsBool() bool {
	return v.V
}

func (v *valueBool) StripVClock() Value {
	return Value{v}
}

type valueNumber struct {
	ImplStubs
	V int32 // public! Needed for gob to work.
}

var _ impl = &valueNumber{}

func MakeNumber(num int32) Value {
	return Value{&valueNumber{V: num}}
}

func (v *valueNumber) Hash() uint32 {
	return fnv1a.HashUint32(uint32(v.AsNumber()))
}

func (v *valueNumber) Equal(other Value) bool {
	return other.IsNumber() && v.AsNumber() == other.AsNumber()
}

func (v *valueNumber) String() string {
	return strconv.FormatInt(int64(v.AsNumber()), 10)
}

func (v *valueNumber) IsNumber() bool {
	return true
}

func (v *valueNumber) AsNumber() int32 {
	return v.V
}

func (v *valueNumber) StripVClock() Value {
	return Value{v}
}

type valueString struct {
	ImplStubs
	V string // public for gob decode to work!
}

var _ impl = &valueString{}

func MakeString(value string) Value {
	return Value{&valueString{V: value}}
}

func (v *valueString) Hash() uint32 {
	return fnv1a.HashString32(v.AsString())
}

func (v *valueString) Equal(other Value) bool {
	return other.IsString() && v.AsString() == other.AsString()
}

func (v *valueString) String() string {
	return strconv.Quote(v.AsString())
}

func (v *valueString) IsString() bool {
	return true
}

func (v *valueString) AsString() string {
	return v.V
}

func (v *valueString) StripVClock() Value {
	return Value{v}
}

type valueSet struct {
	ImplStubs
	v *immutable.Map[Value, bool]
}

var _ impl = &valueSet{}

func MakeSet(members ...Value) Value {
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	for _, member := range members {
		builder.Set(member, true)
	}
	return Value{&valueSet{v: builder.Map()}}
}

func MakeSetFromMap(m *immutable.Map[Value, bool]) Value {
	return Value{&valueSet{v: m}}
}

func (v *valueSet) Hash() uint32 {
	var hash uint32 = 0
	it := v.AsSet().Iterator()
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
	c := v.AsSet()
	oC := other.AsSet()
	if c.Len() != oC.Len() {
		return false
	} else {
		it := c.Iterator()
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
			_, ok := c.Get(k)
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
	it := v.AsSet().Iterator()
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
	it := v.AsSet().Iterator()
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
				v.v = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(elem, true)
	}
}

func (v *valueSet) IsSet() bool {
	return true
}

func (v *valueSet) AsSet() *immutable.Map[Value, bool] {
	return v.v
}

func (v *valueSet) StripVClock() Value {
	return Value{v}
}

type valueTuple struct {
	ImplStubs
	v *immutable.List[Value]
}

var _ impl = &valueTuple{}

func MakeTuple(members ...Value) Value {
	builder := immutable.NewListBuilder[Value]()
	for _, member := range members {
		builder.Append(member)
	}
	return Value{&valueTuple{v: builder.List()}}
}

func MakeTupleFromList(list *immutable.List[Value]) Value {
	return Value{&valueTuple{v: list}}
}

func (v *valueTuple) Hash() uint32 {
	h := fnv1a.Init32
	it := v.AsTuple().Iterator()
	for !it.Done() {
		_, member := it.Next()
		memberV := member
		h = fnv1a.AddUint32(h, memberV.Hash())
	}
	return h
}

func (v *valueTuple) Equal(other Value) bool {
	if !other.IsTuple() {
		return false
	}

	tuple := v.AsTuple()
	otherTuple := other.AsTuple()
	if tuple.Len() != otherTuple.Len() {
		return false
	}
	it1, it2 := tuple.Iterator(), otherTuple.Iterator()
	for !it1.Done() && !it2.Done() {
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
	it := v.AsTuple().Iterator()
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
	it := v.AsTuple().Iterator()
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
				v.v = builder.List()
				return nil
			} else {
				return err
			}
		}
		builder.Append(elem)
	}
}

func (v *valueTuple) IsTuple() bool {
	return true
}

func (v *valueTuple) AsTuple() *immutable.List[Value] {
	return v.v
}

func (v *valueTuple) StripVClock() Value {
	return Value{v}
}

type valueFunction struct {
	ImplStubs
	v *immutable.Map[Value, Value]
}

type RecordField struct {
	Key, Value Value
}

func (field RecordField) Hash() uint32 {
	h := fnv1a.Init32
	h = fnv1a.AddUint32(h, field.Key.Hash())
	h = fnv1a.AddUint32(h, field.Value.Hash())
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

	return Value{&valueFunction{v: builder.Map()}}
}

func MakeRecord(pairs []RecordField) Value {
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})
	for _, pair := range pairs {
		builder.Set(pair.Key, pair.Value)
	}
	return Value{&valueFunction{v: builder.Map()}}
}

func MakeRecordFromMap(m *immutable.Map[Value, Value]) Value {
	return Value{&valueFunction{v: m}}
}

func MakeRecordSet(pairs []RecordField) Value {
	recordSet := immutable.NewMap[Value, bool](ValueHasher{})
	// start with a set of one empty map
	recordSet = recordSet.Set(Value{&valueFunction{v: immutable.NewMap[Value, Value](ValueHasher{})}}, true)
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
				builder.Set(Value{&valueFunction{v: accFn.Set(pair.Key, val)}}, true)
			}
		}
		recordSet = builder.Map()
	}
	return Value{&valueSet{v: recordSet}}
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
	it := v.AsFunction().Iterator()
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

	function := v.AsFunction()
	otherFunction := other.AsFunction()
	if function.Len() != otherFunction.Len() {
		return false
	}
	it := function.Iterator()
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
	if v.AsFunction().Len() == 0 {
		return "[x \\in {} |-> x]"
	}
	builder := strings.Builder{}
	builder.WriteString("(")
	first := true
	it := v.AsFunction().Iterator()
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
	it := v.AsFunction().Iterator()
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
				v.v = builder.Map()
				return nil
			} else {
				return err
			}
		}
		builder.Set(field.Key, field.Value)
	}
}

func (v *valueFunction) IsFunction() bool {
	return true
}

func (v *valueFunction) AsFunction() *immutable.Map[Value, Value] {
	return v.v
}

func (v *valueFunction) StripVClock() Value {
	return Value{v}
}

var vClocksEnabled bool

func init() {
	var env string
	env, vClocksEnabled = os.LookupEnv("PGO_TRACE_DIR")
	vClocksEnabled = vClocksEnabled && env != ""
}

type valueCausalWrapped struct {
	Value // forward almost everything to the value, be almost invisible
	clock VClock
}

var _ impl = &valueCausalWrapped{}

func WrapCausal(value Value, clock VClock) Value {
	if !vClocksEnabled {
		return value
	}

	if existingClock := value.GetVClock(); existingClock != nil {
		clock = clock.Merge(*existingClock)
	}

	switch data := value.data.(type) {
	case *valueCausalWrapped:
		return Value{&valueCausalWrapped{
			Value: data.Value,
			clock: clock,
		}}
	default:
		return Value{&valueCausalWrapped{
			Value: value,
			clock: clock,
		}}
	}
}

func (v *valueCausalWrapped) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	encoder.Encode(&v.clock)
	encoder.Encode(&v.Value)
	return buf.Bytes(), nil
}

func (v *valueCausalWrapped) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	err := decoder.Decode(&v.clock)
	if err != nil {
		return err
	}
	return decoder.Decode(&v.Value)
}

func (v valueCausalWrapped) GetVClock() *VClock {
	return &v.clock
}

func (v valueCausalWrapped) StripVClock() Value {
	return v.Value
}
