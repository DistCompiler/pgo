package distsys

import (
    "encoding/binary"
    "encoding/gob"
    "errors"
    "fmt"
    "github.com/benbjohnson/immutable"
    "hash/fnv"
    "strconv"
    "strings"
)

var TLATypeError = errors.New("TLA+ type error")

func init() {
    gob.Register(tlaValueBool(true))
    gob.Register(tlaValueNumber(0))
    gob.Register(tlaValueString(""))
    gob.Register(tlaValueSet{})
    gob.Register(tlaValueTuple{})
}

type TLAValue struct {
    data tlaValueImpl
}

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

func (v TLAValue) AsBool() bool {
    switch data := v.data.(type) {
    case tlaValueBool:
        return bool(data)
    default:
        panic(TLATypeError)
    }
}

func (v TLAValue) AsNumber() int32 {
    switch data := v.data.(type) {
    case tlaValueNumber:
        return int32(data)
    default:
        panic(TLATypeError)
    }
}

func (v TLAValue) AsString() string {
    switch data := v.data.(type) {
    case tlaValueString:
        return string(data)
    default:
        panic(TLATypeError)
    }
}

func (v TLAValue) AsSet() immutable.Map {
    switch data := v.data.(type) {
    case tlaValueSet:
        return immutable.Map(data)
    default:
        panic(TLATypeError)
    }
}

func (v TLAValue) AsTuple() immutable.List {
    switch data := v.data.(type) {
    case tlaValueTuple:
        return immutable.List(data)
    default:
        panic(TLATypeError)
    }
}

func (v TLAValue) IsTrue() bool {
    return v.AsBool()
}

func (v TLAValue) SelectElement() TLAValue {
    set := v.AsSet()
    it := set.Iterator()
    if !it.Done() {
        key, _ := it.Next()
        return key.(TLAValue)
    } else {
        panic(fmt.Errorf(""))
    }
}


type TLAValueHasher struct{}

func (TLAValueHasher) Hash(key interface{}) uint32 {
    return key.(TLAValue).Hash()
}

func (hasher TLAValueHasher) Equal(a, b interface{}) bool {
    return a.(TLAValue).Equal(b.(TLAValue))
}

type tlaValueImpl interface {
    Hash() uint32
    Equal(other TLAValue) bool
    String() string
}

type tlaValueBool bool

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
    return TLAValue{tlaValueNumber(lhs.AsNumber() + rhs.AsNumber())}
}

type tlaValueString string

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

type tlaValueSet immutable.Map

func NewTLASet(members ...TLAValue) TLAValue {
    builder := immutable.NewMapBuilder(TLAValueHasher{})
    for _, member := range members {
        builder.Set(member, true)
    }
    return TLAValue{tlaValueSet(*builder.Map())}
}

func (v tlaValueSet) Hash() uint32 {
    vC := immutable.Map(v)
    var hash uint32 = 0
    it := vC.Iterator()
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

func (v tlaValueSet) Equal(other TLAValue) bool {
    vC := immutable.Map(v)
    oC := other.AsSet()
    if vC.Len() != oC.Len() {
        return false
    } else {
        it := vC.Iterator()
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
            _, ok := vC.Get(k)
            if !ok {
                return false
            }
        }
        return true
    }
}

func (v tlaValueSet) String() string {
    builder := strings.Builder{}
    builder.WriteString("{")
    vC := immutable.Map(v)
    it := vC.Iterator()
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

type tlaValueTuple immutable.List

func NewTLATuple(members ...TLAValue) TLAValue {
    builder := immutable.NewListBuilder()
    for _, member := range members {
        builder.Append(member)
    }
    return TLAValue{tlaValueTuple(*builder.List())}
}

func (v tlaValueTuple) Hash() uint32 {
    vC := immutable.List(v)
    h := fnv.New32()
    it := vC.Iterator()
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

func (v tlaValueTuple) Equal(other TLAValue) bool {
    vC := immutable.List(v)
    oC := other.AsTuple()
    if vC.Len() != oC.Len() {
        return false
    }
    it1, it2 := vC.Iterator(), oC.Iterator()
    for !it1.Done() || !it2.Done() {
        _, elem1 := it1.Next()
        _, elem2 := it2.Next()
        if !elem1.(TLAValue).data.Equal(elem2.(TLAValue)) {
            return false
        }
    }
    return true
}

func (v tlaValueTuple) String() string {
    vC := immutable.List(v)
    builder := strings.Builder{}
    builder.WriteString("<<")
    it := vC.Iterator()
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
