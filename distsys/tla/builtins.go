package tla

import (
	"fmt"

	"github.com/benbjohnson/immutable"
)

// this file contains all definitions of PGo's supported expressions which are
// built-in syntax (not the ones that require using `EXTENDS`)

func QuantifiedUniversal(setVals []Value, pred func([]Value) bool) Value {
	var sets []*immutable.Map[Value, bool]
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]Value, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _, _ := it.Next()
			predArgs[idx] = elem
			if !helper(idx + 1) {
				return false
			}
		}
		return true
	}

	return MakeBool(helper(0))
}

func QuantifiedExistential(setVals []Value, pred func([]Value) bool) Value {
	var sets []*immutable.Map[Value, bool]
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]Value, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _, _ := it.Next()
			predArgs[idx] = elem
			if helper(idx + 1) {
				return true
			}
		}
		return false
	}

	return MakeBool(helper(0))
}

func SetRefinement(setVal Value, pred func(Value) bool) Value {
	set := setVal.AsSet()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	it := set.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		if pred(elem) {
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func SetComprehension(setVals []Value, body func([]Value) Value) Value {
	var sets []*immutable.Map[Value, bool]
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	bodyArgs := make([]Value, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(sets) {
			builder.Set(body(bodyArgs), true)
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
	return Value{&valueSet{builder.Map()}}
}

func CrossProduct(vs ...Value) Value {
	var sets []*immutable.Map[Value, bool]
	for _, v := range vs {
		sets = append(sets, v.AsSet())
	}

	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})

	var helper func(tuple *immutable.List[Value], idx int)
	helper = func(tuple *immutable.List[Value], idx int) {
		if idx < len(sets) {
			set := sets[idx]
			it := set.Iterator()
			for !it.Done() {
				elem, _, _ := it.Next()
				helper(tuple.Append(elem), idx+1)
			}
		} else {
			builder.Set(MakeTupleFromList(tuple), true)
		}
	}

	helper(immutable.NewList[Value](), 0)

	return Value{&valueSet{builder.Map()}}
}

type FunctionSubstitutionRecord struct {
	Keys  []Value
	Value func(anchor Value) Value
}

func FunctionSubstitution(source Value, substitutions []FunctionSubstitutionRecord) Value {
	var keysHelper func(source Value, keys []Value, value func(anchor Value) Value) Value
	keysHelper = func(source Value, keys []Value, value func(anchor Value) Value) Value {
		if len(keys) == 0 {
			return value(source)
		} else {
			if source.IsFunction() {
				sourceFn := source.AsFunction()
				val, keyOk := sourceFn.Get(keys[0])
				require(keyOk, "invalid key during function substitution")
				sourceFn = sourceFn.Set(keys[0], keysHelper(val, keys[1:], value))
				return Value{&valueFunction{sourceFn}}
			} else if source.IsTuple() {
				sourceTuple := source.AsTuple()
				idx := int(keys[0].AsNumber())
				require(idx >= 1 && idx <= sourceTuple.Len(), "invalid key during function substitution")
				val := sourceTuple.Get(idx - 1)
				sourceTuple = sourceTuple.Set(idx-1, keysHelper(val, keys[1:], value))
				return Value{&valueTuple{sourceTuple}}
			} else {
				panic(fmt.Errorf("%w: during function substitution, %v was neither a function nor a tuple", ErrTLAType, source))
			}
		}
	}
	for _, substitution := range substitutions {
		source = keysHelper(source, substitution.Keys, substitution.Value)
	}
	return source
}

func Choose(setVal Value, pred func(value Value) bool) Value {
	set := setVal.AsSet()
	it := set.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		elemV := elem
		if pred(elemV) {
			return elemV
		}
	}

	require(false, "CHOOSE could not be satisfied; entire set of candidates exhausted")
	panic("UNREACHABLE")
}
