package tla

import (
	"fmt"
	"github.com/benbjohnson/immutable"
)

// this file contains all definitions of PGo's supported expressions which are
// built-in syntax (not the ones that require using `EXTENDS`)

func TLAQuantifiedUniversal(setVals []TLAValue, pred func([]TLAValue) bool) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]TLAValue, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _ := it.Next()
			predArgs[idx] = elem.(TLAValue)
			if !helper(idx + 1) {
				return false
			}
		}
		return true
	}

	return MakeTLABool(helper(0))
}

func TLAQuantifiedExistential(setVals []TLAValue, pred func([]TLAValue) bool) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	predArgs := make([]TLAValue, len(sets))

	var helper func(idx int) bool
	helper = func(idx int) bool {
		if idx == len(sets) {
			return pred(predArgs)
		}

		it := sets[idx].Iterator()
		for !it.Done() {
			elem, _ := it.Next()
			predArgs[idx] = elem.(TLAValue)
			if helper(idx + 1) {
				return true
			}
		}
		return false
	}

	return MakeTLABool(helper(0))
}

func TLASetRefinement(setVal TLAValue, pred func(TLAValue) bool) TLAValue {
	set := setVal.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if pred(elem.(TLAValue)) {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLASetComprehension(setVals []TLAValue, body func([]TLAValue) TLAValue) TLAValue {
	var sets []*immutable.Map
	for _, val := range setVals {
		sets = append(sets, val.AsSet())
	}

	builder := immutable.NewMapBuilder(TLAValueHasher{})
	bodyArgs := make([]TLAValue, len(sets))

	var helper func(idx int)
	helper = func(idx int) {
		if idx == len(sets) {
			builder.Set(body(bodyArgs), true)
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
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLACrossProduct(vs ...TLAValue) TLAValue {
	var sets []*immutable.Map
	for _, v := range vs {
		sets = append(sets, v.AsSet())
	}

	builder := immutable.NewMapBuilder(TLAValueHasher{})

	var helper func(tuple *immutable.List, idx int)
	helper = func(tuple *immutable.List, idx int) {
		if idx < len(sets) {
			set := sets[idx]
			it := set.Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				helper(tuple.Append(elem), idx+1)
			}
		} else {
			builder.Set(tuple, true)
		}
	}

	helper(immutable.NewList(), 0)

	return TLAValue{&tlaValueSet{builder.Map()}}
}

type TLAFunctionSubstitutionRecord struct {
	Keys  []TLAValue
	Value func(anchor TLAValue) TLAValue
}

func TLAFunctionSubstitution(source TLAValue, substitutions []TLAFunctionSubstitutionRecord) TLAValue {
	var keysHelper func(source TLAValue, keys []TLAValue, value func(anchor TLAValue) TLAValue) TLAValue
	keysHelper = func(source TLAValue, keys []TLAValue, value func(anchor TLAValue) TLAValue) TLAValue {
		if len(keys) == 0 {
			return value(source)
		} else {
			if source.IsFunction() {
				sourceFn := source.AsFunction()
				val, keyOk := sourceFn.Get(keys[0])
				require(keyOk, "invalid key during function substitution")
				sourceFn = sourceFn.Set(keys[0], keysHelper(val.(TLAValue), keys[1:], value))
				return TLAValue{&tlaValueFunction{sourceFn}}
			} else if source.IsTuple() {
				sourceTuple := source.AsTuple()
				idx := int(keys[0].AsNumber())
				require(idx >= 1 && idx <= sourceTuple.Len(), "invalid key during function substitution")
				val := sourceTuple.Get(idx - 1)
				sourceTuple = sourceTuple.Set(idx-1, keysHelper(val.(TLAValue), keys[1:], value))
				return TLAValue{&tlaValueTuple{sourceTuple}}
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

func TLAChoose(setVal TLAValue, pred func(value TLAValue) bool) TLAValue {
	set := setVal.AsSet()
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		elemV := elem.(TLAValue)
		if pred(elemV) {
			return elemV
		}
	}

	require(false, "CHOOSE could not be satisfied; entire set of candidates exhausted")
	panic("UNREACHABLE")
}
