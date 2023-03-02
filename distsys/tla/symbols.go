package tla

import (
	"fmt"
	"math"

	"github.com/benbjohnson/immutable"
)

// this file contains definitions of all PGo's supported TLA+ Modules (that would usually be evaluated by TLC)

// TLC-specific

var ModuledefaultInitValue = Value{}

func ModuleAssert(cond, msg Value) Value {
	require(cond.AsBool(), fmt.Sprintf("TLA+ assertion: %s", msg.AsString()))
	return ModuleTRUE
}

func ModuleToString(value Value) Value {
	return MakeString(value.String())
}

// eq checks

func ModuleEqualsSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.Equal(rhs))
}

func ModuleNotEqualsSymbol(lhs, rhs Value) Value {
	return MakeBool(!lhs.Equal(rhs))
}

// Boolean-related

var ModuleTRUE = Value{valueBool(true)}
var ModuleFALSE = Value{valueBool(false)}
var ModuleBOOLEAN = MakeSet(ModuleTRUE, ModuleFALSE)

// logical AND, OR, and IMPLIES Modules are special-cased in the compiler, because they are short-circuiting

func ModuleLogicalNotSymbol(v Value) Value {
	return MakeBool(!v.AsBool())
}

func ModuleEquivSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsBool() == rhs.AsBool())
}

// number-related

var ModuleZero = MakeNumber(0)

func ModulePlusSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() + rhs.AsNumber())
}

func ModuleMinusSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() - rhs.AsNumber())
}

func ModuleAsteriskSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() * rhs.AsNumber())
}

func ModuleSuperscriptSymbol(lhs, rhs Value) Value {
	rawResult := math.Pow(float64(lhs.AsNumber()), float64(rhs.AsNumber()))
	// this is dangerous, annoying numeric territory...
	// TLC reports an overflow when this int32 cast would lose information, but Go silently ... wraps the sign?!?
	// well, Scala silently truncates as well, so eh.
	// for sanity, let's report an overflow as well. if you hit this, your spec probably has issues :)
	result := int32(rawResult)
	require(rawResult <= math.MaxInt32 && rawResult >= math.MinInt32, "integer exponentiation must remain within int32 range")
	return MakeNumber(result)
}

func ModuleLessThanOrEqualSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() <= rhs.AsNumber())
}

func ModuleGreaterThanOrEqualSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() >= rhs.AsNumber())
}

func ModuleLessThanSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() < rhs.AsNumber())
}

func ModuleGreaterThanSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() > rhs.AsNumber())
}

func ModuleDotDotSymbol(lhs, rhs Value) Value {
	from, to := lhs.AsNumber(), rhs.AsNumber()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	for i := from; i <= to; i++ {
		builder.Set(MakeNumber(i), true)
	}
	return Value{&valueSet{builder.Map()}}
}

func ModuleDivSymbol(lhs, rhs Value) Value {
	rhsNum := rhs.AsNumber()
	require(rhsNum != 0, "divisor must not be 0")
	return MakeNumber(lhs.AsNumber() / rhsNum)
}

func ModulePercentSymbol(lhs, rhs Value) Value {
	rhsNum := rhs.AsNumber()
	require(rhsNum > 0, "divisor be greater than 0")
	return MakeNumber(lhs.AsNumber() % rhsNum)
}

func ModuleNegationSymbol(v Value) Value {
	return MakeNumber(-v.AsNumber())
}

// set-related

func ModuleInSymbol(lhs, rhs Value) Value {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeBool(ok)
}

func ModuleNotInSymbol(lhs, rhs Value) Value {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeBool(!ok)
}

func ModuleIntersectSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		if _, ok := rhsSet.Get(elem); ok {
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func ModuleUnionSymbol(lhs, rhs Value) Value {
	bigSet, smallSet := lhs.AsSet(), rhs.AsSet()
	if bigSet.Len() < smallSet.Len() {
		smallSet, bigSet = bigSet, smallSet
	}
	it := smallSet.Iterator()
	for !it.Done() {
		v, _, _ := it.Next()
		bigSet = bigSet.Set(v, true)
	}
	return Value{&valueSet{bigSet}}
}

func ModuleSubsetOrEqualSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		_, ok := rhsSet.Get(elem)
		if !ok {
			return ModuleFALSE
		}
	}
	return ModuleTRUE
}

func ModuleBackslashSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		if _, ok := rhsSet.Get(elem); !ok {
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func ModulePrefixSubsetSymbol(v Value) Value {
	set := v.AsSet()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	shrinkingSet := set
	it := set.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		builder.Set(MakeSetFromMap(shrinkingSet), true)
		shrinkingSet = shrinkingSet.Delete(elem)
	}
	builder.Set(MakeSetFromMap(shrinkingSet), true) // add the empty set
	return Value{&valueSet{builder.Map()}}
}

func ModulePrefixUnionSymbol(v Value) Value {
	setOfSets := v.AsSet()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	it := setOfSets.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		set := elem.AsSet()
		innerIt := set.Iterator()
		for !innerIt.Done() {
			elem, _, _ := it.Next()
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func ModuleIsFiniteSet(v Value) Value {
	_ = v.AsSet() // it should at least _be_ a set, even if we're sure it's finite
	return ModuleTRUE
}

func ModuleCardinality(v Value) Value {
	return MakeNumber(int32(v.AsSet().Len()))
}

// sequence / tuple-related

func ModuleSeq(v Value) Value {
	set := v.AsSet()
	// move all the elements onto a slice for easier handling
	var elems []Value
	it := set.Iterator()
	for !it.Done() {
		elem, _, _ := it.Next()
		elems = append(elems, elem)
	}

	// prepare to build a set of tuples
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})

	// special-case the empty set, as the main process doesn't handle it
	if len(elems) == 0 {
		builder.Set(MakeTuple(), true)
	} else {
		// generate permutations using Heap's algorithm
		var generatePermutations func(k int)
		generatePermutations = func(k int) {
			if k == 1 {
				// store a new tuple in the set
				builder.Set(MakeTuple(elems...), true)
			} else {
				generatePermutations(k - 1)

				for i := 0; i < k-1; i += 1 {
					if k%2 == 0 {
						elems[i], elems[k-1] = elems[k-1], elems[i]
					} else {
						elems[0], elems[k-1] = elems[k-1], elems[0]
					}
					generatePermutations(k - 1)
				}
			}
		}

		generatePermutations(len(elems))
	}

	return Value{&valueSet{builder.Map()}}
}

func ModuleLen(v Value) Value {
	return MakeNumber(int32(v.AsTuple().Len()))
}

func ModuleOSymbol(lhs, rhs Value) Value {
	lhsTuple, rhsTuple := lhs.AsTuple(), rhs.AsTuple()
	it := rhsTuple.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		lhsTuple = lhsTuple.Append(elem)
	}
	return Value{&valueTuple{lhsTuple}}
}

func ModuleAppend(lhs, rhs Value) Value {
	return Value{&valueTuple{lhs.AsTuple().Append(rhs)}}
}

func ModuleHead(v Value) Value {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Head, tuple must not be empty")
	return tuple.Get(0)
}

func ModuleTail(v Value) Value {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Tail, tuple must not be empty")
	return Value{&valueTuple{tuple.Slice(1, tuple.Len())}}
}

func ModuleSubSeq(v, m, n Value) Value {
	tuple := v.AsTuple()
	from, to := int(m.AsNumber()), int(n.AsNumber())
	if from > to {
		return Value{&valueTuple{immutable.NewList[Value]()}}
	}
	require(from <= to && from >= 1 && to <= tuple.Len(), "to call SubSeq, from and to indices must be in-bounds")
	return Value{&valueTuple{tuple.Slice(from-1, to)}}
}

// TODO: ModuleSelectSeq, uses predicate
func ModuleSelectSeq(a, b Value) Value {
	panic("implement me")
}

// function-related

func ModuleColonGreaterThanSymbol(lhs, rhs Value) Value {
	builder := immutable.NewMapBuilder[Value, Value](ValueHasher{})
	builder.Set(lhs, rhs)
	return Value{&valueFunction{builder.Map()}}
}

func ModuleDoubleAtSignSymbol(lhs, rhs Value) Value {
	lhsFn, rhsFh := lhs.AsFunction(), rhs.AsFunction()
	it := rhsFh.Iterator()
	for !it.Done() {
		key, value, _ := it.Next()
		lhsFn = lhsFn.Set(key, value)
	}
	return Value{&valueFunction{lhsFn}}
}

func ModuleDomainSymbol(v Value) Value {
	fn := v.AsFunction()
	builder := immutable.NewMapBuilder[Value, bool](ValueHasher{})
	it := fn.Iterator()
	for !it.Done() {
		domainElem, _, _ := it.Next()
		builder.Set(domainElem, true)
	}
	return Value{&valueSet{builder.Map()}}
}
