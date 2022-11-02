package tla

import (
	"fmt"
	"math"

	"github.com/benbjohnson/immutable"
)

// this file contains definitions of all PGo's supported TLA+ Symbol_s (that would usually be evaluated by TLC)

// TLC-specific

var Symbol_defaultInitValue = Value{}

func Symbol_Assert(cond, msg Value) Value {
	require(cond.AsBool(), fmt.Sprintf("TLA+ assertion: %s", msg.AsString()))
	return Symbol_TRUE
}

func Symbol_ToString(value Value) Value {
	return MakeString(value.String())
}

// eq checks

func Symbol_EqualsSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.Equal(rhs))
}

func Symbol_NotEqualsSymbol(lhs, rhs Value) Value {
	return MakeBool(!lhs.Equal(rhs))
}

// Boolean-related

var Symbol_TRUE = Value{valueBool(true)}
var Symbol_FALSE = Value{valueBool(false)}
var Symbol_BOOLEAN = MakeSet(Symbol_TRUE, Symbol_FALSE)

// logical AND, OR, and IMPLIES Symbol_s are special-cased in the compiler, because they are short-circuiting

func Symbol_LogicalNotSymbol(v Value) Value {
	return MakeBool(!v.AsBool())
}

func Symbol_EquivSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsBool() == rhs.AsBool())
}

// number-related

var Symbol_Zero = MakeNumber(0)

func Symbol_PlusSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() + rhs.AsNumber())
}

func Symbol_MinusSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() - rhs.AsNumber())
}

func Symbol_AsteriskSymbol(lhs, rhs Value) Value {
	return MakeNumber(lhs.AsNumber() * rhs.AsNumber())
}

func Symbol_SuperscriptSymbol(lhs, rhs Value) Value {
	rawResult := math.Pow(float64(lhs.AsNumber()), float64(rhs.AsNumber()))
	// this is dangerous, annoying numeric territory...
	// TLC reports an overflow when this int32 cast would lose information, but Go silently ... wraps the sign?!?
	// well, Scala silently truncates as well, so eh.
	// for sanity, let's report an overflow as well. if you hit this, your spec probably has issues :)
	result := int32(rawResult)
	require(rawResult <= math.MaxInt32 && rawResult >= math.MinInt32, "integer exponentiation must remain within int32 range")
	return MakeNumber(result)
}

func Symbol_LessThanOrEqualSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() <= rhs.AsNumber())
}

func Symbol_GreaterThanOrEqualSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() >= rhs.AsNumber())
}

func Symbol_LessThanSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() < rhs.AsNumber())
}

func Symbol_GreaterThanSymbol(lhs, rhs Value) Value {
	return MakeBool(lhs.AsNumber() > rhs.AsNumber())
}

func Symbol_DotDotSymbol(lhs, rhs Value) Value {
	from, to := lhs.AsNumber(), rhs.AsNumber()
	builder := immutable.NewMapBuilder(ValueHasher{})
	for i := from; i <= to; i++ {
		builder.Set(MakeNumber(i), true)
	}
	return Value{&valueSet{builder.Map()}}
}

func Symbol_DivSymbol(lhs, rhs Value) Value {
	rhsNum := rhs.AsNumber()
	require(rhsNum != 0, "divisor must not be 0")
	return MakeNumber(lhs.AsNumber() / rhsNum)
}

func Symbol_PercentSymbol(lhs, rhs Value) Value {
	rhsNum := rhs.AsNumber()
	require(rhsNum > 0, "divisor be greater than 0")
	return MakeNumber(lhs.AsNumber() % rhsNum)
}

func Symbol_NegationSymbol(v Value) Value {
	return MakeNumber(-v.AsNumber())
}

// set-related

func Symbol_InSymbol(lhs, rhs Value) Value {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeBool(ok)
}

func Symbol_NotInSymbol(lhs, rhs Value) Value {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeBool(!ok)
}

func Symbol_IntersectSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(ValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); ok {
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func Symbol_UnionSymbol(lhs, rhs Value) Value {
	bigSet, smallSet := lhs.AsSet(), rhs.AsSet()
	if bigSet.Len() < smallSet.Len() {
		smallSet, bigSet = bigSet, smallSet
	}
	it := smallSet.Iterator()
	for !it.Done() {
		v, _ := it.Next()
		bigSet = bigSet.Set(v, true)
	}
	return Value{&valueSet{bigSet}}
}

func Symbol_SubsetOrEqualSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		_, ok := rhsSet.Get(elem)
		if !ok {
			return Symbol_FALSE
		}
	}
	return Symbol_TRUE
}

func Symbol_BackslashSymbol(lhs, rhs Value) Value {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(ValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); !ok {
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func Symbol_PrefixSubsetSymbol(v Value) Value {
	set := v.AsSet()
	builder := immutable.NewMapBuilder(ValueHasher{})
	shrinkingSet := set
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		builder.Set(shrinkingSet, true)
		shrinkingSet = shrinkingSet.Delete(elem)
	}
	builder.Set(shrinkingSet, true) // add the empty set
	return Value{&valueSet{builder.Map()}}
}

func Symbol_PrefixUnionSymbol(v Value) Value {
	setOfSets := v.AsSet()
	builder := immutable.NewMapBuilder(ValueHasher{})
	it := setOfSets.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		set := elem.(Value).AsSet()
		innerIt := set.Iterator()
		for !innerIt.Done() {
			elem, _ := it.Next()
			builder.Set(elem, true)
		}
	}
	return Value{&valueSet{builder.Map()}}
}

func Symbol_IsFiniteSet(v Value) Value {
	_ = v.AsSet() // it should at least _be_ a set, even if we're sure it's finite
	return Symbol_TRUE
}

func Symbol_Cardinality(v Value) Value {
	return MakeNumber(int32(v.AsSet().Len()))
}

// sequence / tuple-related

func Symbol_Seq(v Value) Value {
	set := v.AsSet()
	// move all the elements onto a slice for easier handling
	var elems []Value
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		elems = append(elems, elem.(Value))
	}

	// prepare to build a set of tuples
	builder := immutable.NewMapBuilder(ValueHasher{})

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

func Symbol_Len(v Value) Value {
	return MakeNumber(int32(v.AsTuple().Len()))
}

func Symbol_OSymbol(lhs, rhs Value) Value {
	lhsTuple, rhsTuple := lhs.AsTuple(), rhs.AsTuple()
	it := rhsTuple.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		lhsTuple = lhsTuple.Append(elem)
	}
	return Value{&valueTuple{lhsTuple}}
}

func Symbol_Append(lhs, rhs Value) Value {
	return Value{&valueTuple{lhs.AsTuple().Append(rhs)}}
}

func Symbol_Head(v Value) Value {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Head, tuple must not be empty")
	return tuple.Get(0).(Value)
}

func Symbol_Tail(v Value) Value {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Tail, tuple must not be empty")
	return Value{&valueTuple{tuple.Slice(1, tuple.Len())}}
}

func Symbol_SubSeq(v, m, n Value) Value {
	tuple := v.AsTuple()
	from, to := int(m.AsNumber()), int(n.AsNumber())
	if from > to {
		return Value{&valueTuple{immutable.NewList()}}
	}
	require(from <= to && from >= 1 && to <= tuple.Len(), "to call SubSeq, from and to indices must be in-bounds")
	return Value{&valueTuple{tuple.Slice(from-1, to)}}
}

// TODO: Symbol_SelectSeq, uses predicate
func Symbol_SelectSeq(a, b Value) Value {
	panic("implement me")
}

// function-related

func Symbol_ColonGreaterThanSymbol(lhs, rhs Value) Value {
	builder := immutable.NewMapBuilder(ValueHasher{})
	builder.Set(lhs, rhs)
	return Value{&valueFunction{builder.Map()}}
}

func Symbol_DoubleAtSignSymbol(lhs, rhs Value) Value {
	lhsFn, rhsFh := lhs.AsFunction(), rhs.AsFunction()
	it := rhsFh.Iterator()
	for !it.Done() {
		key, value := it.Next()
		lhsFn = lhsFn.Set(key, value)
	}
	return Value{&valueFunction{lhsFn}}
}

func Symbol_DomainSymbol(v Value) Value {
	fn := v.AsFunction()
	builder := immutable.NewMapBuilder(ValueHasher{})
	it := fn.Iterator()
	for !it.Done() {
		domainElem, _ := it.Next()
		builder.Set(domainElem, true)
	}
	return Value{&valueSet{builder.Map()}}
}
