package tla

import (
	"fmt"
	"math"

	"github.com/benbjohnson/immutable"
)

// this file contains definitions of all PGo's supported TLA+ symbols (that would usually be evaluated by TLC)

// TLC-specific

var TLA_defaultInitValue = TLAValue{}

func TLA_Assert(cond, msg TLAValue) TLAValue {
	require(cond.AsBool(), fmt.Sprintf("TLA+ assertion: %s", msg.AsString()))
	return TLA_TRUE
}

func TLA_ToString(value TLAValue) TLAValue {
	return MakeTLAString(value.String())
}

// eq checks

func TLA_EqualsSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.Equal(rhs))
}

func TLA_NotEqualsSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(!lhs.Equal(rhs))
}

// Boolean-related

var TLA_TRUE = TLAValue{tlaValueBool(true)}
var TLA_FALSE = TLAValue{tlaValueBool(false)}
var TLA_BOOLEAN = MakeTLASet(TLA_TRUE, TLA_FALSE)

// logical AND, OR, and IMPLIES symbols are special-cased in the compiler, because they are short-circuiting

func TLA_LogicalNotSymbol(v TLAValue) TLAValue {
	return MakeTLABool(!v.AsBool())
}

func TLA_EquivSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.AsBool() == rhs.AsBool())
}

// number-related

var TLA_Zero = MakeTLANumber(0)

func TLA_PlusSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLANumber(lhs.AsNumber() + rhs.AsNumber())
}

func TLA_MinusSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLANumber(lhs.AsNumber() - rhs.AsNumber())
}

func TLA_AsteriskSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLANumber(lhs.AsNumber() * rhs.AsNumber())
}

func TLA_SuperscriptSymbol(lhs, rhs TLAValue) TLAValue {
	rawResult := math.Pow(float64(lhs.AsNumber()), float64(rhs.AsNumber()))
	// this is dangerous, annoying numeric territory...
	// TLC reports an overflow when this int32 cast would lose information, but Go silently ... wraps the sign?!?
	// well, Scala silently truncates as well, so eh.
	// for sanity, let's report an overflow as well. if you hit this, your spec probably has issues :)
	result := int32(rawResult)
	require(rawResult <= math.MaxInt32 && rawResult >= math.MinInt32, "integer exponentiation must remain within int32 range")
	return MakeTLANumber(result)
}

func TLA_LessThanOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.AsNumber() <= rhs.AsNumber())
}

func TLA_GreaterThanOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.AsNumber() >= rhs.AsNumber())
}

func TLA_LessThanSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.AsNumber() < rhs.AsNumber())
}

func TLA_GreaterThanSymbol(lhs, rhs TLAValue) TLAValue {
	return MakeTLABool(lhs.AsNumber() > rhs.AsNumber())
}

func TLA_DotDotSymbol(lhs, rhs TLAValue) TLAValue {
	from, to := lhs.AsNumber(), rhs.AsNumber()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	for i := from; i <= to; i++ {
		builder.Set(MakeTLANumber(i), true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_DivSymbol(lhs, rhs TLAValue) TLAValue {
	rhsNum := rhs.AsNumber()
	require(rhsNum != 0, "divisor must not be 0")
	return MakeTLANumber(lhs.AsNumber() / rhsNum)
}

func TLA_PercentSymbol(lhs, rhs TLAValue) TLAValue {
	rhsNum := rhs.AsNumber()
	require(rhsNum > 0, "divisor be greater than 0")
	return MakeTLANumber(lhs.AsNumber() % rhsNum)
}

func TLA_NegationSymbol(v TLAValue) TLAValue {
	return MakeTLANumber(-v.AsNumber())
}

// set-related

func TLA_InSymbol(lhs, rhs TLAValue) TLAValue {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeTLABool(ok)
}

func TLA_NotInSymbol(lhs, rhs TLAValue) TLAValue {
	set := rhs.AsSet()
	_, ok := set.Get(lhs)
	return MakeTLABool(!ok)
}

func TLA_IntersectSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); ok {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_UnionSymbol(lhs, rhs TLAValue) TLAValue {
	bigSet, smallSet := lhs.AsSet(), rhs.AsSet()
	if bigSet.Len() < smallSet.Len() {
		smallSet, bigSet = bigSet, smallSet
	}
	it := smallSet.Iterator()
	for !it.Done() {
		v, _ := it.Next()
		bigSet = bigSet.Set(v, true)
	}
	return TLAValue{&tlaValueSet{bigSet}}
}

func TLA_SubsetOrEqualSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		_, ok := rhsSet.Get(elem)
		if !ok {
			return TLA_FALSE
		}
	}
	return TLA_TRUE
}

func TLA_BackslashSymbol(lhs, rhs TLAValue) TLAValue {
	lhsSet, rhsSet := lhs.AsSet(), rhs.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := lhsSet.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		if _, ok := rhsSet.Get(elem); !ok {
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_PrefixSubsetSymbol(v TLAValue) TLAValue {
	set := v.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	shrinkingSet := set
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		builder.Set(shrinkingSet, true)
		shrinkingSet = shrinkingSet.Delete(elem)
	}
	builder.Set(shrinkingSet, true) // add the empty set
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_PrefixUnionSymbol(v TLAValue) TLAValue {
	setOfSets := v.AsSet()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := setOfSets.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		set := elem.(TLAValue).AsSet()
		innerIt := set.Iterator()
		for !innerIt.Done() {
			elem, _ := it.Next()
			builder.Set(elem, true)
		}
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_IsFiniteSet(v TLAValue) TLAValue {
	_ = v.AsSet() // it should at least _be_ a set, even if we're sure it's finite
	return TLA_TRUE
}

func TLA_Cardinality(v TLAValue) TLAValue {
	return MakeTLANumber(int32(v.AsSet().Len()))
}

// sequence / tuple-related

func TLA_Seq(v TLAValue) TLAValue {
	set := v.AsSet()
	// move all the elements onto a slice for easier handling
	var elems []TLAValue
	it := set.Iterator()
	for !it.Done() {
		elem, _ := it.Next()
		elems = append(elems, elem.(TLAValue))
	}

	// prepare to build a set of tuples
	builder := immutable.NewMapBuilder(TLAValueHasher{})

	// special-case the empty set, as the main process doesn't handle it
	if len(elems) == 0 {
		builder.Set(MakeTLATuple(), true)
	} else {
		// generate permutations using Heap's algorithm
		var generatePermutations func(k int)
		generatePermutations = func(k int) {
			if k == 1 {
				// store a new tuple in the set
				builder.Set(MakeTLATuple(elems...), true)
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

	return TLAValue{&tlaValueSet{builder.Map()}}
}

func TLA_Len(v TLAValue) TLAValue {
	return MakeTLANumber(int32(v.AsTuple().Len()))
}

func TLA_OSymbol(lhs, rhs TLAValue) TLAValue {
	lhsTuple, rhsTuple := lhs.AsTuple(), rhs.AsTuple()
	it := rhsTuple.Iterator()
	for !it.Done() {
		_, elem := it.Next()
		lhsTuple = lhsTuple.Append(elem)
	}
	return TLAValue{&tlaValueTuple{lhsTuple}}
}

func TLA_Append(lhs, rhs TLAValue) TLAValue {
	return TLAValue{&tlaValueTuple{lhs.AsTuple().Append(rhs)}}
}

func TLA_Head(v TLAValue) TLAValue {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Head, tuple must not be empty")
	return tuple.Get(0).(TLAValue)
}

func TLA_Tail(v TLAValue) TLAValue {
	tuple := v.AsTuple()
	require(tuple.Len() > 0, "to call Tail, tuple must not be empty")
	return TLAValue{&tlaValueTuple{tuple.Slice(1, tuple.Len())}}
}

func TLA_SubSeq(v, m, n TLAValue) TLAValue {
	tuple := v.AsTuple()
	from, to := int(m.AsNumber()), int(n.AsNumber())
	if from > to {
		return TLAValue{&tlaValueTuple{immutable.NewList()}}
	}
	require(from <= to && from >= 1 && to <= tuple.Len(), "to call SubSeq, from and to indices must be in-bounds")
	return TLAValue{&tlaValueTuple{tuple.Slice(from-1, to)}}
}

// TODO: TLA_SelectSeq, uses predicate
func TLA_SelectSeq(a, b TLAValue) TLAValue {
	panic("implement me")
}

// function-related

func TLA_ColonGreaterThanSymbol(lhs, rhs TLAValue) TLAValue {
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	builder.Set(lhs, rhs)
	return TLAValue{&tlaValueFunction{builder.Map()}}
}

func TLA_DoubleAtSignSymbol(lhs, rhs TLAValue) TLAValue {
	lhsFn, rhsFh := lhs.AsFunction(), rhs.AsFunction()
	it := rhsFh.Iterator()
	for !it.Done() {
		key, value := it.Next()
		lhsFn = lhsFn.Set(key, value)
	}
	return TLAValue{&tlaValueFunction{lhsFn}}
}

func TLA_DomainSymbol(v TLAValue) TLAValue {
	fn := v.AsFunction()
	builder := immutable.NewMapBuilder(TLAValueHasher{})
	it := fn.Iterator()
	for !it.Done() {
		domainElem, _ := it.Next()
		builder.Set(domainElem, true)
	}
	return TLAValue{&tlaValueSet{builder.Map()}}
}
