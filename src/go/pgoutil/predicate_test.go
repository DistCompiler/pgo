package pgoutil

import (
	"testing"
	"mapset"
)

func TestEmptySets(t *testing.T) {
	// For empty sets, Exists is defined to be false and ForAll is defined to be true.
	S := mapset.NewSet()
	assertEquals(
		false,
		Exists(func(i int) bool {
				return true
			}, S), t)
	assertEquals(
		true,
		ForAll(func(i int) bool {
				return false
			}, S), t)

	T := mapset.NewSet()
	assertEquals(
		false,
		Exists(func(i, j int) bool {
				return true
			}, S), t)
	assertEquals(
		true,
		ForAll(func(i, j int) bool {
				return false
			}, S), t)

	U := mapset.NewSet(1, 2, 3)
	assertEquals(
		false,
		Exists(func(i, j, k int) bool {
				return true
			}, S, T, U), t)
	assertEquals(
		true,
		ForAll(func(i, j, k int) bool {
				return false
			}, S, T, U), t)
}

func TestSimpleExistsForAll(t *testing.T) {
	S := mapset.NewSet(2)
	assertEquals(
		true,
		Exists(func(i int) bool {
				return i >= 2
			}, S), t)
	assertEquals(
		true,
		ForAll(func(i int) bool {
				return i >= 2
			}, S), t)

	S.Add(1)
	assertEquals(
		true,
		Exists(func(i int) bool {
				return i % 2 == 1
			}, S), t)
	assertEquals(
		false,
		ForAll(func(i int) bool {
				return i % 2 == 1
			}, S), t)
}

func TestMultipleSets(t *testing.T) {
	S := mapset.NewSet(1, 2, 3)
	T := mapset.NewSet(4, 5, 6)
	assertEquals(
		true,
		Exists(func(i, j int) bool {
				return j - i == 5
			}, S, T), t)
	assertEquals(
		true,
		ForAll(func(i, j int) bool {
				return j > i
			}, S, T), t)

	U := mapset.NewSet(7, 8, 9)
	assertEquals(
		false,
		Exists(func(i, j, k int) bool {
				return i + j + k > 18
			}, S, T, U), t)
	assertEquals(
		false,
		ForAll(func(i, j, k int) bool {
				return i + j + k > 12
			}, S, T, U), t)
}

func TestChoose(t *testing.T) {
	// For our Choose function, we take the least element that satisfies the predicate.
	// This guarantees the determinism the TLA specifies.
	S := mapset.NewSet("x", "a", "ab")
	assertEquals(
		"a",
		Choose(func(i string) bool {
				return true
			}, S), t)

	S = mapset.NewSet(2, 4, 6, 8, 9)
	assertEquals(
		9,
		Choose(func(i int) bool {
				return i % 2 == 1
			}, S), t)

	S.Add(7)
	assertEquals(
		7,
		Choose(func(i int) bool {
				return i % 2 == 1
			}, S), t)
}
