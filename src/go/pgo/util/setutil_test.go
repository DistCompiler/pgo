package pgoutil

import (
	"testing"
	"fmt"
)

func TestSetConstructor(t *testing.T) {
	S := NewSet(1, 2, 3, 4)
	assertSetEqual(
		NewSet(2, 3, 4),
		SetConstructor(S, func(i int) bool {
				return i >= 2
			}), t)
	assertSetEqual(
		NewSet(2, 4),
		SetConstructor(S, func(i int) bool {
				return i % 2 == 0
			}), t)
}

func TestSetImage(t *testing.T) {
	S := NewSet(1, 2, 3)
	assertSetEqual(
		NewSet(2, 4, 6),
		SetImage(func(i int) int {
				return i * 2
			}, S), t)
	assertSetEqual(
		NewSet("a", "aa", "aaa"),
		SetImage(func(i int) string {
				ret := ""
				for k := 0; k < i; k++ {
					ret += "a"
				}
				return ret
			}, S), t)

	T := NewSet()
	assertSetEqual(
		NewSet(),
		SetImage(func(i, j int) int {
				return i + j
			}, S, T), t)

	T.Add(5)
	T.Add(6)
	assertSetEqual(
		NewSet(6, 7, 8, 9),
		SetImage(func(i, j int) int {
				return i + j
			}, S, T), t)

	U := NewSet("a")
	assertSetEqual(
		NewSet("15a", "16a", "25a", "26a", "35a", "36a"),
		SetImage(func(i, j int, k string) string {
				return fmt.Sprintf("%v%v%v", i, j, k)
			}, S, T, U), t)
}
