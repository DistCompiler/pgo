package main

import (
	"flag"
	"math/rand"
	"pgo/datatypes"
	"strconv"
	"time"
)

var todo datatypes.Set = datatypes.NewSet([]int{})
var sols datatypes.Set = datatypes.NewSet()
var N int

func Attacks(queens []int, i int, j int) bool {
	return queens[i - 1] == queens[j - 1]
		|| queens[i - 1] - queens[j - 1] == i - j
		|| queens[j - 1] - queens[i - 1] == i - j
}
func IsSolution(queens []int) bool {
	return datatypes.ForAll(func(i int) bool {
				return datatypes.ForAll(func(j int) bool {
							return !Attacks(queens, i, j)
						}, datatypes.Sequence(i + 1, len(queens)))
			}, datatypes.Sequence(1, len(queens) - 1))
}

func main()  {
	rand.Seed(time.Now().UnixNano())
	flag.Parse()
	N, _ = strconv.Atoi(flag.Args()[0])
	
	for !datatypes.NewSet().Equal(todo) {
		{
			var queens []int // PGo inferred type []int
				= todo.ToSlice()[rand.Intn(todo.Size())].([]int)
			var nxtQ int = len(queens) + 1 // PGo inferred type int
			var cols datatypes.Set // PGo inferred type set[int]
				= datatypes.SetConstructor(datatypes.Sequence(1, N), func(c int) bool {
						return !datatypes.Exists(func(i int) bool {
									return Attacks(append(queens, c), i, nxtQ)
								}, datatypes.Sequence(1, len(queens)))
					})
			var exts datatypes.Set // PGo inferred type set[[]int]
				= datatypes.SetImage(func(c int) []int {
						return append(queens, c)
					}, cols)
			if (nxtQ == N) {
				todo = todo.Difference(datatypes.NewSet(queens))
				sols = exts.Union(sols)
			} else {
				todo = exts.Union((todo.Difference(datatypes.NewSet(queens))))
			}
		}
	}
}
