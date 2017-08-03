package main

import (
	"flag"
	"math/rand"
	"pgoutil"
	"strconv"
	"time"
)

var todo pgoutil.Set = pgoutil.NewSet([]int{})
var sols pgoutil.Set = pgoutil.NewSet()
var N int

func Attacks(queens []int, i int, j int) bool {
	return queens[i - 1] == queens[j - 1] || queens[i - 1] - queens[j - 1] == i - j || queens[j - 1] - queens[i - 1] == i - j
}
func IsSolution(queens []int) bool {
	return pgoutil.ForAll(func(i int) bool {
				return pgoutil.ForAll(func(j int) bool {
							return !Attacks(queens, i, j)
						}, pgoutil.Sequence(i + 1, len(queens)))
			}, pgoutil.Sequence(1, len(queens) - 1))
}

func main()  {
	rand.Seed(time.Now().UnixNano())
	flag.Parse()
	N, _ = strconv.Atoi(flag.Args()[0])
	
	for !pgoutil.NewSet().Equal(todo) {
		{
			queens := todo.ToSlice()[rand.Intn(todo.Size())].([]int)
			nxtQ := len(queens) + 1
			cols := pgoutil.SetConstructor(pgoutil.Sequence(1, N), func(c int) bool {
					return !pgoutil.Exists(func(i int) bool {
								return Attacks(append(queens, c), i, nxtQ)
							}, pgoutil.Sequence(1, len(queens)))
				})
			exts := pgoutil.SetImage(func(c int) []int {
					return append(queens, c)
				}, cols)
			if (nxtQ == N) {
				todo = todo.Difference(pgoutil.NewSet(queens))
				sols = exts.Union(sols)
			} else {
				todo = exts.Union((todo.Difference(pgoutil.NewSet(queens))))
			}
		}
	}
}
