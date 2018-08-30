package main

import (
	"fmt"
	"sort"
)

var N int

func init() {
	N = 8
}

func Attacks(queens []int, i int, j int) bool {
	return queens[i-1] == queens[j-1] || queens[i-1]-queens[j-1] == i-j || queens[j-1]-queens[i-1] == i-j
}

func main() {
	todo := [][]int{[]int{}}
	sols := [][]int{}
	for {
		if !(len(todo) != 0) {
			break
		}
		queens := todo[0]
		nxtQ := len(queens) + 1
		tmpSet := make([]int, 0)
		tmpRange := make([]int, N-1+1)
		for i := 1; i <= N; i++ {
			tmpRange[i-1] = i
		}
		for _, c := range tmpRange {
			exists := false
			tmpRange0 := make([]int, len(queens)-1+1)
			for i := 1; i <= len(queens); i++ {
				tmpRange0[i-1] = i
			}
			for _, i := range tmpRange0 {
				tmpSlice := make([]int, len(queens), len(queens)+1)
				copy(tmpSlice, queens)
				tmpSlice = append(tmpSlice, c)
				if Attacks(tmpSlice, i, nxtQ) {
					exists = true
					break
				}
			}
			if !exists {
				tmpSet = append(tmpSet, c)
			}
		}
		cols := tmpSet
		tmpSet0 := make([][]int, 0)
		for _, c := range cols {
			tmpSlice := make([]int, len(queens), len(queens)+1)
			copy(tmpSlice, queens)
			tmpSlice = append(tmpSlice, c)
			tmpSet0 = append(tmpSet0, tmpSlice)
		}
		sort.Slice(tmpSet0, func(i int, j int) bool {
			less := len(tmpSet0[i]) < len(tmpSet0[j])
			if len(tmpSet0[i]) == len(tmpSet0[j]) {
				for i0 := 0; i0 < len(tmpSet0[i]); i0++ {
					less = tmpSet0[i][i0] < tmpSet0[j][i0]
					if tmpSet0[i][i0] != tmpSet0[j][i0] {
						break
					}
				}
			}
			return less
		})
		if len(tmpSet0) > 1 {
			previousValue := tmpSet0[0]
			currentIndex := 1
			for _, v := range tmpSet0[1:] {
				eq := len(previousValue) == len(v)
				if eq {
					for i0 := 0; i0 < len(previousValue); i0++ {
						eq = previousValue[i0] == v[i0]
						if !eq {
							break
						}
					}
				}
				if !eq {
					tmpSet0[currentIndex] = v
					currentIndex++
				}
				previousValue = v
			}
			tmpSet0 = tmpSet0[:currentIndex]
		}
		exts := tmpSet0
		if nxtQ == N {
			tmpSet1 := make([][]int, 0, len(todo))
			for _, v := range todo {
				eq := len(v) == len(queens)
				if eq {
					for i0 := 0; i0 < len(v); i0++ {
						eq = v[i0] == queens[i0]
						if !eq {
							break
						}
					}
				}
				if !eq {
					tmpSet1 = append(tmpSet1, v)
				}
			}
			todo = tmpSet1
			tmpSet2 := make([][]int, len(sols), len(sols)+len(exts))
			copy(tmpSet2, sols)
			tmpSet2 = append(tmpSet2, exts...)
			sort.Slice(tmpSet2, func(i0 int, j0 int) bool {
				less0 := len(tmpSet2[i0]) < len(tmpSet2[j0])
				if len(tmpSet2[i0]) == len(tmpSet2[j0]) {
					for i1 := 0; i1 < len(tmpSet2[i0]); i1++ {
						less0 = tmpSet2[i0][i1] < tmpSet2[j0][i1]
						if tmpSet2[i0][i1] != tmpSet2[j0][i1] {
							break
						}
					}
				}
				return less0
			})
			if len(tmpSet2) > 1 {
				previousValue := tmpSet2[0]
				currentIndex := 1
				for _, v := range tmpSet2[1:] {
					eq := len(previousValue) == len(v)
					if eq {
						for i1 := 0; i1 < len(previousValue); i1++ {
							eq = previousValue[i1] == v[i1]
							if !eq {
								break
							}
						}
					}
					if !eq {
						tmpSet2[currentIndex] = v
						currentIndex++
					}
					previousValue = v
				}
				tmpSet2 = tmpSet2[:currentIndex]
			}
			sols = tmpSet2
		} else {
			tmpSet1 := make([][]int, 0, len(todo))
			for _, v := range todo {
				eq := len(v) == len(queens)
				if eq {
					for i0 := 0; i0 < len(v); i0++ {
						eq = v[i0] == queens[i0]
						if !eq {
							break
						}
					}
				}
				if !eq {
					tmpSet1 = append(tmpSet1, v)
				}
			}
			tmpSet2 := make([][]int, len(tmpSet1), len(tmpSet1)+len(exts))
			copy(tmpSet2, tmpSet1)
			tmpSet2 = append(tmpSet2, exts...)
			sort.Slice(tmpSet2, func(i0 int, j0 int) bool {
				less0 := len(tmpSet2[i0]) < len(tmpSet2[j0])
				if len(tmpSet2[i0]) == len(tmpSet2[j0]) {
					for i1 := 0; i1 < len(tmpSet2[i0]); i1++ {
						less0 = tmpSet2[i0][i1] < tmpSet2[j0][i1]
						if tmpSet2[i0][i1] != tmpSet2[j0][i1] {
							break
						}
					}
				}
				return less0
			})
			if len(tmpSet2) > 1 {
				previousValue := tmpSet2[0]
				currentIndex := 1
				for _, v := range tmpSet2[1:] {
					eq := len(previousValue) == len(v)
					if eq {
						for i1 := 0; i1 < len(previousValue); i1++ {
							eq = previousValue[i1] == v[i1]
							if !eq {
								break
							}
						}
					}
					if !eq {
						tmpSet2[currentIndex] = v
						currentIndex++
					}
					previousValue = v
				}
				tmpSet2 = tmpSet2[:currentIndex]
			}
			todo = tmpSet2
		}
	}
	fmt.Printf("%v\n", sols)
}
