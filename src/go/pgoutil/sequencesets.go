package pgoutil

func Sequence(begin, end int) []int {
	ret := make([]int, end-begin+1)
	for i := 0; i <= end-begin; i++ {
		ret[i] = begin + i
	}
	return ret
}
