package pgoutil

func Sequence(begin, end int) Set {
	ret := NewSet()
	for i := 0; i <= end-begin; i++ {
		ret.Add(begin + i)
	}
	return ret
}
