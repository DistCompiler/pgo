package main

import (
	"fmt"
)

var N int

func init() {
	N = 42
}

func main() {
	u := 24
	tmpRange := make([]int, N-1+1)
	for i := 1; i <= N; i++ {
		tmpRange[i-1] = i
	}
	v := tmpRange[0]
	v_init := v
	for {
		if !(u != 0) {
			break
		}
		if u < v {
			u, v = v, u
		}
		u = u - v
	}
	fmt.Printf("%v\n", struct {
		e0 int
		e1 int
		e2 string
		e3 int
	}{24, v_init, "have gcd", v})
}
