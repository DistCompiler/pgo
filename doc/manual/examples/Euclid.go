package main

import (
	"flag"
	"fmt"
	"pgo/datatypes"
	"strconv"
)

var v int      // PGo inferred type int
var u int      // PGo inferred type int
var v_init int // PGo inferred type int
var N int

func main() {
	flag.Parse()
	N, _ = strconv.Atoi(flag.Args()[0])

	for v_interface := range datatypes.Sequence(1, N).Iter() {
		v = v_interface.(int)
		u = 24
		v_init = v
		for u != 0 {
			if u < v {
				u_new := v
				v_new := u
				u = u_new
				v = v_new
			}
			u = u - v
		}
		fmt.Printf("%v %v %v %v\n", 24, v_init, "have gcd", v)
	}
}
