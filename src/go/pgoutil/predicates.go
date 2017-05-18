package pgoutil

import "mapset"

func Exists(S mapset.Set, P func(interface{}) bool) bool {
	for x := range S.Iter() {
		if P(x) {
			return true
		}
	}
	return false
}

func ForAll(S mapset.Set, P func(interface{}) bool) bool {
	for x := range S.Iter() {
		if !P(x) {
			return false
		}
	}
	return true
}

func Choose(S mapset.Set, P func(interface{}) bool) interface{} {
	for x := range S.Iter() {
		if P(x) {
			return x
		}
	}
	return nil
}
