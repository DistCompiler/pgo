package pgoutil

import (
	"mapset"
	"reflect"
)

func Exists(S mapset.Set, P interface{}) bool {
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if cond[0].Bool() {
			return true
		}
	}
	return false
}

func ForAll(S mapset.Set, P interface{}) bool {
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if !cond[0].Bool() {
			return false
		}
	}
	return true
}

func Choose(S mapset.Set, P interface{}) interface{} {
	vf := reflect.ValueOf(P)
	for x := range S.Iter() {
		cond := vf.Call([]reflect.Value{reflect.ValueOf(x)})
		if cond[0].Bool() {
			return x
		}
	}
	return nil
}
