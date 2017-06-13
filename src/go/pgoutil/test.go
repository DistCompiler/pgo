package pgoutil

import (
	"testing"
	"reflect"
	"runtime/debug"
)

func assertEquals(expected, actual interface{}, t *testing.T) {
	if (!reflect.DeepEqual(expected, actual)) {
		t.Errorf("Expected %v but got %v", expected, actual)
		debug.PrintStack()
	}
}