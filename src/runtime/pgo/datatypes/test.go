package datatypes

import (
	"reflect"
	"runtime/debug"
	"testing"
)

func assertSetEqual(expected, actual Set, t *testing.T) {
	if !expected.Equal(actual) {
		t.Errorf("Expected %v but got %v", expected, actual)
		debug.PrintStack()
	}
}

func assertEquals(expected, actual interface{}, t *testing.T) {
	if !reflect.DeepEqual(expected, actual) {
		t.Errorf("Expected %v but got %v", expected, actual)
		debug.PrintStack()
	}
}
