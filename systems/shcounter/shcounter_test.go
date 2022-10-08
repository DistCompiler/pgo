package shcounter

// The main test logic has been moved to shcounter_util, in order to also
// use the same tests for benchmarking.

import (
	"testing"
)

func TestShCounter(t *testing.T) {
	RunTest(t, 20)
}
