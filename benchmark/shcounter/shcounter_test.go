package shcounter

import (
	"benchmark"
	"counter"
	"testing"
)

func TestShCounter(t *testing.T) {
	benchmark.TestAndReport(func(numNodes int) {
		shcounter.RunTest(t, numNodes)
	})
}
