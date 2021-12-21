package gcounter

import (
	"benchmark"
	"counter"
	"testing"
)

func TestShCounter(t *testing.T) {
	benchmark.TestAndReport(func(numNodes int) {
		gcounter.Bench(t, numNodes, 1)
	})
}
