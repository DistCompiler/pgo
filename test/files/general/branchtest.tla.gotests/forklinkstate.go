package branchtest_tla_gotests

import (
	"testing"
)

func start(t *testing.T) {
	t.Errorf("NUM_CONSUMERS(12) should have yielded 13, got %v", "error")
}
