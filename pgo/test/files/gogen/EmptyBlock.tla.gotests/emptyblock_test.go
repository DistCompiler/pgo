package emptyblock

import "testing"

func TestNothing(t *testing.T) {
	t.Skipf("Nothing to test. This just has to compile; the generated code should be fundamentally empty.")
}
