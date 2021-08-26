package exprtests

import (
	"github.com/UBC-NSS/pgo/distsys"
	"testing"
)

func TestTest1(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test1(ctx.IFace())
	actualStr := result.String()
	expectedStr := "{1, 2, 3}"
	if actualStr != expectedStr {
		t.Errorf("Expected value %s, got %s", expectedStr, actualStr)
	}
}
