package exprtests

import (
	"errors"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
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

func TestTest3(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test3(ctx.IFace())
	actualStr := result.String()
	expectedStr := "2"
	if actualStr != expectedStr {
		t.Errorf("Expected value %s, got %s", expectedStr, actualStr)
	}
}

func TestTest4(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	defer func() {
		if err := recover(); err != nil {
			if !errors.Is(err.(error), tla.ErrTLAType) {
				t.Fatalf("unexpected panic %v", err)
			}
		}
	}()
	_ = Test4(ctx.IFace())
}
