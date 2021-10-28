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
		} else {
			t.Fatalf("should have panicked, but didn't")
		}
	}()
	_ = Test4(ctx.IFace())
}

func TestTest5(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	result := Test5(ctx.IFace(), tla.MakeTLANumber(1))
	if result.AsNumber() != 2 * 1 {
		t.Fatalf("result %v should have been 2 * 1", result)
	}
}

func TestTest6(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	result := Test6(ctx.IFace(), tla.MakeTLANumber(4))
	if result.AsNumber() != 4 * 3 * 2 * 1 {
		t.Fatalf("result %v should have been 4 * 3 * 2 * 1", result)
	}
}
