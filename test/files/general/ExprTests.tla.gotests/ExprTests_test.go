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

	t.Run("identity", func(t *testing.T) {
		result := Test5(ctx.IFace(), tla.MakeTLANumber(1), tla.MakeTLANumber(3))
		resultStr := result.String()
		if resultStr != "<<1, 2, 3>>" {
			t.Fatalf("result %v did not equal <<1, 2, 3>>", result)
		}
	})

	t.Run("low left idx", func(t *testing.T) {
		defer func() {
			if err := recover(); err != nil {
				if !errors.Is(err.(error), tla.ErrTLAType) {
					t.Fatalf("unexpected panic %v", err)
				}
			} else {
				t.Fatalf("should have panicked, but didn't")
			}
		}()

		_ = Test5(ctx.IFace(), tla.MakeTLANumber(0), tla.MakeTLANumber(3))
	})

	t.Run("high right idx", func(t *testing.T) {
		defer func() {
			if err := recover(); err != nil {
				if !errors.Is(err.(error), tla.ErrTLAType) {
					t.Fatalf("unexpected panic %v", err)
				}
			} else {
				t.Fatalf("should have panicked, but didn't")
			}
		}()

		_ = Test5(ctx.IFace(), tla.MakeTLANumber(1), tla.MakeTLANumber(4))
	})
}

func TestTest6(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	result := Test6(ctx.IFace(), tla.MakeTLANumber(1))
	if result.AsNumber() != 2*1 {
		t.Fatalf("result %v should have been 2 * 1", result)
	}
}

func TestTest7(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	result := Test7(ctx.IFace(), tla.MakeTLANumber(4))
	if result.AsNumber() != 4*3*2*1 {
		t.Fatalf("result %v should have been 4 * 3 * 2 * 1", result)
	}
}

func TestTest8(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	defer func() {
		if err := recover(); err != nil {
			if !errors.Is(err.(error), tla.ErrTLAType) {
				t.Fatalf("error %v should have been ErrTLAType", err)
			}
		} else {
			t.Fatalf("should have panicked")
		}
	}()
	_ = Test8(ctx.IFace())
}

func TestTest9(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()

	defer func() {
		if err := recover(); err != nil {
			if !errors.Is(err.(error), tla.ErrTLAType) {
				t.Fatalf("error %v should have been ErrTLAType", err)
			}
		} else {
			t.Fatalf("should have panicked")
		}
	}()

	_ = Test9(ctx.IFace())
}

func TestTest10(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test10(ctx.IFace())
	if result.AsNumber() != 4 {
		t.Fatalf("%v was not 4", result)
	}
}

func TestTest11(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test11(ctx.IFace())
	if !result.Equal(tla.TLA_FALSE) {
		t.Fatalf("%v was not FALSE", result)
	}
}

func TestTest12(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test12(ctx.IFace())
	if !result.Equal(tla.TLA_TRUE) {
		t.Fatalf("%v was not TRUE", result)
	}
}

func TestTest13(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test13(ctx.IFace())
	if !result.Equal(tla.TLA_TRUE) {
		t.Fatalf("%v was not TRUE", result)
	}
}

func TestTest14(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype()
	result := Test14(ctx.IFace())
	expectedStrs := []string{
		"12",
		"<<>>",
		"\"foo\"",
		"{1}",
	}
	it := result.AsTuple().Iterator()
	for _, expectedStr := range expectedStrs {
		idx, actualValue := it.Next()
		actualString := actualValue.(tla.TLAValue).AsString()
		if actualString != expectedStr {
			t.Fatalf("at idx %d, %s was not %s", idx, actualString, expectedStr)
		}
	}
	if !it.Done() {
		t.Fatalf("result tuple was too long")
	}
}
