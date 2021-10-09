package hello_test

import (
	"log"
	"testing"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"example.org/hello"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

func TestConstantDefinitionVariations(t *testing.T) {
	type TestRec struct {
		Name   string
		Config distsys.MPCalContextConfigFn
	}

	tests := []TestRec{
		{
			Name: "two args",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.TLAValue) tla.TLAValue {
				return tla.MakeTLAString(left.AsString() + right.AsString())
			}),
		},
		{
			Name: "fully variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(args ...tla.TLAValue) tla.TLAValue {
				return tla.MakeTLAString(args[0].AsString() + args[1].AsString())
			}),
		},
		{
			Name: "partly variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left tla.TLAValue, restArgs ...tla.TLAValue) tla.TLAValue {
				return tla.MakeTLAString(left.AsString() + restArgs[0].AsString())
			}),
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			ctx := distsys.NewMPCalContextWithoutArchetype(test.Config)
			expectedResult := tla.MakeTLAString("hello")
			actualResult := hello.HELLO(ctx.IFace())
			if !actualResult.Equal(expectedResult) {
				t.Fatalf("actual result of hello.HELLO %v did not equal expected value %v", actualResult, expectedResult)
			}
		})
	}
}

func TestEmpty(t *testing.T) {
	outCh := make(chan tla.TLAValue, 1)
	// omit the constant defn, and notice that it's still fine, because we ran nothing
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), hello.AHello,
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)))
	defer func() {
		err := ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()
}

func TestHello(t *testing.T) {
	outCh := make(chan tla.TLAValue, 1)
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), hello.AHello,
		distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.TLAValue) tla.TLAValue {
			return tla.MakeTLAString(left.AsString() + right.AsString())
		}),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)))
	defer func() {
		err := ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	err := ctx.Run()
	if err != nil {
		t.Fatalf("non-nil error from AHello archetype: %s", err)
	}
	select {
	case val := <-outCh:
		expectedValue := tla.MakeTLAString("hello")
		if !val.Equal(expectedValue) {
			t.Fatalf("wrong value in the output channel, got %v, expected %v.", val, expectedValue)
		}
	default:
		t.Fatal("no value in the output channel")
	}
}
