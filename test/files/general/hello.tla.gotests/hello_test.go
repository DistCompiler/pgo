package hello_test

import (
	"log"
	"testing"

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
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left, right distsys.TLAValue) distsys.TLAValue {
				return distsys.NewTLAString(left.AsString() + right.AsString())
			}),
		},
		{
			Name: "fully variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(args ...distsys.TLAValue) distsys.TLAValue {
				return distsys.NewTLAString(args[0].AsString() + args[1].AsString())
			}),
		},
		{
			Name: "partly variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left distsys.TLAValue, restArgs ...distsys.TLAValue) distsys.TLAValue {
				return distsys.NewTLAString(left.AsString() + restArgs[0].AsString())
			}),
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			ctx := distsys.NewMPCalContextWithoutArchetype(test.Config)
			expectedResult := distsys.NewTLAString("hello")
			actualResult := hello.HELLO(ctx.IFace())
			if !actualResult.Equal(expectedResult) {
				t.Fatalf("actual result of hello.HELLO %v did not equal expected value %v", actualResult, expectedResult)
			}
		})
	}
}

func TestEmpty(t *testing.T) {
	outCh := make(chan distsys.TLAValue, 1)
	// omit the constant defn, and notice that it's still fine, because we ran nothing
	ctx := distsys.NewMPCalContext(distsys.NewTLAString("self"), hello.AHello,
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelResourceMaker(outCh)))
	defer func() {
		err := ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()
}

func TestHello(t *testing.T) {
	outCh := make(chan distsys.TLAValue, 1)
	ctx := distsys.NewMPCalContext(distsys.NewTLAString("self"), hello.AHello,
		distsys.DefineConstantOperator("MK_HELLO", func(left, right distsys.TLAValue) distsys.TLAValue {
			return distsys.NewTLAString(left.AsString() + right.AsString())
		}),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelResourceMaker(outCh)))
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
		expectedValue := distsys.NewTLAString("hello")
		if !val.Equal(expectedValue) {
			t.Fatalf("wrong value in the output channel, got %v, expected %v.", val, expectedValue)
		}
	default:
		t.Fatal("no value in the output channel")
	}
}
