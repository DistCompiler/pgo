package hello_test

import (
	"log"
	"testing"

	"github.com/DistCompiler/pgo/distsys/trace"

	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/test/files/general/hello.tla.gotests"
)

func TestConstantDefinitionVariations(t *testing.T) {
	type TestRec struct {
		Name   string
		Config distsys.MPCalContextConfigFn
	}

	tests := []TestRec{
		{
			Name: "two args",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.Value) tla.Value {
				return tla.MakeString(left.AsString() + right.AsString())
			}),
		},
		{
			Name: "fully variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(args ...tla.Value) tla.Value {
				return tla.MakeString(args[0].AsString() + args[1].AsString())
			}),
		},
		{
			Name: "partly variadic",
			Config: distsys.DefineConstantOperator("MK_HELLO", func(left tla.Value, restArgs ...tla.Value) tla.Value {
				return tla.MakeString(left.AsString() + restArgs[0].AsString())
			}),
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			ctx := distsys.NewMPCalContextWithoutArchetype(test.Config)
			expectedResult := tla.MakeString("hello")
			actualResult := hello.HELLO(ctx.IFace())
			if !actualResult.Equal(expectedResult) {
				t.Fatalf("actual result of hello.HELLO %v did not equal expected value %v", actualResult, expectedResult)
			}
		})
	}
}

func TestEmpty(t *testing.T) {
	outCh := make(chan tla.Value, 1)
	// omit the constant defn, and notice that it's still fine, because we ran nothing
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), hello.AHello,
		distsys.EnsureArchetypeRefParam("out", resources.NewOutputChan(outCh)))
	defer ctx.Stop()
}

func TestHello(t *testing.T) {
	outCh := make(chan tla.Value, 1)
	var traceRecorder trace.Recorder = nil // trace.MakeLocalFileRecorder("hello_simple_trace.txt")
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), hello.AHello,
		distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.Value) tla.Value {
			return tla.MakeString(left.AsString() + right.AsString())
		}),
		distsys.EnsureArchetypeRefParam("out", resources.NewOutputChan(outCh)),
		distsys.SetTraceRecorder(traceRecorder),
	)

	err := ctx.Run()
	if err != nil {
		t.Fatalf("non-nil error from AHello archetype: %s", err)
	}
	select {
	case val := <-outCh:
		expectedValue := tla.MakeString("hello")
		if !val.Equal(expectedValue) {
			t.Fatalf("wrong value in the output channel, got %v, expected %v.", val, expectedValue)
		}
	default:
		t.Fatal("no value in the output channel")
	}
}

func TestHello_SharedResource(t *testing.T) {
	outMaker := resources.NewLocalSharedManager(tla.MakeString("a"))

	var traceRecorder trace.Recorder = nil // trace.MakeLocalFileRecorder("hello_shared_trace.txt")
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), hello.AHello,
		distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.Value) tla.Value {
			return tla.MakeString(left.AsString() + right.AsString())
		}),
		distsys.EnsureArchetypeRefParam("out", outMaker.MakeLocalShared()),
		distsys.SetTraceRecorder(traceRecorder),
	)

	err := ctx.Run()
	if err != nil {
		t.Fatalf("non-nil error from AHello archetype: %s", err)
	}
}

func TestHello_PersistentResource(t *testing.T) {
	db, err := badger.Open(badger.DefaultOptions("/tmp/badger"))
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := db.Close(); err != nil {
			log.Println(err)
		}
	}()

	out := distsys.NewLocalArchetypeResource(tla.MakeString("a"))
	persistentOutMaker := resources.MakePersistent("ANode.out", db, out)

	var traceRecorder trace.Recorder = nil // trace.MakeLocalFileRecorder("hello_persistent_trace.txt")
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), hello.AHello,
		distsys.DefineConstantOperator("MK_HELLO", func(left, right tla.Value) tla.Value {
			return tla.MakeString(left.AsString() + right.AsString())
		}),
		distsys.EnsureArchetypeRefParam("out", persistentOutMaker),
		distsys.SetTraceRecorder(traceRecorder),
	)

	err = ctx.Run()
	if err != nil {
		t.Fatalf("non-nil error from AHello archetype: %s", err)
	}
}
