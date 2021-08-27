package hello_test

import (
	"log"
	"testing"

	"example.org/hello"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

func TestEmpty(t *testing.T) {
	ctx := distsys.NewMPCalContext()
	defer func() {
		err := ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	outCh := make(chan distsys.TLAValue, 1)
	outMaker := resources.OutputChannelResourceMaker(outCh)
	_ = ctx.EnsureArchetypeResourceByName("out", outMaker)
}

func TestHello(t *testing.T) {
	ctx := distsys.NewMPCalContext()
	defer func() {
		err := ctx.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	constants := hello.Constants{}
	outCh := make(chan distsys.TLAValue, 1)
	outMaker := resources.OutputChannelResourceMaker(outCh)
	out := ctx.EnsureArchetypeResourceByName("out", outMaker)
	err := hello.AHello(ctx, distsys.NewTLANumber(1), constants, out)
	if err != nil {
		t.Fatalf("non-nil error from AHello archetype: %s", err)
	}
	select {
	case val := <-outCh:
		if val != hello.HELLO(constants) {
			t.Fatalf("wrong value in the output channel, got %v, expected %v.", val, hello.HELLO(constants))
		}
	default:
		t.Fatal("no value in the output channel")
	}
}
