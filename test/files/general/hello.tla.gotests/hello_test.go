package hello_test

import (
	"log"
	"testing"

	"example.org/hello"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

func TestEmpty(t *testing.T) {
	outCh := make(chan distsys.TLAValue, 1)
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
		if val != hello.HELLO(ctx.IFace()) {
			t.Fatalf("wrong value in the output channel, got %v, expected %v.", val, hello.HELLO(ctx.IFace()))
		}
	default:
		t.Fatal("no value in the output channel")
	}
}
