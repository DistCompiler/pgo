package dqueue

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

func TestNUM_NODES(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype(
		distsys.DefineConstantValue("NUM_CONSUMERS", tla.MakeTLANumber(12)))

	result := NUM_NODES(ctx.IFace())
	if result.AsNumber() != 13 {
		t.Errorf("NUM_CONSUMERS(12) should have yielded 13, got %v", result)
	}
}

func TestProducerConsumer(t *testing.T) {
	producerSelf := tla.MakeTLANumber(1)
	producerInputChannel := make(chan tla.TLAValue, 3)

	consumerSelf := tla.MakeTLANumber(2)
	consumerOutputChannel := make(chan tla.TLAValue, 3)

	ctxProducer := distsys.NewMPCalContext(producerSelf, AProducer,
		distsys.DefineConstantValue("PRODUCER", producerSelf),
		distsys.EnsureArchetypeRefParam("net", resources.TCPMailboxesArchetypeResourceMaker(func(index tla.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return resources.TCPMailboxesLocal, "localhost:8001"
			case 2:
				return resources.TCPMailboxesRemote, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		})),
		distsys.EnsureArchetypeRefParam("s", resources.InputChannelResourceMaker(producerInputChannel)))
	go func() {
		err := ctxProducer.Run()
		if err != nil && err != distsys.ErrContextClosed {
			panic(err)
		}
	}()

	ctxConsumer := distsys.NewMPCalContext(consumerSelf, AConsumer,
		distsys.DefineConstantValue("PRODUCER", producerSelf),
		distsys.EnsureArchetypeRefParam("net", resources.TCPMailboxesArchetypeResourceMaker(func(index tla.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return resources.TCPMailboxesRemote, "localhost:8001"
			case 2:
				return resources.TCPMailboxesLocal, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		})),
		distsys.EnsureArchetypeRefParam("proc", resources.OutputChannelResourceMaker(consumerOutputChannel)))
	go func() {
		err := ctxConsumer.Run()
		if err != nil && err != distsys.ErrContextClosed {
			panic(err)
		}
	}()

	defer func() {
		if err := ctxProducer.Close(); err != nil {
			log.Println(err)
		}
		if err := ctxConsumer.Close(); err != nil {
			log.Println(err)
		}
	}()

	producedValues := []tla.TLAValue{
		tla.MakeTLAString("foo"),
		tla.MakeTLAString("bar"),
		tla.MakeTLAString("ping"),
	}
	for _, value := range producedValues {
		producerInputChannel <- value
	}

	consumedValues := []tla.TLAValue{<-consumerOutputChannel, <-consumerOutputChannel, <-consumerOutputChannel}
	close(consumerOutputChannel)
	time.Sleep(100 * time.Millisecond)

	if len(consumedValues) != len(producedValues) {
		t.Fatalf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
	}
	for i := range producedValues {
		if !consumedValues[i].Equal(producedValues[i]) {
			t.Fatalf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
		}
	}
}
