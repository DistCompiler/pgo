package dqueue

import (
	"fmt"
	"testing"

	"github.com/DistCompiler/pgo/distsys/tla"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
)

func TestNUM_NODES(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype(
		distsys.DefineConstantValue("NUM_CONSUMERS", tla.MakeNumber(12)))

	result := NUM_NODES(ctx.IFace())
	if result.AsNumber() != 13 {
		t.Errorf("NUM_CONSUMERS(12) should have yielded 13, got %v", result)
	}
}

func TestProducerConsumer(t *testing.T) {
	producerSelf := tla.MakeNumber(0)
	producerInputChannel := make(chan tla.Value, 3)

	consumerSelf := tla.MakeNumber(1)
	consumerOutputChannel := make(chan tla.Value, 3)

	ctxProducer := distsys.NewMPCalContext(producerSelf, AProducer,
		distsys.DefineConstantValue("PRODUCER", producerSelf),
		distsys.EnsureArchetypeRefParam("net", resources.NewTCPMailboxes(func(index tla.Value) (resources.MailboxKind, string) {
			switch index.AsNumber() {
			case 0:
				return resources.MailboxesLocal, "localhost:8001"
			case 1:
				return resources.MailboxesRemote, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		})),
		distsys.EnsureArchetypeRefParam("s", resources.NewInputChan(producerInputChannel)))
	defer ctxProducer.Stop()
	go func() {
		err := ctxProducer.Run()
		if err != nil {
			panic(err)
		}
	}()

	ctxConsumer := distsys.NewMPCalContext(consumerSelf, AConsumer,
		distsys.DefineConstantValue("PRODUCER", producerSelf),
		distsys.EnsureArchetypeRefParam("net", resources.NewTCPMailboxes(func(index tla.Value) (resources.MailboxKind, string) {
			switch index.AsNumber() {
			case 0:
				return resources.MailboxesRemote, "localhost:8001"
			case 1:
				return resources.MailboxesLocal, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		})),
		distsys.EnsureArchetypeRefParam("proc", resources.NewOutputChan(consumerOutputChannel)))
	defer ctxConsumer.Stop()
	go func() {
		err := ctxConsumer.Run()
		if err != nil {
			panic(err)
		}
	}()

	producedValues := []tla.Value{
		tla.MakeNumber(1),
		tla.MakeNumber(2),
		tla.MakeNumber(3),
	}
	for _, value := range producedValues {
		producerInputChannel <- value
	}

	consumedValues := []tla.Value{<-consumerOutputChannel, <-consumerOutputChannel, <-consumerOutputChannel}
	close(consumerOutputChannel)

	if len(consumedValues) != len(producedValues) {
		t.Fatalf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
	}
	for i := range producedValues {
		if !consumedValues[i].Equal(producedValues[i]) {
			t.Fatalf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
		}
	}
}
