package dqueue

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"testing"
)

func TestNUM_NODES(t *testing.T) {
	result := NUM_NODES(Constants{NUM_CONSUMERS: distsys.NewTLANumber(12)})
	if result.AsNumber() != 13 {
		t.Errorf("NUM_CONSUMERS should have yielded 13, got %v", result)
	}
}

func TestProducerConsumer(t *testing.T) {
	producerCtx := distsys.NewMPCalContext()
	producerSelf := distsys.NewTLANumber(1)
	producerInputChannel := make(chan distsys.TLAValue, 3)

	consumerCtx := distsys.NewMPCalContext()
	consumerSelf := distsys.NewTLANumber(2)
	consumerOutputChannel := make(chan distsys.TLAValue, 3)

	constants := Constants{
		PRODUCER: producerSelf,
	}

	go func() {
		network := producerCtx.EnsureArchetypeResourceByName("network", resources.TCPMailboxesArchetypeResourceMaker(func(index distsys.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return resources.TCPMailboxesLocal, "localhost:8001"
			case 2:
				return resources.TCPMailboxesRemote, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}))
		s := producerCtx.EnsureArchetypeResourceByName("s", resources.InputChannelResourceMaker(producerInputChannel))
		err := AProducer(producerCtx, producerSelf, constants, network, s)
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		network := consumerCtx.EnsureArchetypeResourceByName("network", resources.TCPMailboxesArchetypeResourceMaker(func(index distsys.TLAValue) (resources.TCPMailboxKind, string) {
			switch index.AsNumber() {
			case 1:
				return resources.TCPMailboxesRemote, "localhost:8001"
			case 2:
				return resources.TCPMailboxesLocal, "localhost:8002"
			default:
				panic(fmt.Errorf("unknown mailbox index %v", index))
			}
		}))
		proc := consumerCtx.EnsureArchetypeResourceByName("proc", resources.OutputChannelResourceMaker(consumerOutputChannel))
		err := AConsumer(consumerCtx, consumerSelf, constants, network, proc)
		if err != nil {
			panic(err)
		}
	}()

	producedValues := []distsys.TLAValue{
		distsys.NewTLAString("foo"),
		distsys.NewTLAString("bar"),
		distsys.NewTLAString("ping"),
	}
	for _, value := range producedValues {
		producerInputChannel <- value
	}

	consumedValues := []distsys.TLAValue{<-consumerOutputChannel, <-consumerOutputChannel, <-consumerOutputChannel}
	close(consumerOutputChannel)

	if len(consumedValues) != len(producedValues) || !consumedValues[0].Equal(producedValues[0]) || !consumedValues[1].Equal(producedValues[1]) || !consumedValues[2].Equal(producedValues[2]) {
		t.Errorf("Consumed values %v did not match produced values %v", consumedValues, producedValues)
	}
}
