package dqueue

import (
	"github.com/UBC-NSS/pgo/distsys"
	"testing"
)

func TestNUM_NODES(t *testing.T) {
	result := NUM_NODES(Constants{NUM_CONSUMERS: distsys.NewTLANumber(12)})
	if result.AsNumber() != 13 {
		t.Errorf("NUM_CONSUMERS should have yielded 13, got %v", result)
	}
}

func TestAConsumer(t *testing.T) {
	t.Run("one consumer", func(t *testing.T) {

		go func() {
			err := AConsumer(distsys.TLAValue{}, Constants{}, nil, nil)
			if err != nil {
				panic(err)
			}
		}()

	})
	t.Fail()
}
