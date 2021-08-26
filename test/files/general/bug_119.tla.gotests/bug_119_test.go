package test

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"testing"
)

func TestCounter(t *testing.T) {
	outChan := make(chan distsys.TLAValue, 1)

	ctx := distsys.NewMPCalContext(distsys.NewTLAString("self"), Counter,
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelResourceMaker(outChan)))

	err := ctx.Run()
	if err != nil {
		panic(err)
	}

	outVal := <-outChan
	close(outChan) // everything is sync in this test, but close the channel anyway to catch anything weird
	if !outVal.Equal(distsys.NewTLANumber(1)) {
		t.Errorf("incrementation result %v was not equal to expected value 1", outVal)
	}
}
