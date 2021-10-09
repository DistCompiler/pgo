package test

import (
	"testing"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TestCounter(t *testing.T) {
	outChan := make(chan tla.TLAValue, 1)

	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), Counter,
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outChan)))

	err := ctx.Run()
	if err != nil {
		panic(err)
	}

	outVal := <-outChan
	close(outChan) // everything is sync in this test, but close the channel anyway to catch anything weird
	if !outVal.Equal(tla.MakeTLANumber(1)) {
		t.Errorf("incrementation result %v was not equal to expected value 1", outVal)
	}
}
