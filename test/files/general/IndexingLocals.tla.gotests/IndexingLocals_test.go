package indexinglocals

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"testing"
)

func TestANode(t *testing.T) {
	traceRecorder := trace.MakeLocalFileRecorder("IndexingLocals_trace.txt")
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), ANode, distsys.SetTraceRecorder(traceRecorder))
	err := ctx.Run()
	if err != nil {
		panic(err)
	}

	logVal := ctx.IFace().ReadArchetypeResourceLocal("ANode.log")
	pVal := ctx.IFace().ReadArchetypeResourceLocal("ANode.p")

	if pVal.AsNumber() != 3 {
		t.Fatalf("%v did now equal 3", pVal)
	}

	expectedLogVal := tla.MakeTLATuple(
		tla.MakeTLANumber(3),
		tla.MakeTLANumber(21),
		tla.MakeTLANumber(999),
		tla.MakeTLARecord([]tla.TLARecordField{
			{tla.MakeTLAString("foo"), tla.MakeTLANumber(43)},
		}))
	if !logVal.Equal(expectedLogVal) {
		t.Fatalf("%v did not equal %v", logVal, expectedLogVal)
	}
}
