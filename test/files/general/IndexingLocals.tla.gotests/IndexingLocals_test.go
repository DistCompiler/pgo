package indexinglocals

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"testing"
)

func TestANode(t *testing.T) {
	var traceRecorder trace.Recorder = nil // trace.MakeLocalFileRecorder("IndexingLocals_trace.txt")
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), ANode, distsys.SetTraceRecorder(traceRecorder))
	err := ctx.Run()
	if err != nil {
		panic(err)
	}

	logVal := ctx.IFace().ReadArchetypeResourceLocal("ANode.log")
	pVal := ctx.IFace().ReadArchetypeResourceLocal("ANode.p")

	if pVal.AsNumber() != 3 {
		t.Fatalf("%v did now equal 3", pVal)
	}

	expectedLogVal := tla.MakeTuple(
		tla.MakeNumber(3),
		tla.MakeNumber(21),
		tla.MakeNumber(999),
		tla.MakeRecord([]tla.RecordField{
			{tla.MakeString("foo"), tla.MakeNumber(43)},
		}))
	if !logVal.Equal(expectedLogVal) {
		t.Fatalf("%v did not equal %v", logVal, expectedLogVal)
	}
}
