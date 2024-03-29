package gcounter

import (
	"fmt"
	"log"
	"testing"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TestGCounter_Node(t *testing.T) {
	numNodes := 10
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeNumber(int32(numNodes))),
		distsys.DefineConstantValue("BENCH_NUM_ROUNDS", tla.MakeNumber(0)),
	}

	nodeAddrMap := make(map[tla.Value]string, numNodes+1)
	for i := 1; i <= numNodes; i++ {
		portNum := 9000 + i
		addr := fmt.Sprintf("localhost:%d", portNum)
		nodeAddrMap[tla.MakeNumber(int32(i))] = addr
	}

	var replicaCtxs []*distsys.MPCalContext
	errs := make(chan error, numNodes)
	for i := 1; i <= numNodes; i++ {
		ctx := getNodeMapCtx(tla.MakeNumber(int32(i)), nodeAddrMap, constants)
		replicaCtxs = append(replicaCtxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}
	}()

	getVal := func(ctx *distsys.MPCalContext) (tla.Value, error) {
		fs, err := ctx.IFace().RequireArchetypeResourceRef("ANode.cntr")
		if err != nil {
			return tla.Value{}, err
		}
		return ctx.IFace().Read(fs, []tla.Value{ctx.IFace().Self()})
	}

	for i := 1; i <= numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}

	for _, ctx := range replicaCtxs {
		replicaVal, err := getVal(ctx)
		log.Printf("node %s's count: %s", ctx.IFace().Self(), replicaVal)
		if err != nil {
			t.Fatalf("could not read value from cntr")
		}
		if !replicaVal.Equal(tla.MakeNumber(int32(numNodes))) {
			t.Fatalf("expected values %v and %v to be equal", replicaVal, numNodes)
		}
	}
}
