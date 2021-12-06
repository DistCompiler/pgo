package gcounter

import (
	"benchmark"
	"fmt"
	"log"
	"os"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNodeMapCtx(self tla.TLAValue, nodeAddrMap map[tla.TLAValue]string, broadcastInterval time.Duration, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, ANode, append(constants,
		distsys.EnsureArchetypeRefParam("cntr", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			peers := make([]tla.TLAValue, 0)
			for nid := range nodeAddrMap {
				if nid != self {
					peers = append(peers, nid)
				}
			}
			return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
				return nodeAddrMap[index]
			}, broadcastInterval, resources.MakeGCounter)
		})))...)
	return ctx
}

func getVal(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
	cntr, err := ctx.IFace().RequireArchetypeResourceRef("ANode.cntr")
	if err != nil {
		return tla.TLAValue{}, err
	}
	return ctx.IFace().Read(cntr, []tla.TLAValue{ctx.IFace().Self()})
}

func runTest(t *testing.T, numNodes int, broadcastInterval time.Duration) {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}

	nodeAddrMap := make(map[tla.TLAValue]string, numNodes)
	for i := 1; i <= numNodes; i++ {
		portNum := 9000 + i
		addr := fmt.Sprintf("localhost:%d", portNum)
		nodeAddrMap[tla.MakeTLANumber(int32(i))] = addr
	}

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)
	for i := 1; i <= numNodes; i++ {
		ctx := getNodeMapCtx(tla.MakeTLANumber(int32(i)), nodeAddrMap, broadcastInterval, constants)
		replicaCtxs[i-1] = ctx
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}
	}()

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
		if !replicaVal.Equal(tla.MakeTLANumber(int32(numNodes))) {
			t.Fatalf("expected values %v and %v to be equal", replicaVal, numNodes)
		}
	}
}

func TestGCounter(t *testing.T) {
	if os.Getenv("PGO_BENCHMARK") == "" {
		runTest(t, 22, 5)
	} else {
		benchmark.TestAndReport(func(numNodes int, broadcastInterval time.Duration){
			runTest(t, numNodes, broadcastInterval)
		})
	}
}
