package gcounter

import (
	"fmt"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNodeMapCtx(self tla.TLAValue, nodeAddrMap map[tla.TLAValue]string, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	var peers []tla.TLAValue
	for nid := range nodeAddrMap {
		if !nid.Equal(self) {
			peers = append(peers, nid)
		}
	}
	ctx := distsys.NewMPCalContext(self, ANode, append(constants,
		distsys.EnsureArchetypeRefParam("cntr", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
				return nodeAddrMap[index]
			}, 100*time.Millisecond, len(peers), resources.MakeGCounter)
		})),
		distsys.EnsureArchetypeRefParam("c", resources.DummyResourceMaker()),
	)...)
	return ctx
}

func makeNodeBenchCtx(self tla.TLAValue, nodeAddrMap map[tla.TLAValue]string,
	constants []distsys.MPCalContextConfigFn, outCh chan tla.TLAValue) *distsys.MPCalContext {
	var peers []tla.TLAValue
	for nid := range nodeAddrMap {
		if !nid.Equal(self) {
			peers = append(peers, nid)
		}
	}
	ctx := distsys.NewMPCalContext(self, ANodeBench, append(constants,
		distsys.EnsureArchetypeRefParam("cntr", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
				return nodeAddrMap[index]
			}, 100*time.Millisecond, len(peers), resources.MakeGCounter)
		})),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
	)...)
	return ctx
}

func Bench(t *testing.T, numNodes int, numRounds int) {
	numEvents := numNodes * numRounds * 2

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
		distsys.DefineConstantValue("BENCH_NUM_ROUNDS", tla.MakeTLANumber(int32(numRounds))),
	}
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	nodeAddrMap := make(map[tla.TLAValue]string, numNodes+1)
	for i := 1; i <= numNodes; i++ {
		portNum := 9000 + i
		addr := fmt.Sprintf("localhost:%d", portNum)
		nodeAddrMap[tla.MakeTLANumber(int32(i))] = addr
	}

	var replicaCtxs []*distsys.MPCalContext
	outCh := make(chan tla.TLAValue, numEvents)
	errs := make(chan error, numNodes)
	for i := 1; i <= numNodes; i++ {
		ctx := makeNodeBenchCtx(tla.MakeTLANumber(int32(i)), nodeAddrMap, constants, outCh)
		replicaCtxs = append(replicaCtxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	starts := make(map[int32]time.Time)
	for i := 0; i < numEvents; i++ {
		resp := <-outCh
		node := resp.ApplyFunction(tla.MakeTLAString("node")).AsNumber()
		event := resp.ApplyFunction(tla.MakeTLAString("event"))
		if event.Equal(IncStart(iface)) {
			starts[node] = time.Now()
		} else if event.Equal(IncFinish(iface)) {
			elapsed := time.Since(starts[node])
			log.Println(node, elapsed)
		}
	}

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatal(err)
		}
	}
}
