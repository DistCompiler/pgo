package aworset

import (
	"fmt"
	"log"
	"testing"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNodeMapCtx(self tla.TLAValue, nodeAddrMap map[tla.TLAValue]string, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, ANode, append(constants,
		distsys.EnsureArchetypeRefParam("crdt", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			peers := make([]tla.TLAValue, 0)
			for nid := range nodeAddrMap {
				if !nid.Equal(self) {
					peers = append(peers, nid)
				}
			}
			return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
				return nodeAddrMap[index]
			}, 5, 3, resources.MakeAWORSet)
		})))...)
	return ctx
}

func Test_AWORSet(t *testing.T) {
	numNodes := 3
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}

	nodeAddrMap := make(map[tla.TLAValue]string, numNodes)
	for i := 1; i <= numNodes; i++ {
		portNum := 9000 + i
		addr := fmt.Sprintf("localhost:%d", portNum)
		nodeAddrMap[tla.MakeTLANumber(int32(i))] = addr
	}

	var replicaCtxs []*distsys.MPCalContext
	errs := make(chan error, numNodes)
	for i := 1; i <= numNodes; i++ {
		ctx := getNodeMapCtx(tla.MakeTLANumber(int32(i)), nodeAddrMap, constants)
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

	getVal := func(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
		fs, err := ctx.IFace().RequireArchetypeResourceRef("ANode.crdt")
		if err != nil {
			return tla.TLAValue{}, err
		}
		return ctx.IFace().Read(fs, []tla.TLAValue{ctx.IFace().Self()})
	}

	for i := 1; i <= numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}

	for _, ctx := range replicaCtxs {
		replicaVal, err := getVal(ctx)
		log.Printf("node %s's set: %s", ctx.IFace().Self(), replicaVal)
		if err != nil {
			t.Fatalf("could not read value from cntr")
		}
		expected := tla.MakeTLASet()
		if !replicaVal.Equal(expected) {
			t.Fatalf("expected values %v and %v to be equal", replicaVal, expected)
		}
	}
}
