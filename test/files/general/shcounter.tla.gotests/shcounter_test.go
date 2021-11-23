package shcounter

import (
	"fmt"
	"testing"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 9000+nodeIndex)
}

func getArchetypeID(nodeIndex int) tla.TLAValue {
	return tla.MakeTLAString(fmt.Sprintf("node%d", nodeIndex))
}

func getReplicas(selfIndex int, numNodes int) []resources.ReplicaHandle {
	replicas := []resources.ReplicaHandle{}
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		handle := resources.MakeRPCReplicaHandle(getListenAddress(i), getArchetypeID(i))
		replicas = append(replicas, &handle)
	}
	return replicas
}

func getCounterValue(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
	arch, err := ctx.IFace().RequireArchetypeResourceRef("ANode.cntr")
	if err != nil {
		return tla.TLAValue{}, err
	}
	return ctx.IFace().Read(arch, []tla.TLAValue{})
}

func TestShCounter(t *testing.T) {
	numNodes := 5

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		replicas := getReplicas(i, numNodes)
		maker := resources.TwoPCArchetypeResourceMaker(
			tla.MakeTLANumber(0),
			getListenAddress(i),
			replicas,
			getArchetypeID(i),
		)
		ctx := distsys.NewMPCalContext(tla.MakeTLANumber(int32(i)), ANode,
			append(
				constants,
				distsys.EnsureArchetypeRefParam("cntr", maker),
			)...,
		)
		replicaCtxs[i] = ctx
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}
	}()

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}
	for i := 0; i < numNodes; i++ {
		value, _ := getCounterValue(replicaCtxs[i])
		if value != tla.MakeTLANumber(int32(numNodes)) {
			t.Fatalf("Replica value %s was not equal to expected %d", value, numNodes)
		}
	}
}
