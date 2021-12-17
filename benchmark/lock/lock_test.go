package lock

import (
	"fmt"
	"testing"

	"benchmark"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 8000+nodeIndex)
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

func makeContext(i int, receivers []*resources.TwoPCReceiver) *distsys.MPCalContext {
	numNodes := len(receivers)
	constants := []distsys.MPCalContextConfigFn{}
	replicas := getReplicas(i, numNodes)
	maker := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLABool(false),
		getListenAddress(i),
		replicas,
		getArchetypeID(i),
		func(receiver *resources.TwoPCReceiver) {
			receivers[i] = receiver
		},
	)
	return distsys.NewMPCalContext(tla.MakeTLANumber(int32(i)), ANode,
		append(
			constants,
			distsys.EnsureArchetypeRefParam("lock", maker),
		)...,
	)
}

func runTest(t *testing.T, numNodes int) {

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	receivers := make([]*resources.TwoPCReceiver, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		ctx := makeContext(i, receivers)
		replicaCtxs[i] = ctx
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}
		for _, receiver := range receivers {
			resources.CloseTwoPCReceiver(receiver)
		}
	}()

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}

}

func TestLock(t *testing.T) {
	benchmark.TestAndReport(func(numNodes int) {
		runTest(t, numNodes)
	})
}
