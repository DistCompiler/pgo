package shcounter

import (
	"log"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
)

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 9000 + nodeIndex)
}

func getReplicas(selfIndex int, numNodes int) []resources.ReplicaHandle {
	replicas := []resources.ReplicaHandle{}
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		handle := resources.MakeRPCReplicaHandle(getListenAddress(i))
		replicas = append(replicas, &handle)
	}
	return replicas
}

func runArchetype(fn func() error) error {
	err := fn()
	if err == distsys.ErrContextClosed {
		return nil
	}
	return err
}

func TestShCounter(t *testing.T) {
	numNodes := 3

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	complete := make(chan *resources.TwoPCArchetypeResource, numNodes)
	for i := 0; i < numNodes; i++ {
		replicas := getReplicas(i, numNodes)
		nodeName := fmt.Sprintf("Node%d", i);
		maker := resources.TwoPCArchetypeResourceMaker(
			tla.MakeTLANumber(0),
			getListenAddress(i),
			replicas,
			nodeName,
			complete,
		)
		ctx := distsys.NewMPCalContext(tla.MakeTLANumber(int32(i)), ANode,
			append(
				constants,
				distsys.EnsureArchetypeRefParam("cntr", maker),
			)...,
		)
		replicaCtxs[i] = ctx
		go func() {
			errs <- runArchetype(ctx.Run)
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
		}
	}()

	for i := 0; i < numNodes; i++ {
		err := <- errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}
	for i := 0; i < numNodes; i++ {
		resource := <- complete
		value, _ := resource.ReadValue()
		if value != tla.MakeTLANumber(int32(numNodes)) {
			t.Fatalf("Replica value %s was not equal to expected %d", value, numNodes)
		}
	}
}
