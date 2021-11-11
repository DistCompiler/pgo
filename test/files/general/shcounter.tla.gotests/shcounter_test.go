package shcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	"testing"
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

func runArchetype(fn func() error) error {
	err := fn()
	if err == distsys.ErrContextClosed {
		return nil
	}
	return err
}

func getCounterValue(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
	arch, err := ctx.IFace().RequireArchetypeResourceRef("ANode.cntr")
	if err != nil {
		return tla.TLAValue{}, err
	}
	return ctx.IFace().Read(arch, []tla.TLAValue{})
}

const numNodes = 30;

func makeContext(i int) *distsys.MPCalContext {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	};
	replicas := getReplicas(i, numNodes)
	maker := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLANumber(0),
		getListenAddress(i),
		replicas,
		getArchetypeID(i),
	)
	return distsys.NewMPCalContext(tla.MakeTLANumber(int32(i)), ANode,
		append(
			constants,
			distsys.EnsureArchetypeRefParam("cntr", maker),
		)...,
	)
}

func TestShCounter(t *testing.T) {


	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		ctx := makeContext(i)
		replicaCtxs[i] = ctx

		go func() {
			runErr := runArchetype(ctx.Run)
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
			errs <- runErr
		}()
	}

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}

	for i := 0; i < numNodes; i++ {
		value, err := getCounterValue(replicaCtxs[i])
		if err != nil {
			t.Fatalf("Replica %d encountered error %s", i, err)
		}
		if value != tla.MakeTLANumber(int32(numNodes)) {
			t.Fatalf("Replica %d value %s was not equal to expected %d", i, value, numNodes)
		}
	}
}
