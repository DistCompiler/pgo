package shopcart

import (
	"fmt"
	"testing"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

const addToCart = 1
const removeFromCart = 2

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 8000+nodeIndex)
}

func getArchetypeID(nodeIndex int) tla.TLAValue {
	return tla.MakeTLAString(fmt.Sprintf("cart%d", nodeIndex))
}

func getReplicas(selfIndex int, numNodes int) []resources.ReplicaHandle {
	replicas := []resources.ReplicaHandle{}
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		handle := resources.MakeRPCReplicaHandle(
			getListenAddress(i),
			getArchetypeID(i),
		)
		replicas = append(replicas, &handle)
	}
	return replicas
}

func makeAction(cmd int32, elem string) tla.TLAValue {
	action := immutable.NewMapBuilder(tla.TLAValueHasher{})
	action.Set(tla.MakeTLAString("cmd"), tla.MakeTLANumber(int32(cmd)))
	action.Set(tla.MakeTLAString("elem"), tla.MakeTLAString(elem))
	return tla.MakeTLARecordFromMap(action.Map())
}

func makeContext(i int, numNodes int) *distsys.MPCalContext {
	constants := []distsys.MPCalContextConfigFn{}
	cart := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLASet(),
		getListenAddress(i),
		getReplicas(i, numNodes),
		getArchetypeID(i),
		func(receiver *resources.TwoPCReceiver) {},
	)


	inChan := make(chan tla.TLAValue, 4)
	inChan <- makeAction(addToCart, "elem1")
	inChan <- makeAction(removeFromCart, "elem2")
	inChan <- makeAction(addToCart, "elem2")
	inChan <- makeAction(removeFromCart, "elem1")


	in := resources.InputChannelMaker(inChan)

	return distsys.NewMPCalContext(tla.MakeTLANumber(int32(i)), ANode,
		append(
			constants,
			distsys.EnsureArchetypeRefParam("cart", cart),
			distsys.EnsureArchetypeRefParam("in", in),
		)...,
	)
}

func runTest(t *testing.T, numNodes int) {

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		ctx := makeContext(i, numNodes)
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

}

func TestLock(t *testing.T) {
	runTest(t, 10)
}
