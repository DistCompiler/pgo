package shopcart

import (
	"benchmark"
	"fmt"
	"time"
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

func makeContext(i int, numNodes int, inChan chan tla.TLAValue) *distsys.MPCalContext {
	constants := []distsys.MPCalContextConfigFn{}
	cart := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLASet(),
		getListenAddress(i),
		getReplicas(i, numNodes),
		getArchetypeID(i),
		func(receiver *resources.TwoPCReceiver) {},
	)




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

	chans := make([]chan tla.TLAValue, numNodes)
	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		inChan := make(chan tla.TLAValue, 4)
		inChan <- makeAction(addToCart, "elem1")
		inChan <- makeAction(removeFromCart, "elem2")
		inChan <- makeAction(addToCart, "elem2")
		inChan <- makeAction(removeFromCart, "elem1")
		chans[i] = inChan
		ctx := makeContext(i, numNodes, inChan)
		replicaCtxs[i] = ctx
	}

	for i := 0; i < numNodes; i++ {
		ii := i
		go func() {
			errs <- replicaCtxs[ii].Run()
		}()
	}

OuterLoop:
	for {
		time.Sleep(20 * time.Millisecond)
		for i := 0; i < numNodes; i++ {
			if len(chans[i]) > 0 {
				continue OuterLoop
			}
		}
		break OuterLoop
	}

	for _, ctx := range replicaCtxs {
		ctx.Stop()
	}

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}

}

func TestShopCart(t *testing.T) {
	benchmark.TestAndReport(func(numNodes int) {
		runTest(t, numNodes)
	})
}
