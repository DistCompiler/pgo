package kvs

import (
	"fmt"
	"testing"

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

func getReplicas(selfIndex int, numNodes int, keyIndex int, numKeys int) []resources.ReplicaHandle {
	replicas := []resources.ReplicaHandle{}
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		globalID := i * numKeys + keyIndex
		handle := resources.MakeRPCReplicaHandle(getListenAddress(globalID), getArchetypeID(globalID))
		replicas = append(replicas, &handle)
	}
	return replicas
}

func makeContext(nodeIndex int, isReadNode bool, numNodes int, keys []tla.TLAValue) *distsys.MPCalContext {
	twopcs := make(map[tla.TLAValue]distsys.ArchetypeResourceMaker)
	for i := 0; i < len(keys); i++ {
		globalIndex := nodeIndex * len(keys) + i;
		replicas := getReplicas(nodeIndex, numNodes, i, len(keys))
		maker := resources.TwoPCArchetypeResourceMaker(
			tla.MakeTLAString(""),
			getListenAddress(globalIndex),
			replicas,
			getArchetypeID(globalIndex),
			func(receiver *resources.TwoPCReceiver) {},
		)
		twopcs[keys[i]] = maker
	}
	var archetype distsys.MPCalArchetype
	if isReadNode {
		archetype = AReadNode
	} else {
		archetype = AWriteNode
	}
	maker := resources.IncrementalMapMaker(
		func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			return twopcs[index]
		},
	)
	constants := []distsys.MPCalContextConfigFn{}
	return distsys.NewMPCalContext(tla.MakeTLANumber(int32(nodeIndex)), archetype,
		append(
			constants,
			distsys.EnsureArchetypeRefParam("kvs", maker),
		)...,
	)
}

func runTest(t *testing.T, numReadNodes int, numWriteNodes int) {

	numNodes := numReadNodes + numWriteNodes

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	errs := make(chan error, numNodes)

	tlaValues := []tla.TLAValue{tla.MakeTLAString("key1"), tla.MakeTLAString("key2")}

	for i := 0; i < numNodes; i++ {
		ctx := makeContext(i, i < numReadNodes, numNodes, tlaValues)
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

	// for i := 0; i < numNodes; i++ {
	// 	value, err := getCounterValue(replicaCtxs[i])
	// 	if err != nil {
	// 		version := resources.GetTwoPCVersion(receivers[i])
	// 		t.Fatalf("Replica %d(version: %d) encountered error %s", i, version, err)
	// 	}
	// 	if value != tla.MakeTLANumber(int32(numNodes)) {
	// 		t.Fatalf("Replica %d value %s was not equal to expected %d", i, value, numNodes)
	// 	}
	// }

}

func TestKVS(t *testing.T) {
	runTest(t, 5, 5)
}
