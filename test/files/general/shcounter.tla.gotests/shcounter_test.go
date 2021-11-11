package shcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	"math/rand"
	"sync"
	"testing"
	"time"
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

func makeContext(i int, receivers []*resources.TwoPCReceiver) *distsys.MPCalContext {
	numNodes := len(receivers)
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}
	replicas := getReplicas(i, numNodes)
	maker := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLANumber(0),
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
			distsys.EnsureArchetypeRefParam("cntr", maker),
		)...,
	)
}

func runTest(t *testing.T, numNodes int, injectFailures bool) {

	var testMutex sync.Mutex

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	receivers := make([]*resources.TwoPCReceiver, numNodes)
	completed := make([]bool, numNodes)
	errs := make(chan error, numNodes)

	for i := 0; i < numNodes; i++ {
		ctx := makeContext(i, receivers)
		replicaCtxs[i] = ctx

		ii := i
		go func() {
			runErr := runArchetype(ctx.Run)
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
			testMutex.Lock()
			completed[ii] = true
			testMutex.Unlock()
			log.Printf("Archetype %d has completed\n", ii)
			errs <- runErr
		}()
	}

	done := false
	if injectFailures {
		go func() {
			for {
				time.Sleep(1500 * time.Millisecond)
				testMutex.Lock()
				if done {
					testMutex.Unlock()
					break
				}
				indexToFail := rand.Intn(numNodes)
				if completed[indexToFail] {
					testMutex.Unlock()
					log.Printf("Already done: %d\n", indexToFail)
					continue
				}
				toFail := receivers[indexToFail]
				log.Printf("Simulate failure on node %d\n", indexToFail)
				testMutex.Unlock()
				resources.SimulateTwoPCFailure(toFail)
			}
			log.Println("Done with failure injection")
		}()
	}

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatalf("non-nil error from ANode archetype: %s", err)
		}
	}
	done = true

	for i := 0; i < numNodes; i++ {
		value, err := getCounterValue(replicaCtxs[i])
		if err != nil {
			version := resources.GetTwoPCVersion(receivers[i])
			t.Fatalf("Replica %d(version: %d) encountered error %s", i, version, err)
		}
		if value != tla.MakeTLANumber(int32(numNodes)) {
			t.Fatalf("Replica %d value %s was not equal to expected %d", i, value, numNodes)
		}
		resources.CloseTwoPCReceiver(receivers[i])
	}

}

func TestShCounterNoFailures(t *testing.T) {
	runTest(t, 20, false)
}

func TestShCounterFailures(t *testing.T) {
	runTest(t, 20, true)
}
