package shopcart

import (
	"benchmark"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	rand2 "math/rand"
	"os"
	"sync"
	"testing"
	"time"
)

const (
	ADD    = 1 // Add operation
	REMOVE = 2 // Remove operation
)

const maxInt = 10

func getANodeCtx(self tla.TLAValue, nodeAddrMap map[tla.TLAValue]string, inChan chan tla.TLAValue, broadcastInterval time.Duration, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, ANode, append(constants,
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inChan)),
		distsys.EnsureArchetypeRefParam("crdt", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			peers := make([]tla.TLAValue, 0)
			for nid := range nodeAddrMap {
				if nid != self {
					peers = append(peers, nid)
				}
			}
			return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
				return nodeAddrMap[index]
			}, broadcastInterval, resources.MakeAWORSet)
		})))...)
	return ctx
}

func runTest(t *testing.T, numNodes int, broadcastInterval time.Duration) {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
	}

	nodeAddrMap := make(map[tla.TLAValue]string, numNodes)
	for i := 1; i <= numNodes; i++ {
		portNum := 8000 + i
		addr := fmt.Sprintf("localhost:%d", portNum)
		nodeAddrMap[tla.MakeTLANumber(int32(i))] = addr
	}

	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	replicaInChans := make([]chan tla.TLAValue, numNodes)
	errs := make(chan error, numNodes)
	for i := 1; i <= numNodes; i++ {
		inChan := make(chan tla.TLAValue)
		ctx := getANodeCtx(tla.MakeTLANumber(int32(i)), nodeAddrMap, inChan, broadcastInterval, constants)
		replicaCtxs[i-1] = ctx
		replicaInChans[i-1] = inChan
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}
	}()

	var wg sync.WaitGroup
	rand2.Seed(time.Now().UnixNano())
	log.Printf("making requests\n")
	for i := range replicaInChans {
		wg.Add(1)
		go func(inChan chan tla.TLAValue) {
			makeRequests(inChan)
			defer wg.Done()
		}(replicaInChans[i])
	}
	wg.Wait()
	log.Printf("all requests made\n")

	<- time.After(20 * time.Second)
}

func makeRequests(inChan chan tla.TLAValue) {
	addElem := func(elem int) tla.TLAValue {
		return tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("cmd"), Value: tla.MakeTLANumber(ADD)},
			{Key: tla.MakeTLAString("elem"), Value: tla.MakeTLANumber(int32(elem))},
		})
	}
	remElem := func(elem int) tla.TLAValue {
		return tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("cmd"), Value: tla.MakeTLANumber(REMOVE)},
			{Key: tla.MakeTLAString("elem"), Value: tla.MakeTLANumber(int32(elem))},
		})
	}

	inChan <- addElem(rand2.Intn(maxInt))
	inChan <- remElem(rand2.Intn(maxInt))
	inChan <- addElem(rand2.Intn(maxInt))
	inChan <- remElem(rand2.Intn(maxInt))
}

func TestShopcartCRDT(t *testing.T) {
	if os.Getenv("PGO_BENCHMARK") == "" {
		runTest(t, 6, 5)
	} else {
		benchmark.TestAndReport(func(numNodes int, broadcastInterval time.Duration){
			runTest(t, numNodes, broadcastInterval)
		})
	}
}