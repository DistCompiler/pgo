package shopcart

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	rand2 "math/rand"
	"sync"
	"time"
)

const testTimeout = 20 * time.Second

const AddReqCnt = 10
const RemReqCnt = 5
const (
	ADD    = 1 // Add operation
	REMOVE = 2 // Remove operation
)
const MaxRand = 100

type NodeChannels struct {
	In   chan tla.TLAValue
	Done chan struct{}
}

func Benchmark(channels []NodeChannels, outChan chan tla.TLAValue) {
	start := time.Now()
	rand2.Seed(start.UnixNano())

	var mu = new(sync.Mutex)
	var set = make(map[int]bool)
	var wg sync.WaitGroup

	for i := range channels {
		wg.Add(1)
		go func(nodeChans NodeChannels) {
			benchmarkANode(nodeChans, set, mu)
			defer wg.Done()
		}(channels[i])
	}
	wg.Wait()
	requestComplete := time.Now()
	elapsed := time.Since(start)
	log.Printf("duration until request complete: %s", elapsed)

	var finalSet tla.TLAValue
	select {
	case finalSet = <-outChan:
	case <-time.After(testTimeout):
		log.Fatal("timeout before convergence")
	}

	elapsed = time.Since(requestComplete)
	log.Printf("duration until converge: %s", elapsed)
	log.Printf("final state: %v (%d)", finalSet, finalSet.AsSet().Len())

	arr := make([]tla.TLAValue, 0)
	for k, v := range set {
		if v {
			arr = append(arr, tla.MakeTLANumber(int32(k)))
		}
	}
	refSet := tla.MakeTLASet(arr...)
	log.Printf("ref state: %v (%d)", refSet, refSet.AsSet().Len())
}

func benchmarkANode(nodeChans NodeChannels, refSet map[int]bool, mu *sync.Mutex) {
	for i := 0; i < AddReqCnt; i++ {
		mu.Lock()
		elem := rand2.Intn(MaxRand)
		nodeChans.In <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("cmd"), Value: tla.MakeTLANumber(ADD)},
			{Key: tla.MakeTLAString("elem"), Value: tla.MakeTLANumber(int32(elem))},
		})
		refSet[elem] = true
		mu.Unlock()
	}
	time.Sleep(5 * time.Second)
	for i := 0; i < RemReqCnt; i++ {
		mu.Lock()
		elem := rand2.Intn(MaxRand)
		nodeChans.In <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("cmd"), Value: tla.MakeTLANumber(REMOVE)},
			{Key: tla.MakeTLAString("elem"), Value: tla.MakeTLANumber(int32(elem))},
		})
		refSet[elem] = false
		mu.Unlock()
	}
	nodeChans.Done <- struct{}{}
}
