package shopcart

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	rand2 "math/rand"
	"sync"
	"time"
)

const ReqCnt = 1000
const (
	ADD    = 1 // Add operation
	REMOVE = 2 // Remove operation
)
const MaxRand = 100

type NodeChannels struct{
	In   chan tla.TLAValue
	Done chan struct{}
	Read chan struct{}
	Out  chan tla.TLAValue
}

func Benchmark(channels []NodeChannels) {
	start := time.Now()
	rand := rand2.New(rand2.NewSource(start.UnixNano()))

	var mu = new(sync.Mutex)
	var set = make(map[int]bool)
	var wg sync.WaitGroup

	for i := range channels {
		wg.Add(1)
		go func(nodeChans NodeChannels) {
			benchmarkANode(nodeChans, set, mu, rand)
			defer wg.Done()
		}(channels[i])
	}
	wg.Wait()
	elapsed := time.Since(start)
	log.Printf("duration: %s", elapsed)

	time.Sleep(30 * time.Second) // sleep to let the broadcast flood state

	finalVal := make([]int, 0)
	for k, v := range set {
		if v {
			finalVal = append(finalVal, k)
		}
	}
	log.Printf("reference: %v", finalVal)
}

func benchmarkANode(nodeChans NodeChannels, set map[int]bool, mu *sync.Mutex, rand *rand2.Rand) {
	for i := 0; i < ReqCnt; i++ {
		mu.Lock()
		var cmd int32
		elem := rand.Intn(MaxRand)
		if rand.Intn(2) == 0 {
			cmd = ADD
			set[elem] = true
		} else {
			cmd = REMOVE
			set[elem] = false
		}
		log.Printf("cmd: %d, elem: %d", cmd, elem)
		nodeChans.In <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("cmd"), Value: tla.MakeTLANumber(cmd)},
			{Key: tla.MakeTLAString("elem"), Value: tla.MakeTLANumber(int32(elem))},
		})
		//sleep := time.Duration(rand.Intn(1000))
		mu.Unlock()
		//time.Sleep(sleep * time.Millisecond)
	}
	nodeChans.Done <- struct{}{}
}