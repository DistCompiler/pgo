package kvs

import (
	"fmt"
	"log"
	"math/rand"
	"sync"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNetworkMaker(nodeIndex int) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesMaker(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if nodeIndex == int(idx.AsNumber()) {
				kind = resources.MailboxesLocal
			}
			port := 9000 + idx.AsNumber()
			addr := fmt.Sprintf("localhost:%d", port)
			return kind, addr
		},
	)
}

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 8000+nodeIndex)
}

func getArchetypeID(nodeIndex int) tla.TLAValue {
	return tla.MakeTLANumber(int32(nodeIndex))
}

func getReplicas(selfIndex int, numNodes int) []resources.ReplicaHandle {
	var replicas []resources.ReplicaHandle
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		globalID := i
		handle := resources.MakeRPCReplicaHandle(getListenAddress(globalID), getArchetypeID(globalID))
		replicas = append(replicas, &handle)
	}
	return replicas
}

func makeServerContext(nodeIndex int, numServers int, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	replicas := getReplicas(nodeIndex, numServers)
	twoPCMaker := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLAFunction([]tla.TLAValue{tla.MakeTLASet()}, nil),
		getListenAddress(nodeIndex),
		replicas,
		getArchetypeID(nodeIndex),
		nil,
	)

	return distsys.NewMPCalContext(getArchetypeID(nodeIndex), AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("kvs", twoPCMaker),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(nodeIndex)),
	)
}

const monAddr = "localhost:9500"

func makeClientCtx(nodeIndex int, constants []distsys.MPCalContextConfigFn,
	inCh, outCh chan tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(getArchetypeID(nodeIndex), AClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(nodeIndex)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inCh)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
	)
	return ctx
}

func setupMonitor() *resources.Monitor {
	mon := resources.NewMonitor(monAddr)
	go func() {
		if err := mon.ListenAndServe(); err != nil {
			log.Fatal(err)
		}
	}()
	return mon
}

var letterRunes = []rune("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

const valueSize = 10

func RandStringRunes(n int) string {
	b := make([]rune, n)
	for i := range b {
		b[i] = letterRunes[rand.Intn(len(letterRunes))]
	}
	return string(b)
}

type reqType int

const (
	putReq reqType = iota + 1
	getReq
)

func getRequest(reqType reqType, key tla.TLAValue, iface distsys.ArchetypeInterface) tla.TLAValue {
	if reqType == putReq {
		valueStr := RandStringRunes(valueSize)
		value := tla.MakeTLAString(valueStr)
		putReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: Put(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
			{Key: tla.MakeTLAString("value"), Value: value},
		})
		return putReq
	} else if reqType == getReq {
		getReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: Get(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
		})
		return getReq
	}
	panic("invalid request type")
}

type atomicCounter struct {
	lock sync.RWMutex
	val  int
}

func (ac *atomicCounter) get() int {
	ac.lock.RLock()
	defer ac.lock.RUnlock()
	return ac.val
}

func (ac *atomicCounter) inc() {
	ac.lock.Lock()
	defer ac.lock.Unlock()
	ac.val += 1
}

func runTest(t *testing.T, numServers int, numClients int) {
	numRequests := 10000
	keySize := 100

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
	}
	mon := setupMonitor()

	var ctxs []*distsys.MPCalContext
	errs := make(chan error)

	var serverCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		ctx := makeServerContext(i, numServers, constants)
		serverCtxs = append(serverCtxs, ctx)
		ctxs = append(ctxs, ctx)

		go func() {
			errs <- mon.RunArchetype(ctx)
		}()
	}

	var inChs []chan tla.TLAValue
	var outChs []chan tla.TLAValue
	for i := numServers + 1; i <= numServers+numClients; i++ {
		inCh := make(chan tla.TLAValue, numRequests)
		outCh := make(chan tla.TLAValue, numRequests)
		inChs = append(inChs, inCh)
		outChs = append(outChs, outCh)

		ctx := makeClientCtx(i, constants, inCh, outCh)
		ctxs = append(ctxs, ctx)

		go func() {
			errs <- ctx.Run()
		}()
	}
	defer func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		log.Println("stop done")
		for range ctxs {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %v", err)
			}
		}
	}()

	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	var keys []tla.TLAValue
	for i := 0; i < keySize; i++ {
		key := tla.MakeTLAString(fmt.Sprintf("key%d", i))
		inChs[0] <- getRequest(putReq, key, iface)
		<-outChs[0]

		keys = append(keys, key)
	}

	log.Println("setup done")

	start := time.Now()

	var latencies []time.Duration
	var lock sync.Mutex

	reqCnt := atomicCounter{val: 0}
	var wg sync.WaitGroup
	for k := 0; k < numClients; k++ {
		chIdx := k
		wg.Add(1)

		go func() {
			for reqCnt.get() < numRequests {
				key := keys[rand.Intn(len(keys))]
				r := rand.Intn(2) + 1
				req := getRequest(reqType(r), key, iface)

				reqStart := time.Now()
				inChs[chIdx] <- req
				<-outChs[chIdx]
				reqElapsed := time.Since(reqStart)

				lock.Lock()
				latencies = append(latencies, reqElapsed)
				lock.Unlock()

				reqCnt.inc()
			}
			wg.Done()
		}()
	}

	wg.Wait()

	elapsed := time.Since(start)
	iops := float64(numRequests) / elapsed.Seconds()
	avgLatency := average(latencies)

	fmt.Printf("elapsed = %s, iops = %f, average latency = %s\n", elapsed, iops, avgLatency)
}

func average(a []time.Duration) time.Duration {
	var tot time.Duration

	for _, e := range a {
		tot += e
	}
	return time.Duration(int64(tot) / int64(len(a)))
}

func TestKVS(t *testing.T) {
	runTest(t, 3, 10)
}
