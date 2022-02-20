package raftkvs_test

import (
	"fmt"
	"log"
	"math/rand"
	"sync"
	"testing"
	"time"

	"example.org/raftkvs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

type mailboxMaker func(fn resources.MailboxesAddressMappingFn) distsys.ArchetypeResourceMaker

func getNetworkMaker(self tla.TLAValue, maker mailboxMaker) distsys.ArchetypeResourceMaker {
	return maker(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			port := 8000 + aid
			addr := fmt.Sprintf("localhost:%d", port)
			return kind, addr
		},
	)
}

const monAddr = "localhost:9000"
const requestTimeout = 2 * time.Second

func makeServerCtxs(self tla.TLAValue, constants []distsys.MPCalContextConfigFn, netMaker mailboxMaker, db *badger.DB) (*distsys.MPCalContext, *distsys.MPCalContext) {
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	stateMaker := resources.LocalSharedMaker(raftkvs.Follower(iface))
	nextIndexMaker := resources.LocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(1)
		}),
	)
	logMaker := resources.LocalSharedMaker(tla.MakeTLATuple())
	currentTermMaker := resources.LocalSharedMaker(tla.MakeTLANumber(1))
	commitIndexMaker := resources.LocalSharedMaker(tla.MakeTLANumber(0))
	votedForMaker := distsys.LocalArchetypeResourceMaker(raftkvs.Nil(iface))

	pCurrentTermMaker := resources.PersistentResourceMaker(fmt.Sprintf("Server.%v.currentTerm", self), db, currentTermMaker)
	pVotedForMaker := resources.PersistentResourceMaker(fmt.Sprintf("Server%v.votedFor", self), db, votedForMaker)
	plogMaker := raftkvs.PersistentLogMaker(fmt.Sprintf("Server%v.plog", self), db)

	mapMaker := func(maker distsys.ArchetypeResourceMaker) distsys.ArchetypeResourceMaker {
		return resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if index.Equal(self) {
				return maker
			}
			panic("wrong index")
		})
	}

	srvCh := make(chan tla.TLAValue, 100)

	srvCtx := distsys.NewMPCalContext(self, raftkvs.AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, netMaker)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeDerivedRefParam("netLen", "net", resources.MailboxesLengthMaker),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.PlaceHolderResourceMaker()),
		distsys.EnsureArchetypeRefParam("state", mapMaker(stateMaker)),
		distsys.EnsureArchetypeRefParam("nextIndex", mapMaker(nextIndexMaker)),
		distsys.EnsureArchetypeRefParam("log", mapMaker(logMaker)),
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(pCurrentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("timer", raftkvs.TimerResourceMaker()),
		distsys.EnsureArchetypeRefParam("in", resources.OutputChannelMaker(srvCh)),
		distsys.EnsureArchetypeRefParam("votedFor", pVotedForMaker),
		distsys.EnsureArchetypeRefParam("plog", mapMaker(plogMaker)),
	)

	sndSelf := tla.TLA_PlusSymbol(self, iface.GetConstant("NumServers")())
	sndCtx := distsys.NewMPCalContext(sndSelf, raftkvs.AServerSender,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(sndSelf, netMaker)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeRefParam("netEnabled",
			resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
				return distsys.LocalArchetypeResourceMaker(tla.TLA_TRUE)
			})),
		distsys.EnsureArchetypeValueParam("sid", self),
		distsys.EnsureArchetypeRefParam("state", mapMaker(stateMaker)),
		distsys.EnsureArchetypeRefParam("nextIndex", mapMaker(nextIndexMaker)),
		distsys.EnsureArchetypeRefParam("log", mapMaker(logMaker)),
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(currentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("in", raftkvs.CustomInChanMaker(srvCh)),
	)
	return srvCtx, sndCtx
}

func makeClientCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	inChan, outChan, timeoutCh chan tla.TLAValue, netMaker mailboxMaker) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, raftkvs.AClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, netMaker)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inChan)),
		distsys.EnsureArchetypeRefParam("out", resources.SingleOutputChannelMaker(outChan)),
		distsys.EnsureArchetypeDerivedRefParam("netLen", "net", resources.MailboxesLengthMaker),
		distsys.EnsureArchetypeRefParam("timeout", resources.InputChannelMaker(timeoutCh)),
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

func runSafetyTest(t *testing.T, numServers int, numFailures int, netMaker mailboxMaker) {
	numClients := 1
	numRequestPairs := 3
	numRequests := numRequestPairs * 2

	keys := []tla.TLAValue{
		tla.MakeTLAString("key1"),
		tla.MakeTLAString("key2"),
		tla.MakeTLAString("key3"),
	}
	iface := distsys.NewMPCalContextWithoutArchetype().IFace()
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.TLA_TRUE),
	}, raftkvs.PersistentLogConstantDefs)
	mon := setupMonitor()
	errs := make(chan error)

	db, err := badger.Open(badger.DefaultOptions("/tmp/badger"))
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := db.Close(); err != nil {
			log.Println(err)
		}
	}()

	var ctxs []*distsys.MPCalContext

	var srvCtxs []*distsys.MPCalContext
	var sndCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		srvCtx, sndCtx := makeServerCtxs(tla.MakeTLANumber(int32(i)), constants, netMaker, db)
		srvCtxs = append(srvCtxs, srvCtx)
		sndCtxs = append(sndCtxs, sndCtx)
		ctxs = append(ctxs, srvCtx, sndCtx)
		go func() {
			err := mon.RunArchetype(srvCtx)
			log.Printf("archetype = %v, err = %v", srvCtx.IFace().Self(), err)
			errs <- err
		}()
		go func() {
			err := mon.RunArchetype(sndCtx)
			log.Printf("archetype = %v, err = %v", sndCtx.IFace().Self(), err)
			errs <- err
		}()
	}

	inCh := make(chan tla.TLAValue, numRequests)
	outCh := make(chan tla.TLAValue, numRequests)
	timeoutCh := make(chan tla.TLAValue)
	var clientCtxs []*distsys.MPCalContext
	for i := 2*numServers + 1; i <= 2*numServers+numClients; i++ {
		clientCtx := makeClientCtx(tla.MakeTLANumber(int32(i)), constants, inCh, outCh, timeoutCh, netMaker)
		clientCtxs = append(clientCtxs, clientCtx)
		ctxs = append(ctxs, clientCtx)
		go func() {
			err := clientCtx.Run()
			log.Printf("archetype = %v, err = %v", clientCtx.IFace().Self(), err)
			errs <- err
		}()
	}

	defer func() {
		for i := 0; i < len(srvCtxs); i++ {
			srvCtxs[i].Stop()
			sndCtxs[i].Stop()
		}
		for _, ctx := range clientCtxs {
			ctx.Stop()
		}
		for i := 0; i < len(ctxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %v", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}()

	if numFailures > 0 {
		go func() {
			d := rand.Intn(3000)
			time.Sleep(time.Duration(d) * time.Millisecond)
			for i := 0; i < numFailures; i++ {
				srvCtxs[i].Stop()
				sndCtxs[i].Stop()
			}
		}()
	}

	time.Sleep(1 * time.Second)
	var reqs []tla.TLAValue
	for i := 0; i < numRequestPairs; i++ {
		key := keys[i%len(keys)]
		valueStr := fmt.Sprintf("value%d", i)
		value := tla.MakeTLAString(valueStr)
		putReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: raftkvs.Put(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
			{Key: tla.MakeTLAString("value"), Value: value},
		})
		inCh <- putReq
		reqs = append(reqs, putReq)

		getReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: raftkvs.Get(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
		})
		inCh <- getReq
		reqs = append(reqs, getReq)
	}

	j := 0
	for j < numRequests {
		var resp tla.TLAValue
		select {
		case resp = <-outCh:
		case <-time.After(requestTimeout):
			timeoutCh <- tla.TLA_TRUE
			continue
		}
		log.Println(resp)
		if resp.ApplyFunction(tla.MakeTLAString("msuccess")).Equal(tla.TLA_FALSE) {
			t.Fatal("got an unsuccessful response")
		}

		typ := resp.ApplyFunction(tla.MakeTLAString("mtype"))
		body := resp.ApplyFunction(tla.MakeTLAString("mresponse"))
		key := body.ApplyFunction(tla.MakeTLAString("key"))
		value := body.ApplyFunction(tla.MakeTLAString("value"))
		reqKey := reqs[j].ApplyFunction(tla.MakeTLAString("key"))
		if !key.Equal(reqKey) {
			t.Fatalf("wrong response key, expected: %v, got: %v", reqKey, key)
		}
		if typ.Equal(raftkvs.ClientGetResponse(iface)) {
			reqValue := reqs[j-1].ApplyFunction(tla.MakeTLAString("value"))
			if !value.Equal(reqValue) {
				t.Fatalf("wrong response value, expected: %v, got: %v", reqValue, value)
			}
		} else if typ.Equal(raftkvs.ClientPutRequest(iface)) {
			reqValue := reqs[j].ApplyFunction(tla.MakeTLAString("value"))
			if !value.Equal(reqValue) {
				t.Fatalf("wrong response value, expected: %v, got: %v", reqValue, value)
			}
		}
		j += 1
	}
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
			{Key: tla.MakeTLAString("type"), Value: raftkvs.Put(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
			{Key: tla.MakeTLAString("value"), Value: value},
		})
		return putReq
	} else if reqType == getReq {
		getReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: raftkvs.Get(iface)},
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

func runLivenessTest(t *testing.T, numServers int, netMaker mailboxMaker) {
	numClients := 10
	numRequests := 1000
	keySize := 100

	iface := distsys.NewMPCalContextWithoutArchetype().IFace()
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.TLA_FALSE),
	}, raftkvs.PersistentLogConstantDefs)
	mon := setupMonitor()
	errs := make(chan error)

	db, err := badger.Open(badger.DefaultOptions("/tmp/badger"))
	//db, err := badger.Open(badger.DefaultOptions("").WithInMemory(true))
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := db.Close(); err != nil {
			log.Println(err)
		}
	}()

	var ctxs []*distsys.MPCalContext

	var srvCtxs []*distsys.MPCalContext
	var sndCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		srvCtx, sndCtx := makeServerCtxs(tla.MakeTLANumber(int32(i)), constants, netMaker, db)
		srvCtxs = append(srvCtxs, srvCtx)
		sndCtxs = append(sndCtxs, sndCtx)
		ctxs = append(ctxs, srvCtx, sndCtx)
		go func() {
			err := mon.RunArchetype(srvCtx)
			log.Printf("archetype = %v, err = %v", srvCtx.IFace().Self(), err)
			errs <- err
		}()
		go func() {
			err := mon.RunArchetype(sndCtx)
			log.Printf("archetype = %v, err = %v", sndCtx.IFace().Self(), err)
			errs <- err
		}()
	}

	var inChs []chan tla.TLAValue
	var outChs []chan tla.TLAValue
	timeoutCh := make(chan tla.TLAValue)
	var clientCtxs []*distsys.MPCalContext
	for i := 2*numServers + 1; i <= 2*numServers+numClients; i++ {
		inCh := make(chan tla.TLAValue, numRequests)
		outCh := make(chan tla.TLAValue, numRequests)
		inChs = append(inChs, inCh)
		outChs = append(outChs, outCh)

		clientCtx := makeClientCtx(tla.MakeTLANumber(int32(i)), constants, inCh, outCh, timeoutCh, netMaker)
		clientCtxs = append(clientCtxs, clientCtx)
		ctxs = append(ctxs, clientCtx)
		go func() {
			err := clientCtx.Run()
			log.Printf("archetype = %v, err = %v", clientCtx.IFace().Self(), err)
			errs <- err
		}()
	}

	defer func() {
		for i := 0; i < len(srvCtxs); i++ {
			srvCtxs[i].Stop()
			sndCtxs[i].Stop()
		}
		for _, ctx := range clientCtxs {
			ctx.Stop()
		}
		for i := 0; i < len(ctxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %v", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}()

	time.Sleep(1 * time.Second)

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

				var resp tla.TLAValue
			outerLoop:
				for {
					select {
					case resp = <-outChs[chIdx]:
						break outerLoop
					case <-time.After(requestTimeout):
						timeoutCh <- tla.TLA_TRUE
						continue
					}
				}
				if resp.ApplyFunction(tla.MakeTLAString("msuccess")).Equal(tla.TLA_FALSE) {
					t.Error("got an unsuccessful response")
					return
				}
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

func TestRaftKVS_ThreeServers(t *testing.T) {
	runSafetyTest(t, 3, 0, resources.TCPMailboxesMaker)
}

func TestRaftKVS_ThreeServersOneFailing(t *testing.T) {
	runSafetyTest(t, 3, 1, resources.TCPMailboxesMaker)
}

func TestRaftKVS_FiveServers(t *testing.T) {
	runSafetyTest(t, 5, 0, resources.TCPMailboxesMaker)
}

func TestRaftKVS_FiveServersOneFailing(t *testing.T) {
	runSafetyTest(t, 5, 1, resources.TCPMailboxesMaker)
}

func TestRaftKVS_ThreeServersThreeClients(t *testing.T) {
	//runLivenessTest(t, 3, resources.TCPMailboxesMaker)
}

func TestRaftKVS_RelaxedMailboxes(t *testing.T) {
	//runLivenessTest(t, 3, resources.RelaxedMailboxesMaker)
}
