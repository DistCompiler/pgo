package raftkvs_test

import (
	"fmt"
	"log"
	"math/rand"
	"testing"
	"time"

	"example.org/raftkvs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
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

func makeServerCtxs(self tla.TLAValue, constants []distsys.MPCalContextConfigFn, netMaker mailboxMaker) (*distsys.MPCalContext, *distsys.MPCalContext) {
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
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(currentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("timer", raftkvs.TimerResourceMaker()),
		distsys.EnsureArchetypeRefParam("in", resources.OutputChannelMaker(srvCh)),
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
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outChan)),
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
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.TLA_TRUE),
	}
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext

	var srvCtxs []*distsys.MPCalContext
	var sndCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		srvCtx, sndCtx := makeServerCtxs(tla.MakeTLANumber(int32(i)), constants, netMaker)
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

func runLivenessTest(t *testing.T, numServers int, netMaker mailboxMaker) {
	numClients := 10
	numRequests := 100

	keys := []tla.TLAValue{
		tla.MakeTLAString("key0"),
		tla.MakeTLAString("key1"),
		tla.MakeTLAString("key2"),
		tla.MakeTLAString("key4"),
		tla.MakeTLAString("key5"),
		tla.MakeTLAString("key6"),
		tla.MakeTLAString("key7"),
		tla.MakeTLAString("key8"),
		tla.MakeTLAString("key9"),
	}
	iface := distsys.NewMPCalContextWithoutArchetype().IFace()
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.TLA_FALSE),
	}
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext

	var srvCtxs []*distsys.MPCalContext
	var sndCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		srvCtx, sndCtx := makeServerCtxs(tla.MakeTLANumber(int32(i)), constants, netMaker)
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

	time.Sleep(1 * time.Second)

	start := time.Now()

	var reqs []tla.TLAValue
	for i := 0; i < numRequests; i++ {
		r := rand.Intn(2)

		key := keys[i%len(keys)]
		if r == 0 {
			valueStr := fmt.Sprintf("value%d", i)
			value := tla.MakeTLAString(valueStr)
			putReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: raftkvs.Put(iface)},
				{Key: tla.MakeTLAString("key"), Value: key},
				{Key: tla.MakeTLAString("value"), Value: value},
			})
			inCh <- putReq
			reqs = append(reqs, putReq)
		} else {
			getReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: raftkvs.Get(iface)},
				{Key: tla.MakeTLAString("key"), Value: key},
			})
			inCh <- getReq
			reqs = append(reqs, getReq)
		}
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
		//log.Println(resp)
		if resp.ApplyFunction(tla.MakeTLAString("msuccess")).Equal(tla.TLA_FALSE) {
			t.Fatal("got an unsuccessful response")
		}
		j += 1
	}

	elapsed := time.Since(start)

	fmt.Printf("elapsed = %s, iops = %f\n", elapsed, float64(numRequests)/elapsed.Seconds())
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
	runLivenessTest(t, 3, resources.TCPMailboxesMaker)
}

func TestRaftKVS_RelaxedMailboxes(t *testing.T) {
	runLivenessTest(t, 3, resources.RelaxedMailboxesMaker)
}
