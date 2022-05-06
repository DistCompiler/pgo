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
	"github.com/benbjohnson/immutable"
	"github.com/dgraph-io/badger/v3"
)

const monAddr = "localhost:9000"
const requestTimeout = 200 * time.Millisecond

const fdPullInterval = 200 * time.Millisecond
const fdTimeout = 100 * time.Millisecond

const mailboxesDialTimeout = 50 * time.Millisecond
const mailboxesReadTimeout = 50 * time.Millisecond
const mailboxesWriteTimeout = 50 * time.Millisecond

const leaderElectionTimeout = 150 * time.Millisecond
const leaderElectionTimeoutOffset = 150 * time.Millisecond

const appendEntriesSendInterval = 10 * time.Millisecond

const sharedResourceTimeout = 2 * time.Millisecond

const inputChannelReadTimeout = 2 * time.Millisecond

const valueSize = 10

type mailboxesMaker func(fn resources.MailboxesAddressMappingFn, opts ...resources.MailboxesOption) *resources.Mailboxes

func newNetwork(self tla.TLAValue, maker mailboxesMaker) *resources.Mailboxes {
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
		resources.WithMailboxesDialTimeout(mailboxesDialTimeout),
		resources.WithMailboxesReadTimeout(mailboxesReadTimeout),
		resources.WithMailboxesWriteTimeout(mailboxesWriteTimeout),
	)
}

func newServerCtxs(srvId tla.TLAValue, constants []distsys.MPCalContextConfigFn, mboxMaker mailboxesMaker, db *badger.DB) []*distsys.MPCalContext {
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	toMap := func(res distsys.ArchetypeResource) distsys.ArchetypeResource {
		return resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			if index.Equal(srvId) {
				return res
			}
			panic("wrong index")
		})
	}

	fdMap := immutable.NewMap(tla.TLAValueHasher{})
	fdProvider := func(index tla.TLAValue) distsys.ArchetypeResource {
		if singleFd, ok := fdMap.Get(index); ok {
			return singleFd.(*resources.SingleFailureDetector)
		}
		singleFd := resources.NewSingleFailureDetector(index, monAddr,
			resources.WithFailureDetectorPullInterval(fdPullInterval),
			resources.WithFailureDetectorTimeout(fdTimeout),
		)
		fdMap = fdMap.Set(index, singleFd)
		return singleFd
	}

	stateMaker := resources.NewLocalSharedMaker(raftkvs.Follower(iface),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	currentTermMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(1),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	logMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))

	commitIndexMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(0),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	nextIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(1)
		}),
		resources.WithLocalSharedTimeout(sharedResourceTimeout),
	)
	matchIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(0)
		}),
		resources.WithLocalSharedTimeout(sharedResourceTimeout),
	)
	votedForMaker := resources.NewLocalSharedMaker(raftkvs.Nil(iface),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	votesRespondedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	votesGrantedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))

	leaderMaker := resources.NewLocalSharedMaker(raftkvs.Nil(iface),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))
	smMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.KeySet(iface)}, func(t []tla.TLAValue) tla.TLAValue {
			return raftkvs.Nil(iface)
		}),
		resources.WithLocalSharedTimeout(sharedResourceTimeout),
	)
	smDomainMaker := resources.NewLocalSharedMaker(raftkvs.KeySet(iface),
		resources.WithLocalSharedTimeout(sharedResourceTimeout))

	leaderTimeout := raftkvs.NewTimerResource(leaderElectionTimeout, leaderElectionTimeoutOffset)

	genResources := func(self tla.TLAValue) []distsys.MPCalContextConfigFn {
		net := newNetwork(self, mboxMaker)
		// netLen := resources.NewMailboxesLength(net)
		netLen := distsys.NewLocalArchetypeResource(tla.MakeTLANumber(0))
		netEnabled := resources.NewPlaceHolder()
		fd := resources.NewIncMap(fdProvider)

		state := stateMaker()
		currentTerm := resources.NewPersistent(fmt.Sprintf("Server%v.currentTerm", srvId.AsNumber()), db,
			currentTermMaker(),
		)
		log := logMaker()
		plog := raftkvs.NewPersistentLog(fmt.Sprintf("Server%v.plog", srvId.AsNumber()), db)
		commitIndex := commitIndexMaker()
		nextIndex := nextIndexMaker()
		matchIndex := matchIndexMaker()
		votedFor := resources.NewPersistent(fmt.Sprintf("Server%v.votedFor", srvId.AsNumber()), db,
			votedForMaker(),
		)
		votesResponded := votesRespondedMaker()
		votesGranted := votesGrantedMaker()

		leader := leaderMaker()
		sm := smMaker()
		smDomain := smDomainMaker()

		resourcesConfig := []distsys.MPCalContextConfigFn{
			distsys.EnsureArchetypeValueParam("srvId", srvId),
			distsys.EnsureArchetypeRefParam("net", net),
			// distsys.EnsureArchetypeRefParam("netLen", netLen),
			distsys.EnsureArchetypeRefParam("netLen", toMap(netLen)),
			distsys.EnsureArchetypeRefParam("netEnabled", netEnabled),
			distsys.EnsureArchetypeRefParam("fd", fd),
			distsys.EnsureArchetypeRefParam("state", toMap(state)),
			distsys.EnsureArchetypeRefParam("currentTerm", toMap(currentTerm)),
			distsys.EnsureArchetypeRefParam("log", toMap(log)),
			distsys.EnsureArchetypeRefParam("plog", toMap(plog)),
			distsys.EnsureArchetypeRefParam("commitIndex", toMap(commitIndex)),
			distsys.EnsureArchetypeRefParam("nextIndex", toMap(nextIndex)),
			distsys.EnsureArchetypeRefParam("matchIndex", toMap(matchIndex)),
			distsys.EnsureArchetypeRefParam("votedFor", toMap(votedFor)),
			distsys.EnsureArchetypeRefParam("votesResponded", toMap(votesResponded)),
			distsys.EnsureArchetypeRefParam("votesGranted", toMap(votesGranted)),
			distsys.EnsureArchetypeRefParam("leader", toMap(leader)),
			distsys.EnsureArchetypeRefParam("sm", toMap(sm)),
			distsys.EnsureArchetypeRefParam("smDomain", toMap(smDomain)),
			distsys.EnsureArchetypeRefParam("leaderTimeout", leaderTimeout),
		}
		return resourcesConfig
	}

	appendEntriesCh := make(chan tla.TLAValue, 100)

	srvIdInt := srvId.AsNumber()
	numServersInt := iface.GetConstant("NumServers")().AsNumber()

	serverSelf := srvId
	serverCtx := distsys.NewMPCalContext(
		serverSelf, raftkvs.AServer,
		append(
			genResources(serverSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
		)...,
	)

	serverRequestVoteSelf := tla.MakeTLANumber(srvIdInt + 1*numServersInt)
	serverRequestVoteCtx := distsys.NewMPCalContext(
		serverRequestVoteSelf, raftkvs.AServerRequestVote,
		append(
			genResources(serverRequestVoteSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
		)...,
	)

	serverAppendEntriesSelf := tla.MakeTLANumber(srvIdInt + 2*numServersInt)
	serverAppendEntriesCtx := distsys.NewMPCalContext(
		serverAppendEntriesSelf, raftkvs.AServerAppendEntries,
		append(
			genResources(serverAppendEntriesSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh",
				raftkvs.NewCustomInChan(appendEntriesCh, appendEntriesSendInterval)),
		)...,
	)

	serverAdvanceCommitIndexSelf := tla.MakeTLANumber(srvIdInt + 3*numServersInt)
	serverAdvanceCommitIndexCtx := distsys.NewMPCalContext(
		serverAdvanceCommitIndexSelf, raftkvs.AServerAdvanceCommitIndex,
		append(
			genResources(serverAdvanceCommitIndexSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
		)...,
	)

	serverBecomeLeaderSelf := tla.MakeTLANumber(srvIdInt + 4*numServersInt)
	serverBecomeLeaderCtx := distsys.NewMPCalContext(
		serverBecomeLeaderSelf, raftkvs.AServerBecomeLeader,
		append(
			genResources(serverBecomeLeaderSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
		)...,
	)

	return []*distsys.MPCalContext{
		serverCtx, serverRequestVoteCtx, serverAppendEntriesCtx, serverAdvanceCommitIndexCtx,
		serverBecomeLeaderCtx,
	}
}

func newClientCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	reqCh, respCh, timeoutCh chan tla.TLAValue, mboxMaker mailboxesMaker) *distsys.MPCalContext {

	net := newNetwork(self, mboxMaker)
	netLen := resources.NewMailboxesLength(net)
	fd := resources.NewFailureDetector(
		func(index tla.TLAValue) string {
			return monAddr
		},
		resources.WithFailureDetectorPullInterval(fdPullInterval),
		resources.WithFailureDetectorTimeout(fdTimeout),
	)
	reqChRes := resources.NewInputChan(reqCh, resources.WithInputChanReadTimeout(inputChannelReadTimeout))
	respChRes := resources.NewOutputChan(respCh)
	timeoutChRes := resources.NewInputChan(timeoutCh, resources.WithInputChanReadTimeout(inputChannelReadTimeout))

	ctx := distsys.NewMPCalContext(
		self, raftkvs.AClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", net),
		distsys.EnsureArchetypeRefParam("netLen", netLen),
		distsys.EnsureArchetypeRefParam("fd", fd),
		distsys.EnsureArchetypeRefParam("reqCh", reqChRes),
		distsys.EnsureArchetypeRefParam("respCh", respChRes),
		distsys.EnsureArchetypeRefParam("timeout", timeoutChRes),
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

func runSafetyTest(t *testing.T, numServers int, netMaker mailboxesMaker, numNodeFail int) {
	numClients := 1
	numRequestPairs := 10
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
	}, raftkvs.PersistentLogConstantDefs, raftkvs.LeaderTimeoutConstantDefs)
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

	var allServersCtxs [][]*distsys.MPCalContext
	var ctxs []*distsys.MPCalContext

	for i := 1; i <= numServers; i++ {
		serverCtxs := newServerCtxs(tla.MakeTLANumber(int32(i)), constants, netMaker, db)
		allServersCtxs = append(allServersCtxs, serverCtxs)
		ctxs = append(ctxs, serverCtxs...)
		for i := range serverCtxs {
			ctx := serverCtxs[i]
			go func() {
				err := mon.RunArchetype(ctx)
				log.Printf("archetype = %v, err = %v", ctx.IFace().Self(), err)
				errs <- err
			}()
		}
	}

	reqCh := make(chan tla.TLAValue, numRequests)
	respCh := make(chan tla.TLAValue, numRequests)
	timeoutCh := make(chan tla.TLAValue)
	for i := 6*numServers + 1; i <= 6*numServers+numClients; i++ {
		clientCtx := newClientCtx(tla.MakeTLANumber(int32(i)), constants, reqCh, respCh, timeoutCh, netMaker)
		ctxs = append(ctxs, clientCtx)
		go func() {
			err := clientCtx.Run()
			log.Printf("archetype = %v, err = %v", clientCtx.IFace().Self(), err)
			errs <- err
		}()
	}

	defer func() {
		for _, ctx := range ctxs {
			log.Printf("stopping archetype: %v", ctx.IFace().Self())
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

	log.Println("waiting 3 second")
	time.Sleep(3 * time.Second)

	if numNodeFail > 0 {
		go func() {
			d := rand.Intn(3500)
			time.Sleep(time.Duration(d) * time.Millisecond)
			for i := 0; i < numNodeFail; i++ {
				for _, ctx := range allServersCtxs[i] {
					ctx.Stop()
					log.Printf("archetype %v crashed", ctx.IFace().Self())
				}
			}
		}()
	}

	log.Println("sending client requests")
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
		reqCh <- putReq
		reqs = append(reqs, putReq)

		getReq := tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("type"), Value: raftkvs.Get(iface)},
			{Key: tla.MakeTLAString("key"), Value: key},
		})
		reqCh <- getReq
		reqs = append(reqs, getReq)
	}

	log.Printf("numRequests = %d", numRequests)

	j := 0
	for j < numRequests {
		// log.Printf("waiting for response %d", j+1)
		if len(timeoutCh) != 0 {
			t.Fatal("timeoutCh is not empty")
		}

		var resp tla.TLAValue
		select {
		case resp = <-respCh:
		case <-time.After(requestTimeout):
			log.Printf("sending timeout for response %d", j+1)
			select {
			case timeoutCh <- tla.TLA_TRUE:
				log.Printf("sent timeout for response %d", j+1)
			case <-time.After(requestTimeout):
			}
			continue
		}

		log.Printf("response %d: %v", j+1, resp)

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

func TestSafety_ThreeServers(t *testing.T) {
	runSafetyTest(t, 3, resources.NewRelaxedMailboxes, 0)
}

func TestSafety_FiveServers(t *testing.T) {
	runSafetyTest(t, 5, resources.NewRelaxedMailboxes, 0)
}

func TestSafety_SevenServers(t *testing.T) {
	runSafetyTest(t, 7, resources.NewRelaxedMailboxes, 0)
}

func TestSafety_OneFailling_ThreeServers(t *testing.T) {
	runSafetyTest(t, 3, resources.NewRelaxedMailboxes, 1)
}

func TestSafety_OneFailling_FiveServers(t *testing.T) {
	runSafetyTest(t, 5, resources.NewRelaxedMailboxes, 1)
}

func TestSafety_TwoFailling_FiveServers(t *testing.T) {
	runSafetyTest(t, 5, resources.NewRelaxedMailboxes, 2)
}
