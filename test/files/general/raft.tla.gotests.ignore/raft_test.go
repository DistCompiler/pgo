package raft_test

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"log"
	"math/rand"
	"testing"
	"time"

	"example.org/raft"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNetworkMaker(self tla.TLAValue) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesMaker(
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

func makeServerCtxs(self tla.TLAValue, constants []distsys.MPCalContextConfigFn) (*distsys.MPCalContext, *distsys.MPCalContext) {
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	stateMaker := resources.LocalSharedMaker(raft.Follower(iface))
	nextIndexMaker := resources.LocalSharedMaker(tla.MakeTLAFunction([]tla.TLAValue{raft.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
		return tla.MakeTLANumber(1)
	}))
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

	srvCtx := distsys.NewMPCalContext(self, raft.AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self)),
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
		distsys.EnsureArchetypeRefParam("timer", raft.TimerResourceMaker()),
		distsys.EnsureArchetypeRefParam("in", resources.OutputChannelMaker(srvCh)),
	)

	sndSelf := tla.TLA_PlusSymbol(self, iface.GetConstant("NumServers")())
	sndCtx := distsys.NewMPCalContext(sndSelf, raft.AServerSender,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(sndSelf)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			return distsys.LocalArchetypeResourceMaker(tla.TLA_TRUE)
		})),
		distsys.EnsureArchetypeValueParam("sid", self),
		distsys.EnsureArchetypeRefParam("state", mapMaker(stateMaker)),
		distsys.EnsureArchetypeRefParam("nextIndex", mapMaker(nextIndexMaker)),
		distsys.EnsureArchetypeRefParam("log", mapMaker(logMaker)),
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(currentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("in", raft.CustomInChanMaker(srvCh)),
	)
	return srvCtx, sndCtx
}

func makeClientCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn, inChan chan tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, raft.ALoopClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inChan)),
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

const numRequests = 30
const waitTime = 5 * time.Second

func runTest(t *testing.T, numServers int, numClients int, numFailures int) {
	traceRecorder := trace.MakeLocalFileRecorder(fmt.Sprintf("raft_%d_%d_%d.txt", numServers, numClients, numFailures))
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.TLA_TRUE),
		distsys.SetTraceRecorder(traceRecorder),
	}
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext

	var srvCtxs []*distsys.MPCalContext
	var sndCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		srvCtx, sndCtx := makeServerCtxs(tla.MakeTLANumber(int32(i)), constants)
		srvCtxs = append(srvCtxs, srvCtx)
		sndCtxs = append(sndCtxs, sndCtx)
		ctxs = append(ctxs, srvCtx, sndCtx)
		go func() {
			errs <- mon.RunArchetype(srvCtx)
		}()
		go func() {
			errs <- mon.RunArchetype(sndCtx)
		}()
	}

	inCh := make(chan tla.TLAValue, numRequests)
	var clientCtxs []*distsys.MPCalContext
	for i := 2*numServers + 1; i <= 2*numServers+numClients; i++ {
		clientCtx := makeClientCtx(tla.MakeTLANumber(int32(i)), constants, inCh)
		clientCtxs = append(clientCtxs, clientCtx)
		ctxs = append(ctxs, clientCtx)
		go func() {
			errs <- clientCtx.Run()
		}()
	}

	cleanup := func() {
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
				t.Errorf("archetype error: %s", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}

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
	for i := 0; i < numRequests; i++ {
		inCh <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("key"), Value: tla.MakeTLAString("key")},
			{Key: tla.MakeTLAString("value"), Value: tla.MakeTLANumber(int32(i))},
		})
	}

	time.Sleep(waitTime)

	cleanup()

	getResValue := func(ctx *distsys.MPCalContext, resName string) (tla.TLAValue, error) {
		name := fmt.Sprintf("AServer.%s", resName)
		varHandle := ctx.IFace().RequireArchetypeResource(name)
		return ctx.IFace().Read(varHandle, nil)
	}

	getRefResValue := func(ctx *distsys.MPCalContext, resName string) (tla.TLAValue, error) {
		name := fmt.Sprintf("AServer.%s", resName)
		res, err := ctx.IFace().RequireArchetypeResourceRef(name)
		if err != nil {
			return tla.TLAValue{}, err
		}
		return ctx.IFace().Read(res, []tla.TLAValue{ctx.IFace().Self()})
	}

	printValues := func() {
		for _, ctx := range srvCtxs {
			state, _ := getRefResValue(ctx, "state")
			currentTerm, _ := getRefResValue(ctx, "currentTerm")
			//votesResponded, _ := getResValue(ctx, "votesResponded")
			//votesGranted, _ := getResValue(ctx, "votesGranted")
			commitIndex, _ := getRefResValue(ctx, "commitIndex")
			raftLog, _ := getRefResValue(ctx, "log")
			nextIndex, _ := getRefResValue(ctx, "nextIndex")
			matchIndex, _ := getResValue(ctx, "matchIndex")
			//log.Println(state, currentTerm, votesResponded, votesGranted, commitIndex, raftLog)
			log.Println(state, currentTerm, commitIndex, raftLog)
			log.Println(nextIndex, matchIndex)
		}
	}

	testLeaderElection := func() {
		isLeader := func(ctx *distsys.MPCalContext, state tla.TLAValue) bool {
			if state.Equal(raft.Leader(ctx.IFace())) {
				return true
			}
			return false
		}

		//hasLeader := false
		//for _, ctx := range srvCtxs {
		//	state, _ := getRefResValue(ctx, "state")
		//	if isLeader(ctx, state) {
		//		hasLeader = true
		//	}
		//}
		//if !hasLeader {
		//	t.Fatalf("No leader found")
		//}

		for i := 0; i < len(srvCtxs); i++ {
			for j := i + 1; j < len(srvCtxs); j++ {
				statei, _ := getRefResValue(srvCtxs[i], "state")
				statej, _ := getRefResValue(srvCtxs[j], "state")
				if isLeader(srvCtxs[i], statei) && isLeader(srvCtxs[j], statej) {
					termi, _ := getRefResValue(srvCtxs[i], "currentTerm")
					termj, _ := getRefResValue(srvCtxs[j], "currentTerm")
					if termi.Equal(termj) {
						t.Fatalf("Two leaders in the same term")
					}
				}
			}
		}
	}

	testStateMachineSafety := func() {
		prefixTuple := func(tuple tla.TLAValue, end int32) tla.TLAValue {
			return tla.MakeTLATupleFromList(tuple.AsTuple().Slice(0, int(end)))
		}

		commitIndex0, _ := getRefResValue(srvCtxs[numFailures], "commitIndex")
		raftLog0, _ := getRefResValue(srvCtxs[numFailures], "log")
		raftLog0Sliced := prefixTuple(raftLog0, commitIndex0.AsNumber())

		for i := numFailures + 1; i < len(srvCtxs); i++ {
			commitIndex, _ := getRefResValue(srvCtxs[i], "commitIndex")
			if !commitIndex.Equal(commitIndex0) {
				t.Fatalf("commit indexes are not equal: %v, %v", commitIndex, commitIndex0)
			}
			raftLog, _ := getRefResValue(srvCtxs[i], "log")
			raftLogSliced := prefixTuple(raftLog, commitIndex.AsNumber())
			if !raftLogSliced.Equal(raftLog0Sliced) {
				t.Fatalf("logs are not equal: %v, %v", raftLogSliced, raftLog0Sliced)
			}
		}
	}

	printValues()
	testLeaderElection()
	testStateMachineSafety()
}

func TestLeaderElection_ThreeServers(t *testing.T) {
	runTest(t, 3, 0, 0)
}

func TestLeaderElection_ThreeServersOneFailing(t *testing.T) {
	runTest(t, 3, 0, 1)
}

func TestLeaderElection_FiveServers(t *testing.T) {
	runTest(t, 5, 0, 0)
}

func TestLeaderElection_FiveServersOneFailing(t *testing.T) {
	runTest(t, 5, 0, 1)
}

func TestLeaderElection_FiveServersTwoFailing(t *testing.T) {
	runTest(t, 5, 0, 2)
}

func TestRaft_ThreeServers(t *testing.T) {
	runTest(t, 3, 2, 0)
}

func TestRaft_ThreeServersOneFailing(t *testing.T) {
	runTest(t, 3, 2, 1)
}

func TestRaft_FiveServers(t *testing.T) {
	runTest(t, 5, 2, 0)
}

func TestRaft_FiveServersOneFailing(t *testing.T) {
	runTest(t, 5, 2, 1)
}
