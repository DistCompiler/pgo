package main

import (
	"flag"
	"fmt"
	"github.com/dgraph-io/badger/v3"
	"log"
	"strings"
	"time"

	"example.org/raftkvs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func main() {
	var peers string
	var monitorPeers string
	var serverBind string

	flag.StringVar(&peers, "peers", "", "comma-separated list of peer nodes to dial. must be in consistent order between invocations. must include self.")
	flag.StringVar(&monitorPeers, "monitorPeers", "", "comma-separated list of peer monitors to dial. must be in consistent order between invocations. must include self.")
	flag.StringVar(&serverBind, "serverBind", "", "host:port combination to bind server to")

	flag.Parse()

	if peers == "" || monitorPeers == "" || serverBind == "" {
		panic(fmt.Errorf("peers, monitorPeers, and serverBind are missing and non-optional"))
	}

	peerList := strings.Split(peers, ",")
	monitorPeerList := strings.Split(monitorPeers, ",")

	var selfIdx = -1
	for idx, peer := range peerList {
		if peer == serverBind {
			selfIdx = idx
		}
	}
	if selfIdx == -1 {
		panic(fmt.Errorf("could not find own address %s in peer list %v", serverBind, peerList))
	}
	srvSelf := tla.MakeTLANumber(int32(selfIdx) + 1)
	sndSelf := tla.MakeTLANumber(int32(selfIdx + 1 + len(peerList)))

	if len(peerList) != len(monitorPeerList) {
		panic(fmt.Errorf("monitor list and peer list are not the same length"))
	}

	monitorOf := make(map[string]string)
	for idx := range peerList {
		monitorOf[peerList[idx]] = monitorPeerList[idx]
	}

	var logConcat = tla.MakeTLAString("log_concat")
	var logPop = tla.MakeTLAString("log_pop")
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(len(peerList)))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("KeySet", tla.MakeTLASet()),
		distsys.DefineConstantValue("Debug", tla.TLA_FALSE),
		distsys.DefineConstantValue("LogConcat", logConcat),
		distsys.DefineConstantValue("LogPop", logPop),
	}

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

	pCurrentTermMaker := resources.PersistentResourceMaker(fmt.Sprintf("Server.%v.currentTerm", srvSelf), db, currentTermMaker)
	pVotedForMaker := resources.PersistentResourceMaker(fmt.Sprintf("Server%v.votedFor", srvSelf), db, votedForMaker)
	plogMaker := raftkvs.PersistentLogMaker(fmt.Sprintf("Server%v.plog", srvSelf), db)

	fdMaker := resources.FailureDetectorMaker(
		func(index tla.TLAValue) string {
			peerHost := peerList[int(index.AsNumber())-1]
			return monitorOf[peerHost]
		},
		resources.WithFailureDetectorPullInterval(100*time.Millisecond),
		resources.WithFailureDetectorTimeout(200*time.Millisecond),
	)
	getNetworkMaker := func(self tla.TLAValue) distsys.ArchetypeResourceMaker {
		return resources.RelaxedMailboxesMaker(
			func(idx tla.TLAValue) (resources.MailboxKind, string) {
				kind := resources.MailboxesRemote
				if idx.Equal(self) {
					kind = resources.MailboxesLocal
				}

				if idx.IsNumber() {
					// one of the two server archetypes; tell which one by which number range it fits in
					i := int(idx.AsNumber())
					if i > len(peerList) {
						i -= len(peerList)
						return kind, monitorPeerList[i-1]
					} else {
						return kind, peerList[i-1]
					}
				} else if idx.IsString() {
					// it's probably a client's hostname used as self
					return kind, idx.AsString()
				} else {
					panic(fmt.Errorf("could not convert idx %v to hostname", idx))
				}
			},
		)
	}

	mapMaker := func(self tla.TLAValue, maker distsys.ArchetypeResourceMaker) distsys.ArchetypeResourceMaker {
		return resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if index.Equal(self) {
				return maker
			}
			panic("wrong index")
		})
	}

	srvCh := make(chan tla.TLAValue, 10000)

	srvCtx := distsys.NewMPCalContext(srvSelf, raftkvs.AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(srvSelf)),
		distsys.EnsureArchetypeRefParam("fd", fdMaker),
		distsys.EnsureArchetypeDerivedRefParam("netLen", "net", resources.MailboxesLengthMaker),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.PlaceHolderResourceMaker()),
		distsys.EnsureArchetypeRefParam("state", mapMaker(srvSelf, stateMaker)),
		distsys.EnsureArchetypeRefParam("nextIndex", mapMaker(srvSelf, nextIndexMaker)),
		distsys.EnsureArchetypeRefParam("log", mapMaker(srvSelf, logMaker)),
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(srvSelf, pCurrentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(srvSelf, commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("timer", raftkvs.TimerResourceMaker()),
		distsys.EnsureArchetypeRefParam("in", resources.OutputChannelMaker(srvCh)),
		distsys.EnsureArchetypeRefParam("votedFor", pVotedForMaker),
		distsys.EnsureArchetypeRefParam("plog", mapMaker(srvSelf, plogMaker)),
	)

	sndCtx := distsys.NewMPCalContext(sndSelf, raftkvs.AServerSender,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(sndSelf)),
		distsys.EnsureArchetypeRefParam("fd", fdMaker),
		distsys.EnsureArchetypeRefParam("netEnabled",
			resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
				return distsys.LocalArchetypeResourceMaker(tla.TLA_TRUE)
			})),
		distsys.EnsureArchetypeValueParam("sid", srvSelf),
		distsys.EnsureArchetypeRefParam("state", mapMaker(srvSelf, stateMaker)),
		distsys.EnsureArchetypeRefParam("nextIndex", mapMaker(srvSelf, nextIndexMaker)),
		distsys.EnsureArchetypeRefParam("log", mapMaker(srvSelf, logMaker)),
		distsys.EnsureArchetypeRefParam("currentTerm", mapMaker(srvSelf, currentTermMaker)),
		distsys.EnsureArchetypeRefParam("commitIndex", mapMaker(srvSelf, commitIndexMaker)),
		distsys.EnsureArchetypeRefParam("in", raftkvs.CustomInChanMaker(srvCh)),
	)

	monitor := resources.NewMonitor(monitorOf[peerList[selfIdx]])

	go func() {
		err := monitor.ListenAndServe()
		if err != nil {
			panic(err)
		}
	}()
	defer func() {
		err := monitor.Close()
		if err != nil {
			panic(err)
		}
	}()

	go func() {
		err := monitor.RunArchetype(srvCtx)
		if err != nil {
			panic(err)
		}
	}()
	defer srvCtx.Stop()

	go func() {
		err := monitor.RunArchetype(sndCtx)
		if err != nil {
			panic(err)
		}
	}()
	defer sndCtx.Stop()

	select {}
}
