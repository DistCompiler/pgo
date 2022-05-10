package main

import (
	"fmt"
	"log"

	"example.org/raftkvs"
	"example.org/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"github.com/dgraph-io/badger/v3"
)

func makeConstants(c configs.Root) []distsys.MPCalContextConfigFn {
	constants := append([]distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(c.NumServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(c.NumClients))),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
		distsys.DefineConstantValue("Debug", tla.MakeTLABool(c.Debug)),
	}, raftkvs.PersistentLogConstantDefs, raftkvs.LeaderTimeoutConstantDefs)
	return constants
}

func newNetwork(self tla.TLAValue, c configs.Root) *resources.Mailboxes {
	return resources.NewRelaxedMailboxes(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			addr := c.Archetypes[int(aid)].MailboxAddr
			return kind, addr
		},
		resources.WithMailboxesDialTimeout(c.Mailboxes.DialTimeout),
		resources.WithMailboxesReadTimeout(c.Mailboxes.ReadTimeout),
		resources.WithMailboxesWriteTimeout(c.Mailboxes.WriteTimeout),
	)
}

func setupMonitor(self tla.TLAValue, c configs.Root) *resources.Monitor {
	selfInt := int(self.AsNumber())
	archetypeConfig, ok := c.Archetypes[selfInt]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}
	mon := resources.NewMonitor(archetypeConfig.MonitorAddr)
	go func() {
		if err := mon.ListenAndServe(); err != nil {
			log.Fatal(err)
		}
	}()
	return mon
}

func newSingleFD(c configs.Root, index tla.TLAValue) *resources.SingleFailureDetector {
	aid := int(index.AsNumber())
	archetypeConfig, ok := c.Archetypes[aid]
	if !ok || archetypeConfig.MonitorAddr == "" {
		log.Fatal("monitor not found")
	}
	singleFd := resources.NewSingleFailureDetector(
		index,
		archetypeConfig.MonitorAddr,
		resources.WithFailureDetectorPullInterval(c.FD.PullInterval),
		resources.WithFailureDetectorTimeout(c.FD.Timeout),
	)
	return singleFd
}

func newServerCtxs(srvId tla.TLAValue, c configs.Root, db *badger.DB) []*distsys.MPCalContext {
	constants := makeConstants(c)
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
		if singleFD, ok := fdMap.Get(index); ok {
			return singleFD.(*resources.SingleFailureDetector)
		}
		singleFD := newSingleFD(c, index)
		fdMap = fdMap.Set(index, singleFD)
		return singleFD
	}

	stateMaker := resources.NewLocalSharedMaker(raftkvs.Follower(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	currentTermMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(1),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	logMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	commitIndexMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(0),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	nextIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(1)
		}),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout),
	)
	matchIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(0)
		}),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout),
	)
	votedForMaker := resources.NewLocalSharedMaker(raftkvs.Nil(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	votesRespondedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	votesGrantedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	leaderMaker := resources.NewLocalSharedMaker(raftkvs.Nil(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	smMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raftkvs.KeySet(iface)}, func(t []tla.TLAValue) tla.TLAValue {
			return raftkvs.Nil(iface)
		}),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout),
	)
	smDomainMaker := resources.NewLocalSharedMaker(raftkvs.KeySet(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	leaderTimeout := raftkvs.NewTimerResource(c.LeaderElection.Timeout, c.LeaderElection.TimeoutOffset)

	genResources := func(self tla.TLAValue) []distsys.MPCalContextConfigFn {
		net := newNetwork(self, c)
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
				raftkvs.NewCustomInChan(appendEntriesCh, c.AppendEntriesSendInterval)),
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
