package bootstrap

import (
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/systems/raftkvs"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

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

	fdMap := hashmap.New[distsys.ArchetypeResource]()
	for i := 1; i <= c.NumServers; i++ {
		tlaIndex := tla.MakeTLANumber(int32(i))
		singleFD := newSingleFD(c, tlaIndex)
		fdMap.Set(tlaIndex, singleFD)
	}

	fdProvider := func(index tla.TLAValue) distsys.ArchetypeResource {
		res, ok := fdMap.Get(index)
		if !ok {
			panic("failure detector not found")
		}
		return res
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

		var currentTerm distsys.ArchetypeResource
		if c.Persist {
			currentTerm = resources.NewPersistent(fmt.Sprintf("Server%v.currentTerm", srvId.AsNumber()), db,
				currentTermMaker(),
			)
		} else {
			currentTerm = currentTermMaker()
		}

		log := logMaker()

		var plog distsys.ArchetypeResource
		if c.Persist {
			plog = raftkvs.NewPersistentLog(fmt.Sprintf("Server%v.plog", srvId.AsNumber()), db)
		} else {
			plog = resources.NewDummy()
		}

		commitIndex := commitIndexMaker()
		nextIndex := nextIndexMaker()
		matchIndex := matchIndexMaker()

		var votedFor distsys.ArchetypeResource
		if c.Persist {
			votedFor = resources.NewPersistent(fmt.Sprintf("Server%v.votedFor", srvId.AsNumber()), db,
				votedForMaker(),
			)
		} else {
			votedFor = votedForMaker()
		}

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
	becomeLeaderCh := make(chan tla.TLAValue, 100)
	if c.NumServers == 1 {
		becomeLeaderCh <- tla.TLA_TRUE
	}

	srvIdInt := srvId.AsNumber()
	numServersInt := iface.GetConstant("NumServers")().AsNumber()

	serverSelf := srvId
	serverCtx := distsys.NewMPCalContext(
		serverSelf, raftkvs.AServer,
		append(
			genResources(serverSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", toMap(resources.NewOutputChan(becomeLeaderCh))),
		)...,
	)

	serverRequestVoteSelf := tla.MakeTLANumber(srvIdInt + 1*numServersInt)
	serverRequestVoteCtx := distsys.NewMPCalContext(
		serverRequestVoteSelf, raftkvs.AServerRequestVote,
		append(
			genResources(serverRequestVoteSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
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
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
		)...,
	)

	serverAdvanceCommitIndexSelf := tla.MakeTLANumber(srvIdInt + 3*numServersInt)
	serverAdvanceCommitIndexCtx := distsys.NewMPCalContext(
		serverAdvanceCommitIndexSelf, raftkvs.AServerAdvanceCommitIndex,
		append(
			genResources(serverAdvanceCommitIndexSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
		)...,
	)

	serverBecomeLeaderSelf := tla.MakeTLANumber(srvIdInt + 4*numServersInt)
	serverBecomeLeaderCtx := distsys.NewMPCalContext(
		serverBecomeLeaderSelf, raftkvs.AServerBecomeLeader,
		append(
			genResources(serverBecomeLeaderSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh",
				toMap(resources.NewInputChan(becomeLeaderCh, resources.WithInputChanReadTimeout(c.InputChanReadTimeout))),
			),
		)...,
	)

	return []*distsys.MPCalContext{
		serverCtx, serverRequestVoteCtx, serverAppendEntriesCtx, serverAdvanceCommitIndexCtx,
		serverBecomeLeaderCtx,
	}
}

type Server struct {
	Id     int
	Config configs.Root

	ctxs []*distsys.MPCalContext
	mon  *resources.Monitor
}

func NewServer(srvId int, c configs.Root, db *badger.DB) *Server {
	srvIdTLA := tla.MakeTLANumber(int32(srvId))
	mon := setupMonitor(srvIdTLA, c)
	ctxs := newServerCtxs(srvIdTLA, c, db)

	return &Server{
		Id:     srvId,
		Config: c,
		ctxs:   ctxs,
		mon:    mon,
	}
}

func (s *Server) Run() error {
	errCh := make(chan error)
	for i := range s.ctxs {
		ctx := s.ctxs[i]
		go func() {
			err := s.mon.RunArchetype(ctx)
			log.Printf("archetype %v finished, err = %v", ctx.IFace().Self(), err)
			errCh <- err
		}()
	}

	for range s.ctxs {
		err := <-errCh
		if err != nil {
			return err
		}
	}
	return nil
}

func (s *Server) Close() error {
	for _, ctx := range s.ctxs {
		ctx.Stop()
	}
	err := s.mon.Close()
	return err
}
