package bootstrap

import (
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/hashmap"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/raftkvs"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"

	"github.com/dgraph-io/badger/v3"
)

func newServerCtxs(srvId tla.Value, c configs.Root, db *badger.DB) ([]*distsys.MPCalContext, *hashmap.HashMap[distsys.ArchetypeResource]) {
	constants := makeConstants(c)
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	toMap := func(res distsys.ArchetypeResource) distsys.ArchetypeResource {
		return resources.NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
			if index.Equal(srvId) {
				return res
			}
			panic("wrong index")
		})
	}

	fdMap := hashmap.New[distsys.ArchetypeResource]()
	for i := 1; i <= c.NumServers; i++ {
		tlaIndex := tla.MakeNumber(int32(i))
		singleFD := newSingleFD(c, tlaIndex)
		fdMap.Set(tlaIndex, singleFD)
	}

	fdProvider := func(index tla.Value) distsys.ArchetypeResource {
		res, ok := fdMap.Get(index)
		if !ok {
			panic("failure detector not found")
		}
		return res
	}

	stateMaker := resources.NewLocalSharedManager(raftkvs.Follower(iface),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	currentTermMaker := resources.NewLocalSharedManager(tla.MakeNumber(1),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	logMaker := resources.NewLocalSharedManager(tla.MakeTuple(),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))

	commitIndexMaker := resources.NewLocalSharedManager(tla.MakeNumber(0),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	nextIndexMaker := resources.NewLocalSharedManager(
		tla.MakeFunction([]tla.Value{raftkvs.ServerSet(iface)}, func(values []tla.Value) tla.Value {
			return tla.MakeNumber(1)
		}),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout),
	)
	matchIndexMaker := resources.NewLocalSharedManager(
		tla.MakeFunction([]tla.Value{raftkvs.ServerSet(iface)}, func(values []tla.Value) tla.Value {
			return tla.MakeNumber(0)
		}),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout),
	)
	votedForMaker := resources.NewLocalSharedManager(raftkvs.Nil(iface),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	votesRespondedMaker := resources.NewLocalSharedManager(tla.MakeSet(),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	votesGrantedMaker := resources.NewLocalSharedManager(tla.MakeSet(),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))

	leaderMaker := resources.NewLocalSharedManager(raftkvs.Nil(iface),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))
	smMaker := resources.NewLocalSharedManager(
		tla.MakeFunction([]tla.Value{raftkvs.KeySet(iface)}, func(t []tla.Value) tla.Value {
			return raftkvs.Nil(iface)
		}),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout),
	)
	smDomainMaker := resources.NewLocalSharedManager(raftkvs.KeySet(iface),
		resources.WithLocalSharedResourceTimeout(c.SharedResourceTimeout))

	leaderTimeout := raftkvs.NewTimerResource(c.LeaderElection.Timeout, c.LeaderElection.TimeoutOffset)

	genResources := func(self tla.Value) []distsys.MPCalContextConfigFn {
		net := newNetwork(self, c)
		// netLen := resources.NewMailboxesLength(net)
		netLen := distsys.NewLocalArchetypeResource(tla.MakeNumber(0))
		netEnabled := resources.NewPlaceHolder()
		fd := resources.NewIncMap(fdProvider)

		state := stateMaker.MakeLocalShared()

		var currentTerm distsys.ArchetypeResource
		if c.Persist {
			currentTerm = resources.MakePersistent(fmt.Sprintf("Server%v.currentTerm", srvId.AsNumber()), db,
				currentTermMaker.MakeLocalShared(),
			)
		} else {
			currentTerm = currentTermMaker.MakeLocalShared()
		}

		log := logMaker.MakeLocalShared()

		var plog distsys.ArchetypeResource
		if c.Persist {
			plog = raftkvs.NewPersistentLog(fmt.Sprintf("Server%v.plog", srvId.AsNumber()), db)
		} else {
			plog = resources.NewDummy()
		}

		commitIndex := commitIndexMaker.MakeLocalShared()
		nextIndex := nextIndexMaker.MakeLocalShared()
		matchIndex := matchIndexMaker.MakeLocalShared()

		var votedFor distsys.ArchetypeResource
		if c.Persist {
			votedFor = resources.MakePersistent(fmt.Sprintf("Server%v.votedFor", srvId.AsNumber()), db,
				votedForMaker.MakeLocalShared(),
			)
		} else {
			votedFor = votedForMaker.MakeLocalShared()
		}

		votesResponded := votesRespondedMaker.MakeLocalShared()
		votesGranted := votesGrantedMaker.MakeLocalShared()

		leader := leaderMaker.MakeLocalShared()
		sm := smMaker.MakeLocalShared()
		smDomain := smDomainMaker.MakeLocalShared()

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

	appendEntriesCh := make(chan tla.Value, 100)
	becomeLeaderCh := make(chan tla.Value, 100)
	if c.NumServers == 1 {
		becomeLeaderCh <- tla.ModuleTRUE
	}

	srvIdInt := srvId.AsNumber()
	numServersInt := iface.GetConstant("NumServers")().AsNumber()

	serverSelf := srvId
	serverCtx := distsys.NewMPCalContext(
		serverSelf, raftkvs.AServer,
		append(
			genResources(serverSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", toMap(resources.NewDummy())),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", toMap(resources.NewOutputChan(becomeLeaderCh))),
		)...,
	)

	serverRequestVoteSelf := tla.MakeNumber(srvIdInt + 1*numServersInt)
	serverRequestVoteCtx := distsys.NewMPCalContext(
		serverRequestVoteSelf, raftkvs.AServerRequestVote,
		append(
			genResources(serverRequestVoteSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
		)...,
	)

	serverAppendEntriesSelf := tla.MakeNumber(srvIdInt + 2*numServersInt)
	serverAppendEntriesCtx := distsys.NewMPCalContext(
		serverAppendEntriesSelf, raftkvs.AServerAppendEntries,
		append(
			genResources(serverAppendEntriesSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh",
				toMap(raftkvs.NewCustomInChan(appendEntriesCh, c.AppendEntriesSendInterval))),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
		)...,
	)

	serverAdvanceCommitIndexSelf := tla.MakeNumber(srvIdInt + 3*numServersInt)
	serverAdvanceCommitIndexCtx := distsys.NewMPCalContext(
		serverAdvanceCommitIndexSelf, raftkvs.AServerAdvanceCommitIndex,
		append(
			genResources(serverAdvanceCommitIndexSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
		)...,
	)

	serverBecomeLeaderSelf := tla.MakeNumber(srvIdInt + 4*numServersInt)
	serverBecomeLeaderCtx := distsys.NewMPCalContext(
		serverBecomeLeaderSelf, raftkvs.AServerBecomeLeader,
		append(
			genResources(serverBecomeLeaderSelf),
			distsys.EnsureMPCalContextConfigs(constants...),
			distsys.EnsureArchetypeRefParam("appendEntriesCh", toMap(resources.NewOutputChan(appendEntriesCh))),
			distsys.EnsureArchetypeRefParam("becomeLeaderCh",
				toMap(resources.NewInputChan(becomeLeaderCh, resources.WithInputChanReadTimeout(c.InputChanReadTimeout))),
			),
		)...,
	)

	return []*distsys.MPCalContext{
		serverCtx, serverRequestVoteCtx, serverAppendEntriesCtx, serverAdvanceCommitIndexCtx,
		serverBecomeLeaderCtx,
	}, fdMap
}

type Server struct {
	Id     int
	Config configs.Root

	ctxs  []*distsys.MPCalContext
	mon   *resources.Monitor
	fdMap *hashmap.HashMap[distsys.ArchetypeResource]
}

func NewServer(srvId int, c configs.Root, db *badger.DB) *Server {
	srvIdTLA := tla.MakeNumber(int32(srvId))
	mon := setupMonitor(srvIdTLA, c)
	ctxs, fdMap := newServerCtxs(srvIdTLA, c, db)

	return &Server{
		Id:     srvId,
		Config: c,
		ctxs:   ctxs,
		mon:    mon,
		fdMap:  fdMap,
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
	log.Printf("server %v closed", s.Id)
	return err
}
