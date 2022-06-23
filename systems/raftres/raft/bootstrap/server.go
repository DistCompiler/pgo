package bootstrap

import (
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/systems/raftres/configs"
	"github.com/DistCompiler/pgo/systems/raftres/raft"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

func serverNetListenerId(c configs.Root, srvId int) int {
	return c.NumServers*0 + srvId
}

func serverPropChListenerId(c configs.Root, srvId int) int {
	return c.NumServers*1 + srvId
}

func serverRequestVoteId(c configs.Root, srvId int) int {
	return c.NumServers*2 + srvId
}

func serverAppendEntriesId(c configs.Root, srvId int) int {
	return c.NumServers*3 + srvId
}

func serverAdvanceCommitIndexId(c configs.Root, srvId int) int {
	return c.NumServers*4 + srvId
}

func serverBecomeLeaderId(c configs.Root, srvId int) int {
	return c.NumServers*5 + srvId
}

func serverFollowerAdvanceCommitIndexId(c configs.Root, srvId int) int {
	return c.NumServers*6 + srvId
}

func newServerCtxs(srvId tla.TLAValue, c configs.Root, db *badger.DB, propChan, acctChan chan tla.TLAValue) []*distsys.MPCalContext {
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

	stateMaker := resources.NewLocalSharedMaker(raft.Follower(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	currentTermMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(1),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	logMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	commitIndexMaker := resources.NewLocalSharedMaker(tla.MakeTLANumber(0),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	nextIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raft.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(1)
		}),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout),
	)
	matchIndexMaker := resources.NewLocalSharedMaker(
		tla.MakeTLAFunction([]tla.TLAValue{raft.ServerSet(iface)}, func(values []tla.TLAValue) tla.TLAValue {
			return tla.MakeTLANumber(0)
		}),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout),
	)
	votedForMaker := resources.NewLocalSharedMaker(raft.Nil(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	votesRespondedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))
	votesGrantedMaker := resources.NewLocalSharedMaker(tla.MakeTLATuple(),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	leaderMaker := resources.NewLocalSharedMaker(raft.Nil(iface),
		resources.WithLocalSharedTimeout(c.SharedResourceTimeout))

	leaderTimeout := raft.NewTimerResource(c.LeaderElection.Timeout, c.LeaderElection.TimeoutOffset)

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
		plog := raft.NewPersistentLog(fmt.Sprintf("Server%v.plog", srvId.AsNumber()), db)
		commitIndex := commitIndexMaker()
		nextIndex := nextIndexMaker()
		matchIndex := matchIndexMaker()
		votedFor := resources.NewPersistent(fmt.Sprintf("Server%v.votedFor", srvId.AsNumber()), db,
			votedForMaker(),
		)
		votesResponded := votesRespondedMaker()
		votesGranted := votesGrantedMaker()

		leader := leaderMaker()

		propCh := resources.NewInputChan(propChan, resources.WithInputChanReadTimeout(c.InputChanReadTimeout))
		acctCh := resources.NewOutputChan(acctChan)

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
			distsys.EnsureArchetypeRefParam("propCh", toMap(propCh)),
			distsys.EnsureArchetypeRefParam("acctCh", toMap(acctCh)),
			distsys.EnsureArchetypeRefParam("leaderTimeout", leaderTimeout),
		}
		return resourcesConfig
	}

	appendEntriesCh := make(chan tla.TLAValue, 100)
	becomeLeaderCh := make(chan tla.TLAValue, 100)
	if c.NumServers == 1 {
		becomeLeaderCh <- tla.TLA_TRUE
	}
	fAdvCommitIdxCh := make(chan tla.TLAValue, 100)

	srvIdInt := int(srvId.AsNumber())

	serverNetListenerCtx := func() *distsys.MPCalContext {
		self := serverNetListenerId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerNetListener,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", toMap(resources.NewOutputChan(becomeLeaderCh))),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", toMap(resources.NewOutputChan(fAdvCommitIdxCh))),
			)...,
		)
	}()

	serverPropChListenerCtx := func() *distsys.MPCalContext {
		self := serverPropChListenerId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerPropChListener,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", toMap(resources.NewOutputChan(becomeLeaderCh))),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", toMap(resources.NewOutputChan(fAdvCommitIdxCh))),
			)...,
		)
	}()

	serverRequestVoteCtx := func() *distsys.MPCalContext {
		self := serverRequestVoteId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerRequestVote,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", resources.NewPlaceHolder()),
			)...,
		)
	}()

	serverAppendEntriesCtx := func() *distsys.MPCalContext {
		self := serverAppendEntriesId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerAppendEntries,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh",
					raft.NewCustomInChan(appendEntriesCh, c.AppendEntriesSendInterval)),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", resources.NewPlaceHolder()),
			)...,
		)
	}()

	serverAdvanceCommitIndexCtx := func() *distsys.MPCalContext {
		self := serverAdvanceCommitIndexId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerAdvanceCommitIndex,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", resources.NewPlaceHolder()),
			)...,
		)
	}()

	serverBecomeLeaderCtx := func() *distsys.MPCalContext {
		self := serverBecomeLeaderId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerBecomeLeader,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewOutputChan(appendEntriesCh)),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh",
					toMap(resources.NewInputChan(becomeLeaderCh, resources.WithInputChanReadTimeout(c.InputChanReadTimeout))),
				),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh", resources.NewPlaceHolder()),
			)...,
		)
	}()

	serverFollowerAdvanceCommitIndexCtx := func() *distsys.MPCalContext {
		self := serverFollowerAdvanceCommitIndexId(c, srvIdInt)
		tlaSelf := tla.MakeTLANumber(int32(self))

		return distsys.NewMPCalContext(
			tlaSelf, raft.AServerFollowerAdvanceCommitIndex,
			append(
				genResources(tlaSelf),
				distsys.EnsureMPCalContextConfigs(constants...),
				distsys.EnsureArchetypeRefParam("appendEntriesCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("becomeLeaderCh", resources.NewPlaceHolder()),
				distsys.EnsureArchetypeRefParam("fAdvCommitIdxCh",
					toMap(resources.NewInputChan(fAdvCommitIdxCh, resources.WithInputChanReadTimeout(c.InputChanReadTimeout))),
				),
			)...,
		)
	}()

	return []*distsys.MPCalContext{
		serverNetListenerCtx, serverPropChListenerCtx, serverRequestVoteCtx, serverAppendEntriesCtx,
		serverAdvanceCommitIndexCtx, serverBecomeLeaderCtx, serverFollowerAdvanceCommitIndexCtx,
	}
}

type Server struct {
	Id     int
	Config configs.Root

	ctxs []*distsys.MPCalContext
	mon  *resources.Monitor
}

func NewServer(srvId int, c configs.Root, db *badger.DB, mon *resources.Monitor,
	propCh, acctCh chan tla.TLAValue) *Server {

	srvIdTLA := tla.MakeTLANumber(int32(srvId))
	ctxs := newServerCtxs(srvIdTLA, c, db, propCh, acctCh)
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
	return nil
}
