-------------------------------- MODULE raft --------------------------------

\* Raft consensus protocol specification based on the TLA+ spec from
\* https://github.com/ongardie/raft.tla.
\*
\* We used limited buffer sized network channels to improve model checking 
\* perofmance. Also leader election part of Raft is not live by design.
\* These two can cause deadlock, so don't check deadlocks in model checking.
\*
\* Properties are defined based on the presented properties in the original 
\* Raft paper. See figure 3 in https://raft.github.io/raft.pdf.

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT ExploreFail

CONSTANT NumServers
CONSTANT NumClients

CONSTANT BufferSize

CONSTANT MaxTerm
CONSTANT MaxCommitIndex

CONSTANT MaxNodeFail

(********************

--mpcal raft {
    define {
        Follower  == "follower"
        Candidate == "candidate"
        Leader    == "leader"

        RequestVoteRequest    == "rvq"
        RequestVoteResponse   == "rvp"
        AppendEntriesRequest  == "apq"
        AppendEntriesResponse == "app"
        ClientPutRequest      == "cpq"

        Key1   == "key1"
        Value1 == "value1"

        Min(s) == CHOOSE x \in s : \A y \in s : x <= y
        Max(s) == CHOOSE x \in s : \A y \in s : x >= y

        LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

        Nil == 0

        ServerSet == 1..NumServers
        ClientSet == (NumServers+1)..(NumServers+NumClients)

        isQuorum(s) == Cardinality(s) * 2 > NumServers
    }

    macro mayFail(selfId, netEnabled) {
        if (ExploreFail) {
            either { skip; } or {
                netEnabled[selfId] := FALSE;
                goto failLabel;
            };
        };
    }

    macro Send(net, dest, fd, m) {
        either {
            net[dest] := m;
        } or {
            await fd[dest];
        };
    }

    macro UpdateTerm(i, m, currentTerm, state, votedFor) {
        if (m.mterm > currentTerm) {
            currentTerm := m.mterm;
            state       := Follower;
            votedFor    := Nil;
        };
    }

    mapping macro ReliableFIFOLink {
        read {
            assert $variable.enabled;
            await Len($variable.queue) > 0;
            with (readMsg = Head($variable.queue)) {
                $variable := [queue |-> Tail($variable.queue), enabled |-> $variable.enabled];
                yield readMsg;
            };
        }

        write {
            await $variable.enabled;
            await Len($variable.queue) < BufferSize;
            yield [queue |-> Append($variable.queue, $value), enabled |-> $variable.enabled];
        }
    }

    mapping macro NetworkToggle {
        read { yield $variable.enabled; }

        write {
            yield [queue |-> $variable.queue, enabled |-> $value];
        }
    }

    mapping macro PerfectFD {
        read {
            yield $variable;
        }

        write { yield $value; }
    }

    mapping macro NetworkBufferLength {
        read {
            yield Len($variable.queue);
        }

        write {
            assert FALSE;
            yield $value;
        }
    }

    archetype AServer(ref net[_], ref fd[_], ref netLen[_], ref netEnabled[_])
    variables
        currentTerm = 1,
        state       = Follower,
        votedFor    = Nil,
    
        log = << >>,

        commitIndex = 0,

        nextIndex  = [i \in ServerSet |-> 1],
        matchIndex = [i \in ServerSet |-> 0],

        votesResponded = {},
        votesGranted   = {},

        \* added by Shayan
        leader = Nil, 
        idx    = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            \* if (commitIndex > 0) {
            \*     print <<state, self, log, commitIndex, currentTerm>>;
            \* };

            either {
                m := net[self];
                assert m.mdest = self;
                mayFail(self, netEnabled);

            handleMsg:
                if (m.mtype = RequestVoteRequest) {   
                    UpdateTerm(self, m, currentTerm, state, votedFor);

                    \* HandleRequestVoteRequest
                    with (
                        i = self, j = m.msource,
                        logOK = \/ m.mlastLogTerm > LastTerm(log)
                                \/ /\ m.mlastLogTerm = LastTerm(log)
                                   /\ m.mlastLogIndex >= Len(log),
                        grant = /\ m.mterm = currentTerm
                                /\ logOK
                                /\ votedFor \in {Nil, j} 
                    ) {
                        assert m.mterm <= currentTerm;
                        if (grant) {
                            votedFor := j; 
                        };
                        Send(net, j, fd, [
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm,
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j
                        ]);
                    };
                } else if (m.mtype = RequestVoteResponse) {
                    UpdateTerm(self, m, currentTerm, state, votedFor);

                    \* DropStaleResponse
                    if (m.mterm < currentTerm) {
                        goto serverLoop;
                    } else {
                        \* HandleRequestVoteResponse
                        with (i = self, j = m.msource) {
                            assert m.mterm = currentTerm;
                            votesResponded := votesResponded \cup {j};
                            if (m.mvoteGranted) {
                                votesGranted := votesGranted \cup {j};
                            }; 
                        }; 
                    };
                } else if (m.mtype = AppendEntriesRequest) {
                    UpdateTerm(self, m, currentTerm, state, votedFor);

                    leader := m.msource;

                    \* HandleAppendEntriesRequest
                    with (
                        i = self, j = m.msource,
                        logOK = \/ m.mprevLogIndex = 0
                                \/ /\ m.mprevLogIndex > 0
                                   /\ m.mprevLogIndex <= Len(log)
                                   /\ m.mprevLogTerm = log[m.mprevLogIndex].term
                    ) {
                        assert m.mterm <= currentTerm;

                        \* return to follower state
                        if (
                            /\ m.mterm = currentTerm
                            /\ state = Candidate
                        ) {
                            state := Follower;
                        };

                        \* reject request
                        if (
                            \/ m.mterm < currentTerm
                            \/ /\ m.mterm = currentTerm
                               /\ state = Follower
                               /\ \lnot logOK
                        ) {
                            Send(net, j, fd, [
                                mtype       |-> AppendEntriesResponse,
                                mterm       |-> currentTerm,
                                msuccess    |-> FALSE,
                                mmatchIndex |-> 0,
                                msource     |-> i,
                                mdest       |-> j
                            ]);
                        } 
                        \* accept request
                        else {
                            assert (
                                /\ m.mterm = currentTerm
                                /\ state = Follower
                                /\ logOK
                            );
                            with (index = m.mprevLogIndex + 1) {
                                \* conflict: remove 1 entry
                                if (
                                    /\ m.mentries /= << >>
                                    /\ Len(log) >= index
                                    /\ log[index].term /= m.mentries[1].term
                                ) {
                                    log := [k \in 1..(Len(log)-1) |-> log[k]];
                                };
                                
                                \* no conflict: append entry
                                if (
                                    /\ m.mentries /= << >>
                                    /\ Len(log) = m.mprevLogIndex
                                ) {
                                    log := Append(log, m.mentries[1]);
                                };

                                \* already done with request
                                if (
                                    \/ m.mentries = << >>
                                    \/ /\ m.mentries /= << >>
                                       /\ Len(log) >= index
                                       /\ log[index].term = m.mentries[1].term
                                ) {
                                    \* This could make our commitIndex decrease (for
                                    \* example if we process an old, duplicated request),
                                    \* but that doesn't really affect anything.
                                    commitIndex := m.mcommitIndex;
                                    Send(net, j, fd, [
                                        mtype       |-> AppendEntriesResponse,
                                        mterm       |-> currentTerm,
                                        msuccess    |-> TRUE,
                                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                        msource     |-> i,
                                        mdest       |-> j
                                    ]);
                                }; 
                            };
                        };
                    };
                } else if (m.mtype = AppendEntriesResponse) {
                    UpdateTerm(self, m, currentTerm, state, votedFor);

                    \* DropStaleResponse
                    if (m.mterm < currentTerm) {
                        goto serverLoop;
                    } else {
                        \* HandleAppendEntriesResponse
                        with (i = self, j = m.msource) {
                            assert m.mterm = currentTerm;
                            if (m.msuccess) {
                                nextIndex[j]  := m.mmatchIndex + 1;
                                matchIndex[j] := m.mmatchIndex;
                            } else {
                                nextIndex[j]  := Max({nextIndex[j]-1, 1});
                            };
                        };
                    };
                } else if (m.mtype = ClientPutRequest) {
                    \* ClientRequest
                    if (state = Leader) {
                        with (entry = [term  |-> currentTerm, 
                                       key   |-> m.mkey,
                                       value |-> m.mvalue]
                        ) {
                            log := Append(log, entry);
                        };
                    };
                };
            } or {
                \* Server times out and starts a new election.
                await state \in {Follower, Candidate};
                await (
                    /\ netLen[self] = 0
                    /\ \/ leader = Nil
                       \/ /\ leader /= Nil
                          /\ fd[leader]
                );
                state          := Candidate;
                currentTerm    := currentTerm + 1;
                votedFor       := self;
                votesResponded := {self};
                votesGranted   := {self};

                idx := 1;
            requestVoteLoop:
                while (idx <= NumServers) {
                    \* RequestVote
                    if (idx /= self) {
                        Send(net, idx, fd, [
                            mtype         |-> RequestVoteRequest,
                            mterm         |-> currentTerm,
                            mlastLogTerm  |-> LastTerm(log),
                            mlastLogIndex |-> Len(log),
                            msource       |-> self,
                            mdest         |-> idx
                        ]);
                    };
                    idx := idx + 1;
                    mayFail(self, netEnabled);
                };
            } or {
                await state = Leader;

                \* AdvanceCommitIndex
                with (
                    \* Agree(index) = [self] \cup {k \in ServerSet : 
                                                    \* matchIndex[k] >= index},
                    agreeIndexes = {index \in 1..Len(log) : 
                                        isQuorum({self} \cup {k \in ServerSet : 
                                                                matchIndex[k] >= index})},
                    newCommitIndex =
                        IF /\ agreeIndexes /= {}
                           /\ log[Max(agreeIndexes)].term = currentTerm
                        THEN Max(agreeIndexes)
                        ELSE commitIndex
                ) {
                    assert newCommitIndex >= commitIndex;
                    commitIndex := newCommitIndex;
                };

                \* AppendEntries
                idx := 1;
            appendEntriesLoop:
                while (idx <= NumServers) {
                    if (idx /= self) {
                        with (
                            prevLogIndex = nextIndex[idx] - 1,
                            prevLogTerm  = IF prevLogIndex > 0
                                           THEN log[prevLogIndex].term
                                           ELSE 0,
                            lastEntry    = Min({Len(log), nextIndex[idx]}),
                            entries      = SubSeq(log, nextIndex[idx], lastEntry)
                        ) {
                            Send(net, idx, fd, [
                                mtype         |-> AppendEntriesRequest,
                                mterm         |-> currentTerm,
                                mprevLogIndex |-> prevLogIndex,
                                mprevLogTerm  |-> prevLogTerm,
                                mentries      |-> entries,
                                mcommitIndex  |-> Min({commitIndex, lastEntry}),
                                msource       |-> self,
                                mdest         |-> idx
                            ]);
                        };
                    };
                    idx := idx + 1;
                    mayFail(self, netEnabled);
                };
            } or {
                \* BecomeLeader
                await (
                    /\ state = Candidate
                    /\ isQuorum(votesGranted)
                );
                state      := Leader;
                nextIndex  := [j \in ServerSet |-> Len(log) + 1]; 
                matchIndex := [j \in ServerSet |-> 0];
            };
        };

    failLabel:
        fd[self] := TRUE;
    }

    archetype AClient(ref net[_]) {
    sndPutReq:
        with (srv = 1) {
            net[srv] := [
                mtype   |-> ClientPutRequest,
                mkey    |-> Key1,
                mvalue  |-> Value1,
                msource |-> self,
                mdest   |-> srv
            ];
        };
    clientBlock:
        await FALSE; 
    }

    variables
        network = [i \in ServerSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd = [i \in ServerSet |-> FALSE];

    fair process (server \in ServerSet) == instance AServer(ref network[_], ref fd[_], ref network[_], ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle;
    
    fair process (client \in ClientSet) == instance AClient(ref network[_])
        mapping @1[_] via ReliableFIFOLink;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raft {
  variables network = [i \in ServerSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE];
  define{
    Follower == "follower"
    Candidate == "candidate"
    Leader == "leader"
    RequestVoteRequest == "rvq"
    RequestVoteResponse == "rvp"
    AppendEntriesRequest == "apq"
    AppendEntriesResponse == "app"
    ClientPutRequest == "cpq"
    Key1 == "key1"
    Value1 == "value1"
    Min(s) == CHOOSE x \in s : \A y \in s : (x) <= (y)
    Max(s) == CHOOSE x \in s : \A y \in s : (x) >= (y)
    LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
    Nil == 0
    ServerSet == (1) .. (NumServers)
    ClientSet == ((NumServers) + (1)) .. ((NumServers) + (NumClients))
    isQuorum(s) == ((Cardinality(s)) * (2)) > (NumServers)
  }
  
  fair process (server \in ServerSet)
    variables currentTerm = 1; state = Follower; votedFor = Nil; log = <<>>; commitIndex = 0; nextIndex = [i \in ServerSet |-> 1]; matchIndex = [i \in ServerSet |-> 0]; votesResponded = {}; votesGranted = {}; leader = Nil; idx = 1; m;
  {
    serverLoop:
      if(TRUE) {
        either {
          assert ((network)[self]).enabled;
          await (Len(((network)[self]).queue)) > (0);
          with (readMsg00 = Head(((network)[self]).queue)) {
            with (network0 = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]) {
              with (yielded_network1 = readMsg00) {
                m := yielded_network1;
                assert ((m).mdest) = (self);
                if(ExploreFail) {
                  either {
                    skip;
                    network := network0;
                    goto handleMsg;
                  } or {
                    with (value00 = FALSE) {
                      network := [network0 EXCEPT ![self] = [queue |-> ((network0)[self]).queue, enabled |-> value00]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network0;
                  goto handleMsg;
                };
              };
            };
          };
        } or {
          await (state) \in ({Follower, Candidate});
          with (yielded_network00 = Len(((network)[self]).queue)) {
            with (yielded_fd5 = (fd)[leader]) {
              await ((yielded_network00) = (0)) /\ (((leader) = (Nil)) \/ (((leader) # (Nil)) /\ (yielded_fd5)));
              state := Candidate;
              currentTerm := (currentTerm) + (1);
              votedFor := self;
              votesResponded := {self};
              votesGranted := {self};
              idx := 1;
              goto requestVoteLoop;
            };
          };
        } or {
          await (state) = (Leader);
          with (agreeIndexes1 = {index \in (1) .. (Len(log)) : isQuorum(({self}) \union ({k \in ServerSet : ((matchIndex)[k]) >= (index)}))}, newCommitIndex1 = IF ((agreeIndexes1) # ({})) /\ ((((log)[Max(agreeIndexes1)]).term) = (currentTerm)) THEN Max(agreeIndexes1) ELSE commitIndex) {
            assert (newCommitIndex1) >= (commitIndex);
            commitIndex := newCommitIndex1;
            idx := 1;
            goto appendEntriesLoop;
          };
        } or {
          await ((state) = (Candidate)) /\ (isQuorum(votesGranted));
          state := Leader;
          nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
          matchIndex := [j \in ServerSet |-> 0];
          goto serverLoop;
        };
      } else {
        goto failLabel;
      };
    handleMsg:
      if(((m).mtype) = (RequestVoteRequest)) {
        if(((m).mterm) > (currentTerm)) {
          currentTerm := (m).mterm;
          state := Follower;
          with (votedFor1 = Nil) {
            with (i = self, j = (m).msource, logOK = (((m).mlastLogTerm) > (LastTerm(log))) \/ ((((m).mlastLogTerm) = (LastTerm(log))) /\ (((m).mlastLogIndex) >= (Len(log)))), grant = ((((m).mterm) = (currentTerm)) /\ (logOK)) /\ ((votedFor1) \in ({Nil, j}))) {
              assert ((m).mterm) <= (currentTerm);
              if(grant) {
                votedFor := j;
                either {
                  with (value10 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]];
                    goto serverLoop;
                  };
                } or {
                  with (yielded_fd00 = (fd)[j]) {
                    await yielded_fd00;
                    goto serverLoop;
                  };
                };
              } else {
                either {
                  with (value11 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]];
                    votedFor := votedFor1;
                    goto serverLoop;
                  };
                } or {
                  with (yielded_fd01 = (fd)[j]) {
                    await yielded_fd01;
                    votedFor := votedFor1;
                    goto serverLoop;
                  };
                };
              };
            };
          };
        } else {
          with (i = self, j = (m).msource, logOK = (((m).mlastLogTerm) > (LastTerm(log))) \/ ((((m).mlastLogTerm) = (LastTerm(log))) /\ (((m).mlastLogIndex) >= (Len(log)))), grant = ((((m).mterm) = (currentTerm)) /\ (logOK)) /\ ((votedFor) \in ({Nil, j}))) {
            assert ((m).mterm) <= (currentTerm);
            if(grant) {
              votedFor := j;
              either {
                with (value12 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]];
                  goto serverLoop;
                };
              } or {
                with (yielded_fd02 = (fd)[j]) {
                  await yielded_fd02;
                  goto serverLoop;
                };
              };
            } else {
              either {
                with (value13 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]];
                  goto serverLoop;
                };
              } or {
                with (yielded_fd03 = (fd)[j]) {
                  await yielded_fd03;
                  goto serverLoop;
                };
              };
            };
          };
        };
      } else {
        if(((m).mtype) = (RequestVoteResponse)) {
          if(((m).mterm) > (currentTerm)) {
            currentTerm := (m).mterm;
            state := Follower;
            votedFor := Nil;
            if(((m).mterm) < (currentTerm)) {
              goto serverLoop;
            } else {
              with (i = self, j = (m).msource) {
                assert ((m).mterm) = (currentTerm);
                votesResponded := (votesResponded) \union ({j});
                if((m).mvoteGranted) {
                  votesGranted := (votesGranted) \union ({j});
                  goto serverLoop;
                } else {
                  goto serverLoop;
                };
              };
            };
          } else {
            if(((m).mterm) < (currentTerm)) {
              goto serverLoop;
            } else {
              with (i = self, j = (m).msource) {
                assert ((m).mterm) = (currentTerm);
                votesResponded := (votesResponded) \union ({j});
                if((m).mvoteGranted) {
                  votesGranted := (votesGranted) \union ({j});
                  goto serverLoop;
                } else {
                  goto serverLoop;
                };
              };
            };
          };
        } else {
          if(((m).mtype) = (AppendEntriesRequest)) {
            if(((m).mterm) > (currentTerm)) {
              currentTerm := (m).mterm;
              with (state1 = Follower) {
                votedFor := Nil;
                leader := (m).msource;
                with (i = self, j = (m).msource, logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len(log)))) /\ (((m).mprevLogTerm) = (((log)[(m).mprevLogIndex]).term)))) {
                  assert ((m).mterm) <= (currentTerm);
                  if((((m).mterm) = (currentTerm)) /\ ((state1) = (Candidate))) {
                    state := Follower;
                    if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value20 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd10 = (fd)[j]) {
                          await yielded_fd10;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                      with (index = ((m).mprevLogIndex) + (1)) {
                        if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log4 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                            if((((m).mentries) # (<<>>)) /\ ((Len(log4)) = ((m).mprevLogIndex))) {
                              log := Append(log4, ((m).mentries)[1]);
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                either {
                                  with (value30 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value30), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd20 = (fd)[j]) {
                                    await yielded_fd20;
                                    goto serverLoop;
                                  };
                                };
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                either {
                                  with (value31 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value31), enabled |-> ((network)[j]).enabled]];
                                    log := log4;
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd21 = (fd)[j]) {
                                    await yielded_fd21;
                                    log := log4;
                                    goto serverLoop;
                                  };
                                };
                              } else {
                                log := log4;
                                goto serverLoop;
                              };
                            };
                          };
                        } else {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                            log := Append(log, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value32 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value32), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd22 = (fd)[j]) {
                                  await yielded_fd22;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value33 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value33), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd23 = (fd)[j]) {
                                  await yielded_fd23;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              goto serverLoop;
                            };
                          };
                        };
                      };
                    };
                  } else {
                    if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state1) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value21 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]];
                          state := state1;
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd11 = (fd)[j]) {
                          await yielded_fd11;
                          state := state1;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = (currentTerm)) /\ ((state1) = (Follower))) /\ (logOK);
                      with (index = ((m).mprevLogIndex) + (1)) {
                        if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log5 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                            if((((m).mentries) # (<<>>)) /\ ((Len(log5)) = ((m).mprevLogIndex))) {
                              log := Append(log5, ((m).mentries)[1]);
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                either {
                                  with (value34 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value34), enabled |-> ((network)[j]).enabled]];
                                    state := state1;
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd24 = (fd)[j]) {
                                    await yielded_fd24;
                                    state := state1;
                                    goto serverLoop;
                                  };
                                };
                              } else {
                                state := state1;
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                either {
                                  with (value35 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value35), enabled |-> ((network)[j]).enabled]];
                                    log := log5;
                                    state := state1;
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd25 = (fd)[j]) {
                                    await yielded_fd25;
                                    log := log5;
                                    state := state1;
                                    goto serverLoop;
                                  };
                                };
                              } else {
                                log := log5;
                                state := state1;
                                goto serverLoop;
                              };
                            };
                          };
                        } else {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                            log := Append(log, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value36 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value36), enabled |-> ((network)[j]).enabled]];
                                  state := state1;
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd26 = (fd)[j]) {
                                  await yielded_fd26;
                                  state := state1;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              state := state1;
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value37 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value37), enabled |-> ((network)[j]).enabled]];
                                  state := state1;
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd27 = (fd)[j]) {
                                  await yielded_fd27;
                                  state := state1;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              state := state1;
                              goto serverLoop;
                            };
                          };
                        };
                      };
                    };
                  };
                };
              };
            } else {
              leader := (m).msource;
              with (i = self, j = (m).msource, logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len(log)))) /\ (((m).mprevLogTerm) = (((log)[(m).mprevLogIndex]).term)))) {
                assert ((m).mterm) <= (currentTerm);
                if((((m).mterm) = (currentTerm)) /\ ((state) = (Candidate))) {
                  state := Follower;
                  if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (~ (logOK)))) {
                    either {
                      with (value22 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]];
                        goto serverLoop;
                      };
                    } or {
                      with (yielded_fd12 = (fd)[j]) {
                        await yielded_fd12;
                        goto serverLoop;
                      };
                    };
                  } else {
                    assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                    with (index = ((m).mprevLogIndex) + (1)) {
                      if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log6 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log6)) = ((m).mprevLogIndex))) {
                            log := Append(log6, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value38 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value38), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd28 = (fd)[j]) {
                                  await yielded_fd28;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value39 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value39), enabled |-> ((network)[j]).enabled]];
                                  log := log6;
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd29 = (fd)[j]) {
                                  await yielded_fd29;
                                  log := log6;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              log := log6;
                              goto serverLoop;
                            };
                          };
                        };
                      } else {
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            either {
                              with (value310 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value310), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd210 = (fd)[j]) {
                                await yielded_fd210;
                                goto serverLoop;
                              };
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            either {
                              with (value311 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value311), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd211 = (fd)[j]) {
                                await yielded_fd211;
                                goto serverLoop;
                              };
                            };
                          } else {
                            goto serverLoop;
                          };
                        };
                      };
                    };
                  };
                } else {
                  if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (~ (logOK)))) {
                    either {
                      with (value23 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]];
                        goto serverLoop;
                      };
                    } or {
                      with (yielded_fd13 = (fd)[j]) {
                        await yielded_fd13;
                        goto serverLoop;
                      };
                    };
                  } else {
                    assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                    with (index = ((m).mprevLogIndex) + (1)) {
                      if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log7 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log7)) = ((m).mprevLogIndex))) {
                            log := Append(log7, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value312 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value312), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd212 = (fd)[j]) {
                                  await yielded_fd212;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              either {
                                with (value313 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value313), enabled |-> ((network)[j]).enabled]];
                                  log := log7;
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd213 = (fd)[j]) {
                                  await yielded_fd213;
                                  log := log7;
                                  goto serverLoop;
                                };
                              };
                            } else {
                              log := log7;
                              goto serverLoop;
                            };
                          };
                        };
                      } else {
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            either {
                              with (value314 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value314), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd214 = (fd)[j]) {
                                await yielded_fd214;
                                goto serverLoop;
                              };
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            either {
                              with (value315 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value315), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd215 = (fd)[j]) {
                                await yielded_fd215;
                                goto serverLoop;
                              };
                            };
                          } else {
                            goto serverLoop;
                          };
                        };
                      };
                    };
                  };
                };
              };
            };
          } else {
            if(((m).mtype) = (AppendEntriesResponse)) {
              if(((m).mterm) > (currentTerm)) {
                currentTerm := (m).mterm;
                state := Follower;
                votedFor := Nil;
                if(((m).mterm) < (currentTerm)) {
                  goto serverLoop;
                } else {
                  with (i = self, j = (m).msource) {
                    assert ((m).mterm) = (currentTerm);
                    if((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![j] = ((m).mmatchIndex) + (1)];
                      matchIndex := [matchIndex EXCEPT ![j] = (m).mmatchIndex];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![j] = Max({((nextIndex)[j]) - (1), 1})];
                      goto serverLoop;
                    };
                  };
                };
              } else {
                if(((m).mterm) < (currentTerm)) {
                  goto serverLoop;
                } else {
                  with (i = self, j = (m).msource) {
                    assert ((m).mterm) = (currentTerm);
                    if((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![j] = ((m).mmatchIndex) + (1)];
                      matchIndex := [matchIndex EXCEPT ![j] = (m).mmatchIndex];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![j] = Max({((nextIndex)[j]) - (1), 1})];
                      goto serverLoop;
                    };
                  };
                };
              };
            } else {
              if(((m).mtype) = (ClientPutRequest)) {
                if((state) = (Leader)) {
                  with (entry = [term |-> currentTerm, key |-> (m).mkey, value |-> (m).mvalue]) {
                    log := Append(log, entry);
                    goto serverLoop;
                  };
                } else {
                  goto serverLoop;
                };
              } else {
                goto serverLoop;
              };
            };
          };
        };
      };
    requestVoteLoop:
      if((idx) <= (NumServers)) {
        if((idx) # (self)) {
          either {
            with (value40 = [mtype |-> RequestVoteRequest, mterm |-> currentTerm, mlastLogTerm |-> LastTerm(log), mlastLogIndex |-> Len(log), msource |-> self, mdest |-> idx]) {
              await ((network)[idx]).enabled;
              await (Len(((network)[idx]).queue)) < (BufferSize);
              with (network1 = [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value40), enabled |-> ((network)[idx]).enabled]]) {
                idx := (idx) + (1);
                if(ExploreFail) {
                  either {
                    skip;
                    network := network1;
                    goto requestVoteLoop;
                  } or {
                    with (value50 = FALSE) {
                      network := [network1 EXCEPT ![self] = [queue |-> ((network1)[self]).queue, enabled |-> value50]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network1;
                  goto requestVoteLoop;
                };
              };
            };
          } or {
            with (yielded_fd30 = (fd)[idx]) {
              await yielded_fd30;
              idx := (idx) + (1);
              if(ExploreFail) {
                either {
                  skip;
                  goto requestVoteLoop;
                } or {
                  with (value51 = FALSE) {
                    network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value51]];
                    goto failLabel;
                  };
                };
              } else {
                goto requestVoteLoop;
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if(ExploreFail) {
            either {
              skip;
              goto requestVoteLoop;
            } or {
              with (value52 = FALSE) {
                network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value52]];
                goto failLabel;
              };
            };
          } else {
            goto requestVoteLoop;
          };
        };
      } else {
        goto serverLoop;
      };
    appendEntriesLoop:
      if((idx) <= (NumServers)) {
        if((idx) # (self)) {
          with (prevLogIndex1 = ((nextIndex)[idx]) - (1), prevLogTerm1 = IF (prevLogIndex1) > (0) THEN ((log)[prevLogIndex1]).term ELSE 0, lastEntry1 = Min({Len(log), (nextIndex)[idx]}), entries1 = SubSeq(log, (nextIndex)[idx], lastEntry1)) {
            either {
              with (value60 = [mtype |-> AppendEntriesRequest, mterm |-> currentTerm, mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({commitIndex, lastEntry1}), msource |-> self, mdest |-> idx]) {
                await ((network)[idx]).enabled;
                await (Len(((network)[idx]).queue)) < (BufferSize);
                with (network2 = [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value60), enabled |-> ((network)[idx]).enabled]]) {
                  idx := (idx) + (1);
                  if(ExploreFail) {
                    either {
                      skip;
                      network := network2;
                      goto appendEntriesLoop;
                    } or {
                      with (value70 = FALSE) {
                        network := [network2 EXCEPT ![self] = [queue |-> ((network2)[self]).queue, enabled |-> value70]];
                        goto failLabel;
                      };
                    };
                  } else {
                    network := network2;
                    goto appendEntriesLoop;
                  };
                };
              };
            } or {
              with (yielded_fd40 = (fd)[idx]) {
                await yielded_fd40;
                idx := (idx) + (1);
                if(ExploreFail) {
                  either {
                    skip;
                    goto appendEntriesLoop;
                  } or {
                    with (value71 = FALSE) {
                      network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value71]];
                      goto failLabel;
                    };
                  };
                } else {
                  goto appendEntriesLoop;
                };
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if(ExploreFail) {
            either {
              skip;
              goto appendEntriesLoop;
            } or {
              with (value72 = FALSE) {
                network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value72]];
                goto failLabel;
              };
            };
          } else {
            goto appendEntriesLoop;
          };
        };
      } else {
        goto serverLoop;
      };
    failLabel:
      with (value80 = TRUE) {
        fd := [fd EXCEPT ![self] = value80];
        goto Done;
      };
  }
  
  fair process (client \in ClientSet)
  {
    sndPutReq:
      with (srv = 1) {
        with (value90 = [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv]) {
          await ((network)[srv]).enabled;
          await (Len(((network)[srv]).queue)) < (BufferSize);
          network := [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value90), enabled |-> ((network)[srv]).enabled]];
          goto clientBlock;
        };
      };
    clientBlock:
      await FALSE;
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "3cf90fe3" /\ chksum(tla) = "cf912e26")
CONSTANT defaultInitValue
VARIABLES network, fd, pc

(* define statement *)
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
Key1 == "key1"
Value1 == "value1"
Min(s) == CHOOSE x \in s : \A y \in s : (x) <= (y)
Max(s) == CHOOSE x \in s : \A y \in s : (x) >= (y)
LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
Nil == 0
ServerSet == (1) .. (NumServers)
ClientSet == ((NumServers) + (1)) .. ((NumServers) + (NumClients))
isQuorum(s) == ((Cardinality(s)) * (2)) > (NumServers)

VARIABLES currentTerm, state, votedFor, log, commitIndex, nextIndex, 
          matchIndex, votesResponded, votesGranted, leader, idx, m

vars == << network, fd, pc, currentTerm, state, votedFor, log, commitIndex, 
           nextIndex, matchIndex, votesResponded, votesGranted, leader, idx, 
           m >>

ProcSet == (ServerSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [i \in ServerSet |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [i \in ServerSet |-> FALSE]
        (* Process server *)
        /\ currentTerm = [self \in ServerSet |-> 1]
        /\ state = [self \in ServerSet |-> Follower]
        /\ votedFor = [self \in ServerSet |-> Nil]
        /\ log = [self \in ServerSet |-> <<>>]
        /\ commitIndex = [self \in ServerSet |-> 0]
        /\ nextIndex = [self \in ServerSet |-> [i \in ServerSet |-> 1]]
        /\ matchIndex = [self \in ServerSet |-> [i \in ServerSet |-> 0]]
        /\ votesResponded = [self \in ServerSet |-> {}]
        /\ votesGranted = [self \in ServerSet |-> {}]
        /\ leader = [self \in ServerSet |-> Nil]
        /\ idx = [self \in ServerSet |-> 1]
        /\ m = [self \in ServerSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ClientSet -> "sndPutReq"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 460, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          LET network0 == [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]] IN
                                            LET yielded_network1 == readMsg00 IN
                                              /\ m' = [m EXCEPT ![self] = yielded_network1]
                                              /\ Assert(((m'[self]).mdest) = (self), 
                                                        "Failure of assertion at line 466, column 17.")
                                              /\ IF ExploreFail
                                                    THEN /\ \/ /\ TRUE
                                                               /\ network' = network0
                                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                                            \/ /\ LET value00 == FALSE IN
                                                                    /\ network' = [network0 EXCEPT ![self] = [queue |-> ((network0)[self]).queue, enabled |-> value00]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                    ELSE /\ network' = network0
                                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, idx>>
                                  \/ /\ (state[self]) \in ({Follower, Candidate})
                                     /\ LET yielded_network00 == Len(((network)[self]).queue) IN
                                          LET yielded_fd5 == (fd)[leader[self]] IN
                                            /\ ((yielded_network00) = (0)) /\ (((leader[self]) = (Nil)) \/ (((leader[self]) # (Nil)) /\ (yielded_fd5)))
                                            /\ state' = [state EXCEPT ![self] = Candidate]
                                            /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                                            /\ votedFor' = [votedFor EXCEPT ![self] = self]
                                            /\ votesResponded' = [votesResponded EXCEPT ![self] = {self}]
                                            /\ votesGranted' = [votesGranted EXCEPT ![self] = {self}]
                                            /\ idx' = [idx EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                     /\ UNCHANGED <<network, commitIndex, nextIndex, matchIndex, m>>
                                  \/ /\ (state[self]) = (Leader)
                                     /\ LET agreeIndexes1 == {index \in (1) .. (Len(log[self])) : isQuorum(({self}) \union ({k \in ServerSet : ((matchIndex[self])[k]) >= (index)}))} IN
                                          LET newCommitIndex1 == IF ((agreeIndexes1) # ({})) /\ ((((log[self])[Max(agreeIndexes1)]).term) = (currentTerm[self])) THEN Max(agreeIndexes1) ELSE commitIndex[self] IN
                                            /\ Assert((newCommitIndex1) >= (commitIndex[self]), 
                                                      "Failure of assertion at line 502, column 13.")
                                            /\ commitIndex' = [commitIndex EXCEPT ![self] = newCommitIndex1]
                                            /\ idx' = [idx EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                     /\ UNCHANGED <<network, currentTerm, state, votedFor, nextIndex, matchIndex, votesResponded, votesGranted, m>>
                                  \/ /\ ((state[self]) = (Candidate)) /\ (isQuorum(votesGranted[self]))
                                     /\ state' = [state EXCEPT ![self] = Leader]
                                     /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                     /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                     /\ UNCHANGED <<network, currentTerm, votedFor, commitIndex, votesResponded, votesGranted, idx, m>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                               /\ UNCHANGED << network, currentTerm, state, 
                                               votedFor, commitIndex, 
                                               nextIndex, matchIndex, 
                                               votesResponded, votesGranted, 
                                               idx, m >>
                    /\ UNCHANGED << fd, log, leader >>

handleMsg(self) == /\ pc[self] = "handleMsg"
                   /\ IF ((m[self]).mtype) = (RequestVoteRequest)
                         THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                    THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                         /\ state' = [state EXCEPT ![self] = Follower]
                                         /\ LET votedFor1 == Nil IN
                                              LET i == self IN
                                                LET j == (m[self]).msource IN
                                                  LET logOK == (((m[self]).mlastLogTerm) > (LastTerm(log[self]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm(log[self]))) /\ (((m[self]).mlastLogIndex) >= (Len(log[self])))) IN
                                                    LET grant == ((((m[self]).mterm) = (currentTerm'[self])) /\ (logOK)) /\ ((votedFor1) \in ({Nil, j})) IN
                                                      /\ Assert(((m[self]).mterm) <= (currentTerm'[self]), 
                                                                "Failure of assertion at line 524, column 15.")
                                                      /\ IF grant
                                                            THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                                 /\ \/ /\ LET value10 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                            /\ ((network)[j]).enabled
                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                    \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                            /\ yielded_fd00
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ \/ /\ LET value11 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                            /\ ((network)[j]).enabled
                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]]
                                                                            /\ votedFor' = [votedFor EXCEPT ![self] = votedFor1]
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                    \/ /\ LET yielded_fd01 == (fd)[j] IN
                                                                            /\ yielded_fd01
                                                                            /\ votedFor' = [votedFor EXCEPT ![self] = votedFor1]
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       /\ UNCHANGED network
                                    ELSE /\ LET i == self IN
                                              LET j == (m[self]).msource IN
                                                LET logOK == (((m[self]).mlastLogTerm) > (LastTerm(log[self]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm(log[self]))) /\ (((m[self]).mlastLogIndex) >= (Len(log[self])))) IN
                                                  LET grant == ((((m[self]).mterm) = (currentTerm[self])) /\ (logOK)) /\ ((votedFor[self]) \in ({Nil, j})) IN
                                                    /\ Assert(((m[self]).mterm) <= (currentTerm[self]), 
                                                              "Failure of assertion at line 561, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                               /\ \/ /\ LET value12 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                          /\ yielded_fd02
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                          ELSE /\ \/ /\ LET value13 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                          /\ yielded_fd03
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << currentTerm, state >>
                              /\ UNCHANGED << log, commitIndex, nextIndex, 
                                              matchIndex, votesResponded, 
                                              votesGranted, leader >>
                         ELSE /\ IF ((m[self]).mtype) = (RequestVoteResponse)
                                    THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                    /\ state' = [state EXCEPT ![self] = Follower]
                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                    /\ IF ((m[self]).mterm) < (currentTerm'[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = (currentTerm'[self]), 
                                                                                "Failure of assertion at line 604, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j})]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED votesGranted
                                               ELSE /\ IF ((m[self]).mterm) < (currentTerm[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = (currentTerm[self]), 
                                                                                "Failure of assertion at line 619, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j})]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED votesGranted
                                                    /\ UNCHANGED << currentTerm, 
                                                                    state, 
                                                                    votedFor >>
                                         /\ UNCHANGED << network, log, 
                                                         commitIndex, 
                                                         nextIndex, matchIndex, 
                                                         leader >>
                                    ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                               /\ LET state1 == Follower IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                    /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                                    /\ LET i == self IN
                                                                         LET j == (m[self]).msource IN
                                                                           LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len(log[self])))) /\ (((m[self]).mprevLogTerm) = (((log[self])[(m[self]).mprevLogIndex]).term))) IN
                                                                             /\ Assert(((m[self]).mterm) <= (currentTerm'[self]), 
                                                                                       "Failure of assertion at line 638, column 19.")
                                                                             /\ IF (((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Candidate))
                                                                                   THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                        /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ \/ /\ LET value20 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                              /\ ((network)[j]).enabled
                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]]
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                      \/ /\ LET yielded_fd10 == (fd)[j] IN
                                                                                                              /\ yielded_fd10
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                         /\ UNCHANGED network
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 656, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log4 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log4, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value30 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value30), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd20 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd20
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value31 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value31), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd21 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd21
                                                                                                                                                   /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value32 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value32), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd22 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd22
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value33 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value33), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd23 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd23
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                                                   ELSE /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ \/ /\ LET value21 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                              /\ ((network)[j]).enabled
                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]]
                                                                                                              /\ state' = [state EXCEPT ![self] = state1]
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                      \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                              /\ yielded_fd11
                                                                                                              /\ state' = [state EXCEPT ![self] = state1]
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                         /\ UNCHANGED network
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 766, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log5 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log5, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value34 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value34), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd24 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd24
                                                                                                                                                   /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value35 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value35), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                                   /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd25 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd25
                                                                                                                                                   /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                                   /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                        /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value36 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value36), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd26 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd26
                                                                                                                                                 /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value37 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value37), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd27 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd27
                                                                                                                                                 /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len(log[self])))) /\ (((m[self]).mprevLogTerm) = (((log[self])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= (currentTerm[self]), 
                                                                                  "Failure of assertion at line 876, column 17.")
                                                                        /\ IF (((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value22 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                         /\ yielded_fd12
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 894, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log6, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value38 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value38), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd28 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd28
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value39 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value39), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd29 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd29
                                                                                                                                              /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value310 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value310), enabled |-> ((network)[j]).enabled]]
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                    \/ /\ LET yielded_fd210 == (fd)[j] IN
                                                                                                                                            /\ yielded_fd210
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                       /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value311 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value311), enabled |-> ((network)[j]).enabled]]
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                    \/ /\ LET yielded_fd211 == (fd)[j] IN
                                                                                                                                            /\ yielded_fd211
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                       /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                      /\ log' = log
                                                                              ELSE /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value23 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                         /\ yielded_fd13
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 1002, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log7, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value312 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value312), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd212 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd212
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value313 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value313), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd213 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd213
                                                                                                                                              /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value314 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value314), enabled |-> ((network)[j]).enabled]]
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                    \/ /\ LET yielded_fd214 == (fd)[j] IN
                                                                                                                                            /\ yielded_fd214
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                       /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value315 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value315), enabled |-> ((network)[j]).enabled]]
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                    \/ /\ LET yielded_fd215 == (fd)[j] IN
                                                                                                                                            /\ yielded_fd215
                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                       /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                      /\ log' = log
                                                                                   /\ state' = state
                                                               /\ UNCHANGED << currentTerm, 
                                                                               votedFor >>
                                                    /\ UNCHANGED << nextIndex, 
                                                                    matchIndex >>
                                               ELSE /\ IF ((m[self]).mtype) = (AppendEntriesResponse)
                                                          THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                                                     THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                                          /\ state' = [state EXCEPT ![self] = Follower]
                                                                          /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                          /\ IF ((m[self]).mterm) < (currentTerm'[self])
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = (currentTerm'[self]), 
                                                                                                      "Failure of assertion at line 1107, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = Max({((nextIndex[self])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                     ELSE /\ IF ((m[self]).mterm) < (currentTerm[self])
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = (currentTerm[self]), 
                                                                                                      "Failure of assertion at line 1123, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = Max({((nextIndex[self])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                          /\ UNCHANGED << currentTerm, 
                                                                                          state, 
                                                                                          votedFor >>
                                                               /\ log' = log
                                                          ELSE /\ IF ((m[self]).mtype) = (ClientPutRequest)
                                                                     THEN /\ IF (state[self]) = (Leader)
                                                                                THEN /\ LET entry == [term |-> currentTerm[self], key |-> (m[self]).mkey, value |-> (m[self]).mvalue] IN
                                                                                          /\ log' = [log EXCEPT ![self] = Append(log[self], entry)]
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ log' = log
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ log' = log
                                                               /\ UNCHANGED << currentTerm, 
                                                                               state, 
                                                                               votedFor, 
                                                                               nextIndex, 
                                                                               matchIndex >>
                                                    /\ UNCHANGED << network, 
                                                                    commitIndex, 
                                                                    leader >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted >>
                   /\ UNCHANGED << fd, idx, m >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx[self]) <= (NumServers)
                               THEN /\ IF (idx[self]) # (self)
                                          THEN /\ \/ /\ LET value40 == [mtype |-> RequestVoteRequest, mterm |-> currentTerm[self], mlastLogTerm |-> LastTerm(log[self]), mlastLogIndex |-> Len(log[self]), msource |-> self, mdest |-> idx[self]] IN
                                                          /\ ((network)[idx[self]]).enabled
                                                          /\ (Len(((network)[idx[self]]).queue)) < (BufferSize)
                                                          /\ LET network1 == [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value40), enabled |-> ((network)[idx[self]]).enabled]] IN
                                                               /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                               /\ IF ExploreFail
                                                                     THEN /\ \/ /\ TRUE
                                                                                /\ network' = network1
                                                                                /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                             \/ /\ LET value50 == FALSE IN
                                                                                     /\ network' = [network1 EXCEPT ![self] = [queue |-> ((network1)[self]).queue, enabled |-> value50]]
                                                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                     ELSE /\ network' = network1
                                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                  \/ /\ LET yielded_fd30 == (fd)[idx[self]] IN
                                                          /\ yielded_fd30
                                                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                          /\ IF ExploreFail
                                                                THEN /\ \/ /\ TRUE
                                                                           /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                           /\ UNCHANGED network
                                                                        \/ /\ LET value51 == FALSE IN
                                                                                /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value51]]
                                                                                /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                     /\ UNCHANGED network
                                          ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                               /\ IF ExploreFail
                                                     THEN /\ \/ /\ TRUE
                                                                /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                /\ UNCHANGED network
                                                             \/ /\ LET value52 == FALSE IN
                                                                     /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value52]]
                                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                          /\ UNCHANGED network
                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                    /\ UNCHANGED << network, idx >>
                         /\ UNCHANGED << fd, currentTerm, state, votedFor, log, 
                                         commitIndex, nextIndex, matchIndex, 
                                         votesResponded, votesGranted, leader, 
                                         m >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ IF (idx[self]) <= (NumServers)
                                 THEN /\ IF (idx[self]) # (self)
                                            THEN /\ LET prevLogIndex1 == ((nextIndex[self])[idx[self]]) - (1) IN
                                                      LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN ((log[self])[prevLogIndex1]).term ELSE 0 IN
                                                        LET lastEntry1 == Min({Len(log[self]), (nextIndex[self])[idx[self]]}) IN
                                                          LET entries1 == SubSeq(log[self], (nextIndex[self])[idx[self]], lastEntry1) IN
                                                            \/ /\ LET value60 == [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[self], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({commitIndex[self], lastEntry1}), msource |-> self, mdest |-> idx[self]] IN
                                                                    /\ ((network)[idx[self]]).enabled
                                                                    /\ (Len(((network)[idx[self]]).queue)) < (BufferSize)
                                                                    /\ LET network2 == [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value60), enabled |-> ((network)[idx[self]]).enabled]] IN
                                                                         /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                                         /\ IF ExploreFail
                                                                               THEN /\ \/ /\ TRUE
                                                                                          /\ network' = network2
                                                                                          /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                                       \/ /\ LET value70 == FALSE IN
                                                                                               /\ network' = [network2 EXCEPT ![self] = [queue |-> ((network2)[self]).queue, enabled |-> value70]]
                                                                                               /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                               ELSE /\ network' = network2
                                                                                    /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                            \/ /\ LET yielded_fd40 == (fd)[idx[self]] IN
                                                                    /\ yielded_fd40
                                                                    /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                                    /\ IF ExploreFail
                                                                          THEN /\ \/ /\ TRUE
                                                                                     /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                                     /\ UNCHANGED network
                                                                                  \/ /\ LET value71 == FALSE IN
                                                                                          /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value71]]
                                                                                          /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                               /\ UNCHANGED network
                                            ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                 /\ IF ExploreFail
                                                       THEN /\ \/ /\ TRUE
                                                                  /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                  /\ UNCHANGED network
                                                               \/ /\ LET value72 == FALSE IN
                                                                       /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value72]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                            /\ UNCHANGED network
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                      /\ UNCHANGED << network, idx >>
                           /\ UNCHANGED << fd, currentTerm, state, votedFor, 
                                           log, commitIndex, nextIndex, 
                                           matchIndex, votesResponded, 
                                           votesGranted, leader, m >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value80 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value80]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, currentTerm, state, votedFor, log, 
                                   commitIndex, nextIndex, matchIndex, 
                                   votesResponded, votesGranted, leader, idx, 
                                   m >>

server(self) == serverLoop(self) \/ handleMsg(self)
                   \/ requestVoteLoop(self) \/ appendEntriesLoop(self)
                   \/ failLabel(self)

sndPutReq(self) == /\ pc[self] = "sndPutReq"
                   /\ LET srv == 1 IN
                        LET value90 == [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv] IN
                          /\ ((network)[srv]).enabled
                          /\ (Len(((network)[srv]).queue)) < (BufferSize)
                          /\ network' = [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value90), enabled |-> ((network)[srv]).enabled]]
                          /\ pc' = [pc EXCEPT ![self] = "clientBlock"]
                   /\ UNCHANGED << fd, currentTerm, state, votedFor, log, 
                                   commitIndex, nextIndex, matchIndex, 
                                   votesResponded, votesGranted, leader, idx, 
                                   m >>

clientBlock(self) == /\ pc[self] = "clientBlock"
                     /\ FALSE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << network, fd, currentTerm, state, votedFor, 
                                     log, commitIndex, nextIndex, matchIndex, 
                                     votesResponded, votesGranted, leader, idx, 
                                     m >>

client(self) == sndPutReq(self) \/ clientBlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: server(self))
           \/ (\E self \in ClientSet: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(server(self))
        /\ \A self \in ClientSet : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Constraints

LimitTerm == \A i \in ServerSet: currentTerm[i] <= MaxTerm
LimitCommitIndex == \A i \in ServerSet: commitIndex[i] <= MaxCommitIndex

LimitNodeFailure == Cardinality({i \in ServerSet: \lnot network[i].enabled}) <= MaxNodeFail

\* Invariants

ElectionSatefy == \lnot (\E i, j \in ServerSet:
                                        /\ i /= j
                                        /\ currentTerm[i] = currentTerm[j]
                                        /\ state[i] = Leader
                                        /\ state[j] = Leader)

LogMatching == \A i, j \in ServerSet:
                        \A k \in 1..Min({Len(log[i]), Len(log[j])}):
                            log[i][k].term = log[j][k].term
                                => SubSeq(log[i], 1, k) = SubSeq(log[j], 1, k)

LogCompleteness == \A i \in ServerSet: state[i] = Leader =>
                        \A j \in ServerSet:
                            /\ Len(log[i]) >= commitIndex[j] 
                            /\ SubSeq(log[i], 1, commitIndex[j]) = SubSeq(log[j], 1, commitIndex[j])

StateMachineSafety == \A i, j \in ServerSet:
                            \A k \in 1..Min({commitIndex[i], commitIndex[j]}):
                                        log[i][k] = log[j][k]

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

\* Expected this to be violated if NumServers > 1,
\* but TLC doesn't report violation in case of NumServers = 2 because 
\* of using temporal properties and state constraints at the same time. 
\* TLC reports violation when NumServers = 3.
ElectionLiveness == <>(\E i \in ServerSet: state[i] = Leader)

=============================================================================
