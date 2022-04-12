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

CONSTANT Debug

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

        ServerSet       == 1..NumServers
        ServerSenderSet == (NumServers+1)..(NumServers+NumServers)
        ClientSet       == (2*NumServers+1)..(2*NumServers+NumClients)

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

    macro checkFail(selfId, netEnabled) {
        if (ExploreFail) {
            if (\lnot netEnabled[selfId]) {
                goto Done;
            };
        };
    }

    macro debug(toprint) {
        if (Debug) {
            print toprint;
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
        if (m.mterm > currentTerm[i]) {
            currentTerm[i] := m.mterm;
            state[i]       := Follower;
            votedFor       := Nil;
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

    mapping macro PracticalFD {
        read {
            either {
                yield TRUE;
            } or {
                yield FALSE;
            };
        }

        write { yield $value; }
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

    archetype AServer(
        ref net[_], ref fd[_], ref netLen[_], ref netEnabled[_],
        ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref timer, ref in
    )
    variables
        votedFor = Nil,
    
        matchIndex = [t \in ServerSet |-> 0],

        votesResponded = {},
        votesGranted   = {},

        \* added by Shayan
        leader = Nil, 
        idx    = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            \* if (commitIndex[self] > 0) {
            \*     print <<state[self], self, log[self], commitIndex[self], currentTerm[self]>>;
            \* };
            \* print <<"server", self, state[self], currentTerm[self], leader>>;

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
                        logOK = \/ m.mlastLogTerm > LastTerm(log[i])
                                \/ /\ m.mlastLogTerm = LastTerm(log[i])
                                   /\ m.mlastLogIndex >= Len(log[i]),
                        grant = /\ m.mterm = currentTerm[i]
                                /\ logOK
                                /\ votedFor \in {Nil, j} 
                    ) {
                        assert m.mterm <= currentTerm[i];
                        if (grant) {
                            votedFor := j; 
                        };
                        Send(net, j, fd, [
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j
                        ]);
                    };
                } else if (m.mtype = RequestVoteResponse) {
                    UpdateTerm(self, m, currentTerm, state, votedFor);

                    \* DropStaleResponse
                    if (m.mterm < currentTerm[self]) {
                        goto serverLoop;
                    } else {
                        \* HandleRequestVoteResponse
                        with (i = self, j = m.msource) {
                            assert m.mterm = currentTerm[i];
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
                                   /\ m.mprevLogIndex <= Len(log[i])
                                   /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
                    ) {
                        assert m.mterm <= currentTerm[i];

                        \* return to follower state
                        if (
                            /\ m.mterm = currentTerm[i]
                            /\ state[i] = Candidate
                        ) {
                            state[i] := Follower;
                        };

                        \* reject request
                        if (
                            \/ m.mterm < currentTerm[i]
                            \/ /\ m.mterm = currentTerm[i]
                               /\ state[i] = Follower
                               /\ \lnot logOK
                        ) {
                            Send(net, j, fd, [
                                mtype       |-> AppendEntriesResponse,
                                mterm       |-> currentTerm[i],
                                msuccess    |-> FALSE,
                                mmatchIndex |-> 0,
                                msource     |-> i,
                                mdest       |-> j
                            ]);
                        } 
                        \* accept request
                        else {
                            assert (
                                /\ m.mterm = currentTerm[i]
                                /\ state[i] = Follower
                                /\ logOK
                            );
                            with (index = m.mprevLogIndex + 1) {
                                \* conflict: remove 1 entry
                                if (
                                    /\ m.mentries /= << >>
                                    /\ Len(log[i]) >= index
                                    /\ log[i][index].term /= m.mentries[1].term
                                ) {
                                    \* log[i] := [k \in 1..(Len(log[i])-1) |-> log[i][k]];
                                    log[i] := SubSeq(log[i], 1, Len(log[i]) - 1);
                                };
                                
                                \* no conflict: append entry
                                if (
                                    /\ m.mentries /= << >>
                                    /\ Len(log[i]) = m.mprevLogIndex
                                ) {
                                    \* log[i] := Append(log[i], m.mentries[1]);
                                    log[i] := log[i] \o m.mentries;
                                };

                                \* already done with request
                                if (
                                    \/ m.mentries = << >>
                                    \/ /\ m.mentries /= << >>
                                       /\ Len(log[i]) >= index
                                       /\ log[i][index].term = m.mentries[1].term
                                ) {
                                    \* This could make our commitIndex decrease (for
                                    \* example if we process an old, duplicated request),
                                    \* but that doesn't really affect anything.
                                    commitIndex[i] := m.mcommitIndex;
                                    Send(net, j, fd, [
                                        mtype       |-> AppendEntriesResponse,
                                        mterm       |-> currentTerm[i],
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
                    if (m.mterm < currentTerm[self]) {
                        goto serverLoop;
                    } else {
                        \* HandleAppendEntriesResponse
                        with (i = self, j = m.msource) {
                            assert m.mterm = currentTerm[i];
                            if (m.msuccess) {
                                nextIndex[i] := [nextIndex[i] EXCEPT ![j] = m.mmatchIndex + 1];
                                \* nextIndex[j]  := m.mmatchIndex + 1;
                                matchIndex[j] := m.mmatchIndex;
                            } else {
                                nextIndex[i] := [nextIndex[i] EXCEPT ![j] = Max({nextIndex[i][j]-1, 1})];
                                \* nextIndex[j]  := Max({nextIndex[j]-1, 1});
                            };
                        };
                    };
                } else if (m.mtype = ClientPutRequest) {
                    \* ClientRequest
                    if (state[self] = Leader) {
                        with (entry = [term  |-> currentTerm[self], 
                                       key   |-> m.mkey,
                                       value |-> m.mvalue]
                        ) {
                            log[self] := Append(log[self], entry);

                            in := TRUE;
                        };
                    };
                };
            } or {
                \* Server times out and starts a new election.
                await state[self] \in {Follower, Candidate};
                await (
                    /\ netLen[self] = 0
                    /\ timer
                    /\ \/ leader = Nil
                       \/ /\ leader /= Nil
                          /\ fd[leader]
                );
                with (i = self) {
                    state[i]       := Candidate;
                    currentTerm[i] := currentTerm[i] + 1;
                    votedFor       := i;
                    votesResponded := {i};
                    votesGranted   := {i};
                };

                idx := 1;
            requestVoteLoop:
                while (idx <= NumServers) {
                    \* RequestVote
                    if (idx /= self) {
                        Send(net, idx, fd, [
                            mtype         |-> RequestVoteRequest,
                            mterm         |-> currentTerm[self],
                            mlastLogTerm  |-> LastTerm(log[self]),
                            mlastLogIndex |-> Len(log[self]),
                            msource       |-> self,
                            mdest         |-> idx
                        ]);
                    };
                    idx := idx + 1;
                    mayFail(self, netEnabled);
                };
            } or {
                await state[self] = Leader;

                \* AdvanceCommitIndex
                with (
                    \* Agree(index) = [self] \cup {k \in ServerSet : 
                                                    \* matchIndex[k] >= index},
                    i = self,
                    agreeIndexes = {index \in 1..Len(log[i]) : 
                                        isQuorum({i} \cup {k \in ServerSet : 
                                                                matchIndex[k] >= index})},
                    newCommitIndex =
                        IF /\ agreeIndexes /= {}
                           /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
                        THEN Max(agreeIndexes)
                        ELSE commitIndex[i]
                ) {
                    \* print <<"advance commit index", i, agreeIndexes, newCommitIndex, commitIndex[i]>>;
                    assert newCommitIndex >= commitIndex[i];
                    commitIndex[i] := newCommitIndex;
                };
            } or {
                \* BecomeLeader
                await (
                    /\ state[self] = Candidate
                    /\ isQuorum(votesGranted)
                );
                with (i = self) {
                    state[i]     := Leader;
                    nextIndex[i] := [j \in ServerSet |-> Len(log[i]) + 1]; 
                    matchIndex   := [j \in ServerSet |-> 0];

                    in := TRUE;
                    debug(<<"BecomeLeader", i, currentTerm[i]>>);
                };
            };
        };

    failLabel:
        fd[self] := TRUE;
    }

    archetype AServerSender(
        ref net[_], ref fd[_], ref netEnabled[_],
        sid, ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref in
    )
    variables idx;
    {
    serverSenderLoop:
        while (in) {
            await state[sid] = Leader;
            idx := 1;
            \* print <<"sender", self, sid, state[sid], currentTerm[sid]>>;
            checkFail(sid, netEnabled);

        appendEntriesLoop:
            \* AppendEntries
            while (
                /\ netEnabled[sid]
                /\ state[sid] = Leader
                /\ idx <= NumServers
            ) {
                if (idx /= sid) {
                    with (
                        prevLogIndex = nextIndex[sid][idx] - 1,
                        prevLogTerm  = IF prevLogIndex > 0
                                       THEN log[sid][prevLogIndex].term
                                       ELSE 0,
                        lastEntry    = Min({Len(log[sid]), nextIndex[sid][idx]}),
                        entries      = SubSeq(log[sid], nextIndex[sid][idx], lastEntry)
                    ) {
                        Send(net, idx, fd, [
                            mtype         |-> AppendEntriesRequest,
                            mterm         |-> currentTerm[sid],
                            mprevLogIndex |-> prevLogIndex,
                            mprevLogTerm  |-> prevLogTerm,
                            mentries      |-> entries,
                            mcommitIndex  |-> Min({commitIndex[sid], lastEntry}),
                            msource       |-> sid,
                            mdest         |-> idx
                        ]);
                    };
                };
                idx := idx + 1;
            };
        };
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
    }

    archetype ALoopClient(ref net[_], ref fd[_], ref in) {
    clientLoop:
        while (TRUE) {
            with (req = in) {
                with (srv \in ServerSet) {
                    Send(net, srv, fd, [
                        mtype   |-> ClientPutRequest,
                        mkey    |-> req.key,
                        mvalue  |-> req.value,
                        msource |-> self,
                        mdest   |-> srv
                    ]);
                };
            };
        };
    }

    variables
        network = [i \in ServerSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd = [i \in ServerSet |-> FALSE];
    
        sm = [i \in ServerSenderSet |-> i - NumServers];

        state       = [i \in ServerSet |-> Follower];
        nextIndex   = [i \in ServerSet |-> [j \in ServerSet |-> 1]];
        log         = [i \in ServerSet |-> <<>>];
        currentTerm = [i \in ServerSet |-> 1];
        commitIndex = [i \in ServerSet |-> 0];
        
        timer = TRUE;
        in    = TRUE;

    fair process (server \in ServerSet) == instance AServer(
        ref network[_], ref fd[_], ref network[_], ref network[_],
        ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref timer, ref in
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle;
    
    fair process (sender \in ServerSenderSet) == instance AServerSender(
        ref network[_], ref fd[_], ref network[_],
        sm[sender], ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref in
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkToggle;
    
    fair process (client \in ClientSet) == instance AClient(ref network[_])
        mapping @1[_] via ReliableFIFOLink;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raft {
  variables network = [i \in ServerSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; sm = [i \in ServerSenderSet |-> (i) - (NumServers)]; state = [i \in ServerSet |-> Follower]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; log = [i \in ServerSet |-> <<>>]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; timer = TRUE; in = TRUE;
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
    ServerSenderSet == ((NumServers) + (1)) .. ((NumServers) + (NumServers))
    ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
    isQuorum(s) == ((Cardinality(s)) * (2)) > (NumServers)
  }
  
  fair process (server \in ServerSet)
    variables votedFor = Nil; matchIndex = [t \in ServerSet |-> 0]; votesResponded = {}; votesGranted = {}; leader = Nil; idx = 1; m;
  {
    serverLoop:
      if (TRUE) {
        either {
          assert ((network)[self]).enabled;
          await (Len(((network)[self]).queue)) > (0);
          with (
            readMsg00 = Head(((network)[self]).queue), 
            network0 = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]], 
            yielded_network3 = readMsg00
          ) {
            m := yielded_network3;
            assert ((m).mdest) = (self);
            if (ExploreFail) {
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
        } or {
          await ((state)[self]) \in ({Follower, Candidate});
          with (
            yielded_network00 = Len(((network)[self]).queue), 
            yielded_fd5 = (fd)[leader]
          ) {
            await (((yielded_network00) = (0)) /\ (timer)) /\ (((leader) = (Nil)) \/ (((leader) # (Nil)) /\ (yielded_fd5)));
            with (i1 = self) {
              state := [state EXCEPT ![i1] = Candidate];
              currentTerm := [currentTerm EXCEPT ![i1] = ((currentTerm)[i1]) + (1)];
              votedFor := i1;
              votesResponded := {i1};
              votesGranted := {i1};
              idx := 1;
              goto requestVoteLoop;
            };
          };
        } or {
          await ((state)[self]) = (Leader);
          with (
            i = self, 
            agreeIndexes = {index \in (1) .. (Len((log)[i])) : isQuorum(({i}) \union ({k \in ServerSet : ((matchIndex)[k]) >= (index)}))}, 
            newCommitIndex = IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i]
          ) {
            assert (newCommitIndex) >= ((commitIndex)[i]);
            commitIndex := [commitIndex EXCEPT ![i] = newCommitIndex];
            goto serverLoop;
          };
        } or {
          await (((state)[self]) = (Candidate)) /\ (isQuorum(votesGranted));
          with (i = self) {
            state := [state EXCEPT ![i] = Leader];
            nextIndex := [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]];
            matchIndex := [j \in ServerSet |-> 0];
            in := TRUE;
            if (Debug) {
              print <<"BecomeLeader", i, (currentTerm)[i]>>;
              goto serverLoop;
            } else {
              goto serverLoop;
            };
          };
        };
      } else {
        goto failLabel;
      };
    handleMsg:
      if (((m).mtype) = (RequestVoteRequest)) {
        if (((m).mterm) > ((currentTerm)[self])) {
          currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
          state := [state EXCEPT ![self] = Follower];
          with (
            votedFor1 = Nil, 
            i = self, 
            j = (m).msource, 
            logOK = (((m).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m).mlastLogIndex) >= (Len((log)[i])))), 
            grant = ((((m).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ ((votedFor1) \in ({Nil, j}))
          ) {
            assert ((m).mterm) <= ((currentTerm)[i]);
            if (grant) {
              votedFor := j;
              either {
                with (value10 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
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
                with (value11 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
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
        } else {
          with (
            i = self, 
            j = (m).msource, 
            logOK = (((m).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m).mlastLogIndex) >= (Len((log)[i])))), 
            grant = ((((m).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ ((votedFor) \in ({Nil, j}))
          ) {
            assert ((m).mterm) <= ((currentTerm)[i]);
            if (grant) {
              votedFor := j;
              either {
                with (value12 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
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
                with (value13 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
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
        if (((m).mtype) = (RequestVoteResponse)) {
          if (((m).mterm) > ((currentTerm)[self])) {
            currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
            state := [state EXCEPT ![self] = Follower];
            votedFor := Nil;
            if (((m).mterm) < ((currentTerm)[self])) {
              goto serverLoop;
            } else {
              with (
                i = self, 
                j = (m).msource
              ) {
                assert ((m).mterm) = ((currentTerm)[i]);
                votesResponded := (votesResponded) \union ({j});
                if ((m).mvoteGranted) {
                  votesGranted := (votesGranted) \union ({j});
                  goto serverLoop;
                } else {
                  goto serverLoop;
                };
              };
            };
          } else {
            if (((m).mterm) < ((currentTerm)[self])) {
              goto serverLoop;
            } else {
              with (
                i = self, 
                j = (m).msource
              ) {
                assert ((m).mterm) = ((currentTerm)[i]);
                votesResponded := (votesResponded) \union ({j});
                if ((m).mvoteGranted) {
                  votesGranted := (votesGranted) \union ({j});
                  goto serverLoop;
                } else {
                  goto serverLoop;
                };
              };
            };
          };
        } else {
          if (((m).mtype) = (AppendEntriesRequest)) {
            if (((m).mterm) > ((currentTerm)[self])) {
              currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
              with (state1 = [state EXCEPT ![self] = Follower]) {
                votedFor := Nil;
                leader := (m).msource;
                with (
                  i = self, 
                  j = (m).msource, 
                  logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len((log)[i])))) /\ (((m).mprevLogTerm) = ((((log)[i])[(m).mprevLogIndex]).term)))
                ) {
                  assert ((m).mterm) <= ((currentTerm)[i]);
                  if ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Candidate))) {
                    state := [state1 EXCEPT ![i] = Follower];
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value20 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
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
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (index = ((m).mprevLogIndex) + (1)) {
                        if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log4 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))]) {
                            if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                              log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value30 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value31 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                            log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value32 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value33 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value21 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
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
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK);
                      with (index = ((m).mprevLogIndex) + (1)) {
                        if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log5 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))]) {
                            if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                              log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value34 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value35 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                            log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value36 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value37 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
              with (
                i = self, 
                j = (m).msource, 
                logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len((log)[i])))) /\ (((m).mprevLogTerm) = ((((log)[i])[(m).mprevLogIndex]).term)))
              ) {
                assert ((m).mterm) <= ((currentTerm)[i]);
                if ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))) {
                  state := [state EXCEPT ![i] = Follower];
                  if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                    either {
                      with (value22 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
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
                    assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                    with (index = ((m).mprevLogIndex) + (1)) {
                      if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log6 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))]) {
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                            log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value38 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value39 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                        if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                          log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                            either {
                              with (value310 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                            either {
                              with (value311 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                  if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                    either {
                      with (value23 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
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
                    assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                    with (index = ((m).mprevLogIndex) + (1)) {
                      if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log7 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))]) {
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                            log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value312 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value313 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                        if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                          log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                            either {
                              with (value314 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                            either {
                              with (value315 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
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
            if (((m).mtype) = (AppendEntriesResponse)) {
              if (((m).mterm) > ((currentTerm)[self])) {
                currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
                state := [state EXCEPT ![self] = Follower];
                votedFor := Nil;
                if (((m).mterm) < ((currentTerm)[self])) {
                  goto serverLoop;
                } else {
                  with (
                    i = self, 
                    j = (m).msource
                  ) {
                    assert ((m).mterm) = ((currentTerm)[i]);
                    if ((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![j] = (m).mmatchIndex];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                      goto serverLoop;
                    };
                  };
                };
              } else {
                if (((m).mterm) < ((currentTerm)[self])) {
                  goto serverLoop;
                } else {
                  with (
                    i = self, 
                    j = (m).msource
                  ) {
                    assert ((m).mterm) = ((currentTerm)[i]);
                    if ((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![j] = (m).mmatchIndex];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                      goto serverLoop;
                    };
                  };
                };
              };
            } else {
              if (((m).mtype) = (ClientPutRequest)) {
                if (((state)[self]) = (Leader)) {
                  with (entry = [term |-> (currentTerm)[self], key |-> (m).mkey, value |-> (m).mvalue]) {
                    log := [log EXCEPT ![self] = Append((log)[self], entry)];
                    in := TRUE;
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
      if ((idx) <= (NumServers)) {
        if ((idx) # (self)) {
          either {
            with (value40 = [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[self], mlastLogTerm |-> LastTerm((log)[self]), mlastLogIndex |-> Len((log)[self]), msource |-> self, mdest |-> idx]) {
              await ((network)[idx]).enabled;
              await (Len(((network)[idx]).queue)) < (BufferSize);
              with (network1 = [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value40), enabled |-> ((network)[idx]).enabled]]) {
                idx := (idx) + (1);
                if (ExploreFail) {
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
              if (ExploreFail) {
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
          if (ExploreFail) {
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
    failLabel:
      with (value60 = TRUE) {
        fd := [fd EXCEPT ![self] = value60];
        goto Done;
      };
  }
  
  fair process (sender \in ServerSenderSet)
    variables idx0; sid = (sm)[self];
  {
    serverSenderLoop:
      if (in) {
        await ((state)[sid]) = (Leader);
        idx0 := 1;
        if (ExploreFail) {
          with (yielded_network1 = ((network)[sid]).enabled) {
            if (~ (yielded_network1)) {
              goto Done;
            } else {
              goto appendEntriesLoop;
            };
          };
        } else {
          goto appendEntriesLoop;
        };
      } else {
        goto Done;
      };
    appendEntriesLoop:
      with (yielded_network2 = ((network)[sid]).enabled) {
        if (((yielded_network2) /\ (((state)[sid]) = (Leader))) /\ ((idx0) <= (NumServers))) {
          if ((idx0) # (sid)) {
            with (
              prevLogIndex1 = (((nextIndex)[sid])[idx0]) - (1), 
              prevLogTerm1 = IF (prevLogIndex1) > (0) THEN (((log)[sid])[prevLogIndex1]).term ELSE 0, 
              lastEntry1 = Min({Len((log)[sid]), ((nextIndex)[sid])[idx0]}), 
              entries1 = SubSeq((log)[sid], ((nextIndex)[sid])[idx0], lastEntry1)
            ) {
              either {
                with (value70 = [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[sid], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[sid], lastEntry1}), msource |-> sid, mdest |-> idx0]) {
                  await ((network)[idx0]).enabled;
                  await (Len(((network)[idx0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![idx0] = [queue |-> Append(((network)[idx0]).queue, value70), enabled |-> ((network)[idx0]).enabled]];
                  idx0 := (idx0) + (1);
                  goto appendEntriesLoop;
                };
              } or {
                with (yielded_fd40 = (fd)[idx0]) {
                  await yielded_fd40;
                  idx0 := (idx0) + (1);
                  goto appendEntriesLoop;
                };
              };
            };
          } else {
            idx0 := (idx0) + (1);
            goto appendEntriesLoop;
          };
        } else {
          goto serverSenderLoop;
        };
      };
  }
  
  fair process (client \in ClientSet)
  {
    sndPutReq:
      with (
        srv = 1, 
        value80 = [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv]
      ) {
        await ((network)[srv]).enabled;
        await (Len(((network)[srv]).queue)) < (BufferSize);
        network := [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value80), enabled |-> ((network)[srv]).enabled]];
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "8e45e3ed" /\ chksum(tla) = "aa056fa5") PCal-18049938ece8066a38eb5044080cf45c
CONSTANT defaultInitValue
VARIABLES network, fd, sm, state, nextIndex, log, currentTerm, commitIndex, 
          timer, in, pc

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
ServerSenderSet == ((NumServers) + (1)) .. ((NumServers) + (NumServers))
ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
isQuorum(s) == ((Cardinality(s)) * (2)) > (NumServers)

VARIABLES votedFor, matchIndex, votesResponded, votesGranted, leader, idx, m, 
          idx0, sid

vars == << network, fd, sm, state, nextIndex, log, currentTerm, commitIndex, 
           timer, in, pc, votedFor, matchIndex, votesResponded, votesGranted, 
           leader, idx, m, idx0, sid >>

ProcSet == (ServerSet) \cup (ServerSenderSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [i \in ServerSet |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [i \in ServerSet |-> FALSE]
        /\ sm = [i \in ServerSenderSet |-> (i) - (NumServers)]
        /\ state = [i \in ServerSet |-> Follower]
        /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
        /\ log = [i \in ServerSet |-> <<>>]
        /\ currentTerm = [i \in ServerSet |-> 1]
        /\ commitIndex = [i \in ServerSet |-> 0]
        /\ timer = TRUE
        /\ in = TRUE
        (* Process server *)
        /\ votedFor = [self \in ServerSet |-> Nil]
        /\ matchIndex = [self \in ServerSet |-> [t \in ServerSet |-> 0]]
        /\ votesResponded = [self \in ServerSet |-> {}]
        /\ votesGranted = [self \in ServerSet |-> {}]
        /\ leader = [self \in ServerSet |-> Nil]
        /\ idx = [self \in ServerSet |-> 1]
        /\ m = [self \in ServerSet |-> defaultInitValue]
        (* Process sender *)
        /\ idx0 = [self \in ServerSenderSet |-> defaultInitValue]
        /\ sid = [self \in ServerSenderSet |-> (sm)[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ServerSenderSet -> "serverSenderLoop"
                                        [] self \in ClientSet -> "sndPutReq"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 559, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          LET network0 == [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]] IN
                                            LET yielded_network3 == readMsg00 IN
                                              /\ m' = [m EXCEPT ![self] = yielded_network3]
                                              /\ Assert(((m'[self]).mdest) = (self), 
                                                        "Failure of assertion at line 567, column 13.")
                                              /\ IF ExploreFail
                                                    THEN /\ \/ /\ TRUE
                                                               /\ network' = network0
                                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                                            \/ /\ LET value00 == FALSE IN
                                                                    /\ network' = [network0 EXCEPT ![self] = [queue |-> ((network0)[self]).queue, enabled |-> value00]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                    ELSE /\ network' = network0
                                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED <<state, nextIndex, currentTerm, commitIndex, in, votedFor, matchIndex, votesResponded, votesGranted, idx>>
                                  \/ /\ ((state)[self]) \in ({Follower, Candidate})
                                     /\ LET yielded_network00 == Len(((network)[self]).queue) IN
                                          LET yielded_fd5 == (fd)[leader[self]] IN
                                            /\ (((yielded_network00) = (0)) /\ (timer)) /\ (((leader[self]) = (Nil)) \/ (((leader[self]) # (Nil)) /\ (yielded_fd5)))
                                            /\ LET i1 == self IN
                                                 /\ state' = [state EXCEPT ![i1] = Candidate]
                                                 /\ currentTerm' = [currentTerm EXCEPT ![i1] = ((currentTerm)[i1]) + (1)]
                                                 /\ votedFor' = [votedFor EXCEPT ![self] = i1]
                                                 /\ votesResponded' = [votesResponded EXCEPT ![self] = {i1}]
                                                 /\ votesGranted' = [votesGranted EXCEPT ![self] = {i1}]
                                                 /\ idx' = [idx EXCEPT ![self] = 1]
                                                 /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                     /\ UNCHANGED <<network, nextIndex, commitIndex, in, matchIndex, m>>
                                  \/ /\ ((state)[self]) = (Leader)
                                     /\ LET i == self IN
                                          LET agreeIndexes == {index \in (1) .. (Len((log)[i])) : isQuorum(({i}) \union ({k \in ServerSet : ((matchIndex[self])[k]) >= (index)}))} IN
                                            LET newCommitIndex == IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i] IN
                                              /\ Assert((newCommitIndex) >= ((commitIndex)[i]), 
                                                        "Failure of assertion at line 608, column 13.")
                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                     /\ UNCHANGED <<network, state, nextIndex, currentTerm, in, votedFor, matchIndex, votesResponded, votesGranted, idx, m>>
                                  \/ /\ (((state)[self]) = (Candidate)) /\ (isQuorum(votesGranted[self]))
                                     /\ LET i == self IN
                                          /\ state' = [state EXCEPT ![i] = Leader]
                                          /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]]
                                          /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                          /\ in' = TRUE
                                          /\ IF Debug
                                                THEN /\ PrintT(<<"BecomeLeader", i, (currentTerm)[i]>>)
                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                     /\ UNCHANGED <<network, currentTerm, commitIndex, votedFor, votesResponded, votesGranted, idx, m>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                               /\ UNCHANGED << network, state, nextIndex, 
                                               currentTerm, commitIndex, in, 
                                               votedFor, matchIndex, 
                                               votesResponded, votesGranted, 
                                               idx, m >>
                    /\ UNCHANGED << fd, sm, log, timer, leader, idx0, sid >>

handleMsg(self) == /\ pc[self] = "handleMsg"
                   /\ IF ((m[self]).mtype) = (RequestVoteRequest)
                         THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                    THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                         /\ state' = [state EXCEPT ![self] = Follower]
                                         /\ LET votedFor1 == Nil IN
                                              LET i == self IN
                                                LET j == (m[self]).msource IN
                                                  LET logOK == (((m[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                    LET grant == ((((m[self]).mterm) = ((currentTerm')[i])) /\ (logOK)) /\ ((votedFor1) \in ({Nil, j})) IN
                                                      /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                "Failure of assertion at line 642, column 13.")
                                                      /\ IF grant
                                                            THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                                 /\ \/ /\ LET value10 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                            /\ ((network)[j]).enabled
                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                    \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                            /\ yielded_fd00
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ \/ /\ LET value11 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
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
                                                LET logOK == (((m[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                  LET grant == ((((m[self]).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ ((votedFor[self]) \in ({Nil, j})) IN
                                                    /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                              "Failure of assertion at line 683, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                               /\ \/ /\ LET value12 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                          /\ yielded_fd02
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                          ELSE /\ \/ /\ LET value13 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                          /\ yielded_fd03
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << state, currentTerm >>
                              /\ UNCHANGED << nextIndex, log, commitIndex, in, 
                                              matchIndex, votesResponded, 
                                              votesGranted, leader >>
                         ELSE /\ IF ((m[self]).mtype) = (RequestVoteResponse)
                                    THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                    /\ state' = [state EXCEPT ![self] = Follower]
                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                    /\ IF ((m[self]).mterm) < ((currentTerm')[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                "Failure of assertion at line 729, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j})]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED votesGranted
                                               ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                "Failure of assertion at line 747, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j})]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED votesGranted
                                                    /\ UNCHANGED << state, 
                                                                    currentTerm, 
                                                                    votedFor >>
                                         /\ UNCHANGED << network, nextIndex, 
                                                         log, commitIndex, in, 
                                                         matchIndex, leader >>
                                    ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                               /\ LET state1 == [state EXCEPT ![self] = Follower] IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                    /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                                    /\ LET i == self IN
                                                                         LET j == (m[self]).msource IN
                                                                           LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                             /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                                       "Failure of assertion at line 770, column 19.")
                                                                             /\ IF (((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                   THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                        /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ \/ /\ LET value20 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
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
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 788, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log4 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value30 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value31 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value31), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ log' = log4
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd21 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd21
                                                                                                                                                   /\ log' = log4
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ log' = log4
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value32 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value33 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                   ELSE /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ \/ /\ LET value21 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                              /\ ((network)[j]).enabled
                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]]
                                                                                                              /\ state' = state1
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                      \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                              /\ yielded_fd11
                                                                                                              /\ state' = state1
                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                         /\ UNCHANGED network
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 898, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log5 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value34 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value34), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ state' = state1
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd24 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd24
                                                                                                                                                   /\ state' = state1
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                        /\ \/ /\ LET value35 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value35), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                   /\ log' = log5
                                                                                                                                                   /\ state' = state1
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           \/ /\ LET yielded_fd25 == (fd)[j] IN
                                                                                                                                                   /\ yielded_fd25
                                                                                                                                                   /\ log' = log5
                                                                                                                                                   /\ state' = state1
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED network
                                                                                                                                   ELSE /\ log' = log5
                                                                                                                                        /\ state' = state1
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value36 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value36), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ state' = state1
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd26 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd26
                                                                                                                                                 /\ state' = state1
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ state' = state1
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value37 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value37), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ state' = state1
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd27 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd27
                                                                                                                                                 /\ state' = state1
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                                 ELSE /\ state' = state1
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                                                  "Failure of assertion at line 1012, column 17.")
                                                                        /\ IF (((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value22 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
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
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 1030, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value38 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value39 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value39), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ log' = log6
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd29 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd29
                                                                                                                                              /\ log' = log6
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ log' = log6
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value310 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value311 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                              ELSE /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value23 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
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
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 1138, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value312 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                   /\ \/ /\ LET value313 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value313), enabled |-> ((network)[j]).enabled]]
                                                                                                                                              /\ log' = log7
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      \/ /\ LET yielded_fd213 == (fd)[j] IN
                                                                                                                                              /\ yielded_fd213
                                                                                                                                              /\ log' = log7
                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         /\ UNCHANGED network
                                                                                                                              ELSE /\ log' = log7
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value314 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                 /\ \/ /\ LET value315 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
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
                                                                    in, 
                                                                    matchIndex >>
                                               ELSE /\ IF ((m[self]).mtype) = (AppendEntriesResponse)
                                                          THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                                     THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                                          /\ state' = [state EXCEPT ![self] = Follower]
                                                                          /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                          /\ IF ((m[self]).mterm) < ((currentTerm')[self])
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                                      "Failure of assertion at line 1246, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                     ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                                      "Failure of assertion at line 1265, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                          /\ UNCHANGED << state, 
                                                                                          currentTerm, 
                                                                                          votedFor >>
                                                               /\ UNCHANGED << log, 
                                                                               in >>
                                                          ELSE /\ IF ((m[self]).mtype) = (ClientPutRequest)
                                                                     THEN /\ IF ((state)[self]) = (Leader)
                                                                                THEN /\ LET entry == [term |-> (currentTerm)[self], key |-> (m[self]).mkey, value |-> (m[self]).mvalue] IN
                                                                                          /\ log' = [log EXCEPT ![self] = Append((log)[self], entry)]
                                                                                          /\ in' = TRUE
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << log, 
                                                                                                     in >>
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED << log, 
                                                                                          in >>
                                                               /\ UNCHANGED << state, 
                                                                               nextIndex, 
                                                                               currentTerm, 
                                                                               votedFor, 
                                                                               matchIndex >>
                                                    /\ UNCHANGED << network, 
                                                                    commitIndex, 
                                                                    leader >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted >>
                   /\ UNCHANGED << fd, sm, timer, idx, m, idx0, sid >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx[self]) <= (NumServers)
                               THEN /\ IF (idx[self]) # (self)
                                          THEN /\ \/ /\ LET value40 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[self], mlastLogTerm |-> LastTerm((log)[self]), mlastLogIndex |-> Len((log)[self]), msource |-> self, mdest |-> idx[self]] IN
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
                         /\ UNCHANGED << fd, sm, state, nextIndex, log, 
                                         currentTerm, commitIndex, timer, in, 
                                         votedFor, matchIndex, votesResponded, 
                                         votesGranted, leader, m, idx0, sid >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value60 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value60]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, sm, state, nextIndex, log, 
                                   currentTerm, commitIndex, timer, in, 
                                   votedFor, matchIndex, votesResponded, 
                                   votesGranted, leader, idx, m, idx0, sid >>

server(self) == serverLoop(self) \/ handleMsg(self)
                   \/ requestVoteLoop(self) \/ failLabel(self)

serverSenderLoop(self) == /\ pc[self] = "serverSenderLoop"
                          /\ IF in
                                THEN /\ ((state)[sid[self]]) = (Leader)
                                     /\ idx0' = [idx0 EXCEPT ![self] = 1]
                                     /\ IF ExploreFail
                                           THEN /\ LET yielded_network1 == ((network)[sid[self]]).enabled IN
                                                     IF ~ (yielded_network1)
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ idx0' = idx0
                          /\ UNCHANGED << network, fd, sm, state, nextIndex, 
                                          log, currentTerm, commitIndex, timer, 
                                          in, votedFor, matchIndex, 
                                          votesResponded, votesGranted, leader, 
                                          idx, m, sid >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ LET yielded_network2 == ((network)[sid[self]]).enabled IN
                                IF ((yielded_network2) /\ (((state)[sid[self]]) = (Leader))) /\ ((idx0[self]) <= (NumServers))
                                   THEN /\ IF (idx0[self]) # (sid[self])
                                              THEN /\ LET prevLogIndex1 == (((nextIndex)[sid[self]])[idx0[self]]) - (1) IN
                                                        LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN (((log)[sid[self]])[prevLogIndex1]).term ELSE 0 IN
                                                          LET lastEntry1 == Min({Len((log)[sid[self]]), ((nextIndex)[sid[self]])[idx0[self]]}) IN
                                                            LET entries1 == SubSeq((log)[sid[self]], ((nextIndex)[sid[self]])[idx0[self]], lastEntry1) IN
                                                              \/ /\ LET value70 == [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[sid[self]], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[sid[self]], lastEntry1}), msource |-> sid[self], mdest |-> idx0[self]] IN
                                                                      /\ ((network)[idx0[self]]).enabled
                                                                      /\ (Len(((network)[idx0[self]]).queue)) < (BufferSize)
                                                                      /\ network' = [network EXCEPT ![idx0[self]] = [queue |-> Append(((network)[idx0[self]]).queue, value70), enabled |-> ((network)[idx0[self]]).enabled]]
                                                                      /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                                      /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                              \/ /\ LET yielded_fd40 == (fd)[idx0[self]] IN
                                                                      /\ yielded_fd40
                                                                      /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                                      /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                 /\ UNCHANGED network
                                              ELSE /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                   /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                   /\ UNCHANGED network
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverSenderLoop"]
                                        /\ UNCHANGED << network, idx0 >>
                           /\ UNCHANGED << fd, sm, state, nextIndex, log, 
                                           currentTerm, commitIndex, timer, in, 
                                           votedFor, matchIndex, 
                                           votesResponded, votesGranted, 
                                           leader, idx, m, sid >>

sender(self) == serverSenderLoop(self) \/ appendEntriesLoop(self)

sndPutReq(self) == /\ pc[self] = "sndPutReq"
                   /\ LET srv == 1 IN
                        LET value80 == [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv] IN
                          /\ ((network)[srv]).enabled
                          /\ (Len(((network)[srv]).queue)) < (BufferSize)
                          /\ network' = [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value80), enabled |-> ((network)[srv]).enabled]]
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << fd, sm, state, nextIndex, log, currentTerm, 
                                   commitIndex, timer, in, votedFor, 
                                   matchIndex, votesResponded, votesGranted, 
                                   leader, idx, m, idx0, sid >>

client(self) == sndPutReq(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: server(self))
           \/ (\E self \in ServerSenderSet: sender(self))
           \/ (\E self \in ClientSet: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(server(self))
        /\ \A self \in ServerSenderSet : WF_vars(sender(self))
        /\ \A self \in ClientSet : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION  TLA-f157040c4fee3bde8856de68970be59d

\* Constraints

LimitTerm == \A i \in ServerSet: currentTerm[i] <= MaxTerm
LimitCommitIndex == \A i \in ServerSet: commitIndex[i] <= MaxCommitIndex

LimitNodeFailure == Cardinality({i \in ServerSet: \lnot network[i].enabled}) <= MaxNodeFail

\* Invariants

ElectionSafety == \lnot (\E i, j \in ServerSet:
                                        /\ i /= j
                                        /\ currentTerm[i] = currentTerm[j]
                                        /\ state[i] = Leader
                                        /\ state[j] = Leader)

LogMatching == \A i, j \in ServerSet:
                        \A k \in 1..Min({Len(log[i]), Len(log[j])}):
                            log[i][k].term = log[j][k].term
                                => SubSeq(log[i], 1, k) = SubSeq(log[j], 1, k)

LeaderCompleteness == \A i \in ServerSet:
                        \A logIdx \in DOMAIN log[i]:
                          logIdx <= commitIndex[i] =>
                            \A j \in ServerSet:
                              state[j] = Leader /\ currentTerm[j] >= log[i][logIdx].term =>
                                /\ logIdx \in DOMAIN log[j]
                                /\ log[i][logIdx] = log[j][logIdx]

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
