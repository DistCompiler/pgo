-------------------------------- MODULE raft --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumServers

CONSTANT MaxTerm
CONSTANT MaxCommitIndex

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

        Min(s) == CHOOSE x \in s : \A y \in s : x <= y
        Max(s) == CHOOSE x \in s : \A y \in s : x >= y

        LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

        Nil == 0

        ServerSet == 1..NumServers

        isQuorum(s) == Cardinality(s) * 2 > NumServers
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

    archetype AServer(ref net[_], ref fd[_], ref netLen[_])
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
            either {
                m := net[self];

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
                        net[j] := [
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm,
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j
                        ];
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

                        \* BecomeLeader
                        if (
                            /\ state = Candidate
                            /\ isQuorum(votesGranted)
                        ) {
                            state      := Leader;
                            nextIndex  := [j \in ServerSet |-> Len(log) + 1]; 
                            matchIndex := [j \in ServerSet |-> 0];
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
                            net[j] := [
                                mtype       |-> AppendEntriesResponse,
                                mterm       |-> currentTerm,
                                msuccess    |-> FALSE,
                                mmatchIndex |-> 0,
                                msource     |-> i,
                                mdest       |-> j
                            ];
                        } 
                        \* accept request
                        else {
                            assert (
                                /\ m.mterm = currentTerm
                                /\ state = Follower
                                /\ logOK
                            );
                            with (index = m.prevLogIndex + 1) {
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
                                    /\ Len(log) = m.prevLogIndex
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
                                    net[j] := [
                                        mtype       |-> AppendEntriesResponse,
                                        mterm       |-> currentTerm,
                                        msuccess    |-> TRUE,
                                        mmatchIndex |-> m.prevLogIndex + Len(m.mentries),
                                        msource     |-> i,
                                        mdest       |-> j
                                    ];
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
                                nextIndex[j]  := Max({nextIndex[i][j]-1, 1});
                            };
                        };
                    };
                };
            } or {
                \* Server times out and starts a new election.
                if (state \in {Follower, Candidate}) {
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
                    idx            := 1;

                requestVoteLoop:
                    while (idx <= NumServers) {
                        \* RequestVote
                        if (idx /= self) {
                            net[idx] := [
                                mtype         |-> RequestVoteRequest,
                                mterm         |-> currentTerm,
                                mlastLogTerm  |-> LastTerm(log),
                                mlastLogIndex |-> Len(log),
                                msource       |-> self,
                                mdest         |-> idx
                            ];
                        };
                        idx := idx + 1;
                    };
                };
            } or {
                if (state = Leader) {
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
                        commitIndex := newCommitIndex;
                    };

                    \* AppendEntries
                    idx := 1;
                appendEntriesLoop:
                    while (idx <= NumServers) {
                        if (idx /= self) {
                            with (
                                prevLogIndex = nextIndex[idx],
                                prevLogTerm  = IF prevLogIndex > 0
                                               THEN log[prevLogIndex].term
                                               ELSE 0,
                                lastEntry =    Min({Len(log), nextIndex[idx]}),
                                entries =      SubSeq(log, nextIndex[idx], lastEntry)
                            ) {
                                if (Len(entries) > 0) {
                                    net[idx] := [
                                        mtype         |-> AppendEntriesRequest,
                                        mterm         |-> currentTerm,
                                        mprevLogIndex |-> prevLogIndex,
                                        mprevLogTerm  |-> prevLogTerm,
                                        mentries      |-> entries,
                                        mcommitIndex  |-> Min({commitIndex, lastEntry}),
                                        msource       |-> self,
                                        mdest         |-> idx
                                    ];
                                };
                            };
                        };
                    };
                };
            } or {
                \* ClientRequest
                if (state = Leader) {
                    with (entry = [term  |-> currentTerm, 
                                   value |-> 1]
                    ) {
                        log := Append(log, entry);
                    };
                };
            };
        };
    }

    variables
        network = [i \in ServerSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd = [i \in ServerSet |-> FALSE];

    fair process (server \in ServerSet) == instance AServer(ref network[_], ref fd[_], ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkBufferLength;
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
    Min(s) == CHOOSE x \in s : \A y \in s : (x) <= (y)
    Max(s) == CHOOSE x \in s : \A y \in s : (x) >= (y)
    LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
    Nil == 0
    ServerSet == (1) .. (NumServers)
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
            network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
            with (yielded_network1 = readMsg00) {
              m := yielded_network1;
              goto handleMsg;
            };
          };
        } or {
          if((state) \in ({Follower, Candidate})) {
            with (yielded_network00 = Len(((network)[self]).queue)) {
              with (yielded_fd0 = (fd)[leader]) {
                await ((yielded_network00) = (0)) /\ (((leader) = (Nil)) \/ (((leader) # (Nil)) /\ (yielded_fd0)));
                state := Candidate;
                currentTerm := (currentTerm) + (1);
                votedFor := self;
                votesResponded := {self};
                votesGranted := {self};
                idx := 1;
                goto requestVoteLoop;
              };
            };
          } else {
            goto serverLoop;
          };
        } or {
          if((state) = (Leader)) {
            with (agreeIndexes1 = {index \in (1) .. (Len(log)) : isQuorum(({self}) \union ({k \in ServerSet : ((matchIndex)[k]) >= (index)}))}, newCommitIndex1 = IF ((agreeIndexes1) # ({})) /\ ((((log)[Max(agreeIndexes1)]).term) = (currentTerm)) THEN Max(agreeIndexes1) ELSE commitIndex) {
              commitIndex := newCommitIndex1;
              idx := 1;
              goto appendEntriesLoop;
            };
          } else {
            goto serverLoop;
          };
        } or {
          if((state) = (Leader)) {
            with (entry = [term |-> currentTerm, value |-> 1]) {
              log := Append(log, entry);
              goto serverLoop;
            };
          } else {
            goto serverLoop;
          };
        };
      } else {
        goto Done;
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
                with (value00 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]];
                  goto serverLoop;
                };
              } else {
                with (value01 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value01), enabled |-> ((network)[j]).enabled]];
                  votedFor := votedFor1;
                  goto serverLoop;
                };
              };
            };
          };
        } else {
          with (i = self, j = (m).msource, logOK = (((m).mlastLogTerm) > (LastTerm(log))) \/ ((((m).mlastLogTerm) = (LastTerm(log))) /\ (((m).mlastLogIndex) >= (Len(log)))), grant = ((((m).mterm) = (currentTerm)) /\ (logOK)) /\ ((votedFor) \in ({Nil, j}))) {
            assert ((m).mterm) <= (currentTerm);
            if(grant) {
              votedFor := j;
              with (value02 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                await ((network)[j]).enabled;
                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]];
                goto serverLoop;
              };
            } else {
              with (value03 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                await ((network)[j]).enabled;
                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value03), enabled |-> ((network)[j]).enabled]];
                goto serverLoop;
              };
            };
          };
        };
      } else {
        if(((m).mtype) = (RequestVoteResponse)) {
          if(((m).mterm) > (currentTerm)) {
            currentTerm := (m).mterm;
            with (state2 = Follower) {
              votedFor := Nil;
              if(((m).mterm) < (currentTerm)) {
                state := state2;
                goto serverLoop;
              } else {
                with (i2 = self, j2 = (m).msource) {
                  assert ((m).mterm) = (currentTerm);
                  votesResponded := (votesResponded) \union ({j2});
                  if((m).mvoteGranted) {
                    votesGranted := (votesGranted) \union ({j2});
                    if(((state2) = (Candidate)) /\ (isQuorum(votesGranted))) {
                      state := Leader;
                      nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
                      matchIndex := [j \in ServerSet |-> 0];
                      goto serverLoop;
                    } else {
                      state := state2;
                      goto serverLoop;
                    };
                  } else {
                    if(((state2) = (Candidate)) /\ (isQuorum(votesGranted))) {
                      state := Leader;
                      nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
                      matchIndex := [j \in ServerSet |-> 0];
                      goto serverLoop;
                    } else {
                      state := state2;
                      goto serverLoop;
                    };
                  };
                };
              };
            };
          } else {
            if(((m).mterm) < (currentTerm)) {
              goto serverLoop;
            } else {
              with (i3 = self, j3 = (m).msource) {
                assert ((m).mterm) = (currentTerm);
                votesResponded := (votesResponded) \union ({j3});
                if((m).mvoteGranted) {
                  votesGranted := (votesGranted) \union ({j3});
                  if(((state) = (Candidate)) /\ (isQuorum(votesGranted))) {
                    state := Leader;
                    nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
                    matchIndex := [j \in ServerSet |-> 0];
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                } else {
                  if(((state) = (Candidate)) /\ (isQuorum(votesGranted))) {
                    state := Leader;
                    nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
                    matchIndex := [j \in ServerSet |-> 0];
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              };
            };
          };
        } else {
          if(((m).mtype) = (AppendEntriesRequest)) {
            if(((m).mterm) > (currentTerm)) {
              currentTerm := (m).mterm;
              with (state3 = Follower) {
                votedFor := Nil;
                leader := (m).msource;
                with (i = self, j = (m).msource, logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len(log)))) /\ (((m).mprevLogTerm) = (((log)[(m).mprevLogIndex]).term)))) {
                  assert ((m).mterm) <= (currentTerm);
                  if((((m).mterm) = (currentTerm)) /\ ((state3) = (Candidate))) {
                    state := Follower;
                    if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (~ (logOK)))) {
                      with (value10 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]];
                        goto serverLoop;
                      };
                    } else {
                      assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                      with (index = ((m).prevLogIndex) + (1)) {
                        if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log4 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                            if((((m).mentries) # (<<>>)) /\ ((Len(log4)) = ((m).prevLogIndex))) {
                              log := Append(log4, ((m).mentries)[1]);
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value20 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value21 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]];
                                  log := log4;
                                  goto serverLoop;
                                };
                              } else {
                                log := log4;
                                goto serverLoop;
                              };
                            };
                          };
                        } else {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).prevLogIndex))) {
                            log := Append(log, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value22 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value23 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          };
                        };
                      };
                    };
                  } else {
                    if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state3) = (Follower))) /\ (~ (logOK)))) {
                      with (value11 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]];
                        state := state3;
                        goto serverLoop;
                      };
                    } else {
                      assert ((((m).mterm) = (currentTerm)) /\ ((state3) = (Follower))) /\ (logOK);
                      with (index = ((m).prevLogIndex) + (1)) {
                        if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                          with (log5 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                            if((((m).mentries) # (<<>>)) /\ ((Len(log5)) = ((m).prevLogIndex))) {
                              log := Append(log5, ((m).mentries)[1]);
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value24 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value24), enabled |-> ((network)[j]).enabled]];
                                  state := state3;
                                  goto serverLoop;
                                };
                              } else {
                                state := state3;
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value25 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value25), enabled |-> ((network)[j]).enabled]];
                                  log := log5;
                                  state := state3;
                                  goto serverLoop;
                                };
                              } else {
                                log := log5;
                                state := state3;
                                goto serverLoop;
                              };
                            };
                          };
                        } else {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).prevLogIndex))) {
                            log := Append(log, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value26 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value26), enabled |-> ((network)[j]).enabled]];
                                state := state3;
                                goto serverLoop;
                              };
                            } else {
                              state := state3;
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value27 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value27), enabled |-> ((network)[j]).enabled]];
                                state := state3;
                                goto serverLoop;
                              };
                            } else {
                              state := state3;
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
                    with (value12 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                      await ((network)[j]).enabled;
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]];
                      goto serverLoop;
                    };
                  } else {
                    assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                    with (index = ((m).prevLogIndex) + (1)) {
                      if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log6 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log6)) = ((m).prevLogIndex))) {
                            log := Append(log6, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value28 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value28), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value29 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value29), enabled |-> ((network)[j]).enabled]];
                                log := log6;
                                goto serverLoop;
                              };
                            } else {
                              log := log6;
                              goto serverLoop;
                            };
                          };
                        };
                      } else {
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).prevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value210 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value210), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value211 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value211), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
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
                    with (value13 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                      await ((network)[j]).enabled;
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]];
                      goto serverLoop;
                    };
                  } else {
                    assert ((((m).mterm) = (currentTerm)) /\ ((state) = (Follower))) /\ (logOK);
                    with (index = ((m).prevLogIndex) + (1)) {
                      if(((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) # ((((m).mentries)[1]).term))) {
                        with (log7 = [k \in (1) .. ((Len(log)) - (1)) |-> (log)[k]]) {
                          if((((m).mentries) # (<<>>)) /\ ((Len(log7)) = ((m).prevLogIndex))) {
                            log := Append(log7, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value212 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value212), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value213 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value213), enabled |-> ((network)[j]).enabled]];
                                log := log7;
                                goto serverLoop;
                              };
                            } else {
                              log := log7;
                              goto serverLoop;
                            };
                          };
                        };
                      } else {
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).prevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value214 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value214), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value215 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).prevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value215), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
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
                      nextIndex := [nextIndex EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})];
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
                      nextIndex := [nextIndex EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})];
                      goto serverLoop;
                    };
                  };
                };
              };
            } else {
              goto serverLoop;
            };
          };
        };
      };
    requestVoteLoop:
      if((idx) <= (NumServers)) {
        if((idx) # (self)) {
          with (value30 = [mtype |-> RequestVoteRequest, mterm |-> currentTerm, mlastLogTerm |-> LastTerm(log), mlastLogIndex |-> Len(log), msource |-> self, mdest |-> idx]) {
            await ((network)[idx]).enabled;
            network := [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value30), enabled |-> ((network)[idx]).enabled]];
            idx := (idx) + (1);
            goto requestVoteLoop;
          };
        } else {
          idx := (idx) + (1);
          goto requestVoteLoop;
        };
      } else {
        goto serverLoop;
      };
    appendEntriesLoop:
      if((idx) <= (NumServers)) {
        if((idx) # (self)) {
          with (prevLogIndex = (nextIndex)[idx], prevLogTerm = IF (prevLogIndex) > (0) THEN ((log)[prevLogIndex]).term ELSE 0, lastEntry = Min({Len(log), (nextIndex)[idx]}), entries = SubSeq(log, (nextIndex)[idx], lastEntry)) {
            if((Len(entries)) > (0)) {
              with (value40 = [mtype |-> AppendEntriesRequest, mterm |-> currentTerm, mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries, mcommitIndex |-> Min({commitIndex, lastEntry}), msource |-> self, mdest |-> idx]) {
                await ((network)[idx]).enabled;
                network := [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value40), enabled |-> ((network)[idx]).enabled]];
                goto appendEntriesLoop;
              };
            } else {
              goto appendEntriesLoop;
            };
          };
        } else {
          goto appendEntriesLoop;
        };
      } else {
        goto serverLoop;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "6d53a0cd" /\ chksum(tla) = "c8beee85")
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
Min(s) == CHOOSE x \in s : \A y \in s : (x) <= (y)
Max(s) == CHOOSE x \in s : \A y \in s : (x) >= (y)
LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
Nil == 0
ServerSet == (1) .. (NumServers)
isQuorum(s) == ((Cardinality(s)) * (2)) > (NumServers)

VARIABLES currentTerm, state, votedFor, log, commitIndex, nextIndex, 
          matchIndex, votesResponded, votesGranted, leader, idx, m

vars == << network, fd, pc, currentTerm, state, votedFor, log, commitIndex, 
           nextIndex, matchIndex, votesResponded, votesGranted, leader, idx, 
           m >>

ProcSet == (ServerSet)

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
        /\ pc = [self \in ProcSet |-> "serverLoop"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 397, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                          /\ LET yielded_network1 == readMsg00 IN
                                               /\ m' = [m EXCEPT ![self] = yielded_network1]
                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, votesResponded, votesGranted, idx>>
                                  \/ /\ IF (state[self]) \in ({Follower, Candidate})
                                           THEN /\ LET yielded_network00 == Len(((network)[self]).queue) IN
                                                     LET yielded_fd0 == (fd)[leader[self]] IN
                                                       /\ ((yielded_network00) = (0)) /\ (((leader[self]) = (Nil)) \/ (((leader[self]) # (Nil)) /\ (yielded_fd0)))
                                                       /\ state' = [state EXCEPT ![self] = Candidate]
                                                       /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                                                       /\ votedFor' = [votedFor EXCEPT ![self] = self]
                                                       /\ votesResponded' = [votesResponded EXCEPT ![self] = {self}]
                                                       /\ votesGranted' = [votesGranted EXCEPT ![self] = {self}]
                                                       /\ idx' = [idx EXCEPT ![self] = 1]
                                                       /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                /\ UNCHANGED << currentTerm, 
                                                                state, 
                                                                votedFor, 
                                                                votesResponded, 
                                                                votesGranted, 
                                                                idx >>
                                     /\ UNCHANGED <<network, log, commitIndex, m>>
                                  \/ /\ IF (state[self]) = (Leader)
                                           THEN /\ LET agreeIndexes1 == {index \in (1) .. (Len(log[self])) : isQuorum(({self}) \union ({k \in ServerSet : ((matchIndex[self])[k]) >= (index)}))} IN
                                                     LET newCommitIndex1 == IF ((agreeIndexes1) # ({})) /\ ((((log[self])[Max(agreeIndexes1)]).term) = (currentTerm[self])) THEN Max(agreeIndexes1) ELSE commitIndex[self] IN
                                                       /\ commitIndex' = [commitIndex EXCEPT ![self] = newCommitIndex1]
                                                       /\ idx' = [idx EXCEPT ![self] = 1]
                                                       /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                /\ UNCHANGED << commitIndex, 
                                                                idx >>
                                     /\ UNCHANGED <<network, currentTerm, state, votedFor, log, votesResponded, votesGranted, m>>
                                  \/ /\ IF (state[self]) = (Leader)
                                           THEN /\ LET entry == [term |-> currentTerm[self], value |-> 1] IN
                                                     /\ log' = [log EXCEPT ![self] = Append(log[self], entry)]
                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                /\ log' = log
                                     /\ UNCHANGED <<network, currentTerm, state, votedFor, commitIndex, votesResponded, votesGranted, idx, m>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, currentTerm, state, 
                                               votedFor, log, commitIndex, 
                                               votesResponded, votesGranted, 
                                               idx, m >>
                    /\ UNCHANGED << fd, nextIndex, matchIndex, leader >>

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
                                                                "Failure of assertion at line 453, column 15.")
                                                      /\ IF grant
                                                            THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                                 /\ LET value00 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                      /\ ((network)[j]).enabled
                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]]
                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                            ELSE /\ LET value01 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                      /\ ((network)[j]).enabled
                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value01), enabled |-> ((network)[j]).enabled]]
                                                                      /\ votedFor' = [votedFor EXCEPT ![self] = votedFor1]
                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                    ELSE /\ LET i == self IN
                                              LET j == (m[self]).msource IN
                                                LET logOK == (((m[self]).mlastLogTerm) > (LastTerm(log[self]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm(log[self]))) /\ (((m[self]).mlastLogIndex) >= (Len(log[self])))) IN
                                                  LET grant == ((((m[self]).mterm) = (currentTerm[self])) /\ (logOK)) /\ ((votedFor[self]) \in ({Nil, j})) IN
                                                    /\ Assert(((m[self]).mterm) <= (currentTerm[self]), 
                                                              "Failure of assertion at line 473, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                               /\ LET value02 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                    /\ ((network)[j]).enabled
                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                          ELSE /\ LET value03 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                    /\ ((network)[j]).enabled
                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value03), enabled |-> ((network)[j]).enabled]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << currentTerm, state >>
                              /\ UNCHANGED << log, commitIndex, nextIndex, 
                                              matchIndex, votesResponded, 
                                              votesGranted, leader >>
                         ELSE /\ IF ((m[self]).mtype) = (RequestVoteResponse)
                                    THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                    /\ LET state2 == Follower IN
                                                         /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                         /\ IF ((m[self]).mterm) < (currentTerm'[self])
                                                               THEN /\ state' = [state EXCEPT ![self] = state2]
                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                    /\ UNCHANGED << nextIndex, 
                                                                                    matchIndex, 
                                                                                    votesResponded, 
                                                                                    votesGranted >>
                                                               ELSE /\ LET i2 == self IN
                                                                         LET j2 == (m[self]).msource IN
                                                                           /\ Assert(((m[self]).mterm) = (currentTerm'[self]), 
                                                                                     "Failure of assertion at line 501, column 19.")
                                                                           /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j2})]
                                                                           /\ IF (m[self]).mvoteGranted
                                                                                 THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j2})]
                                                                                      /\ IF ((state2) = (Candidate)) /\ (isQuorum(votesGranted'[self]))
                                                                                            THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                                 /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                                                                                 /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            ELSE /\ state' = [state EXCEPT ![self] = state2]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 /\ UNCHANGED << nextIndex, 
                                                                                                                 matchIndex >>
                                                                                 ELSE /\ IF ((state2) = (Candidate)) /\ (isQuorum(votesGranted[self]))
                                                                                            THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                                 /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                                                                                 /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            ELSE /\ state' = [state EXCEPT ![self] = state2]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 /\ UNCHANGED << nextIndex, 
                                                                                                                 matchIndex >>
                                                                                      /\ UNCHANGED votesGranted
                                               ELSE /\ IF ((m[self]).mterm) < (currentTerm[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << state, 
                                                                               nextIndex, 
                                                                               matchIndex, 
                                                                               votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i3 == self IN
                                                                    LET j3 == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = (currentTerm[self]), 
                                                                                "Failure of assertion at line 533, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![self] = (votesResponded[self]) \union ({j3})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = (votesGranted[self]) \union ({j3})]
                                                                                 /\ IF ((state[self]) = (Candidate)) /\ (isQuorum(votesGranted'[self]))
                                                                                       THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                            /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                                                                            /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            /\ UNCHANGED << state, 
                                                                                                            nextIndex, 
                                                                                                            matchIndex >>
                                                                            ELSE /\ IF ((state[self]) = (Candidate)) /\ (isQuorum(votesGranted[self]))
                                                                                       THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                            /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                                                                            /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            /\ UNCHANGED << state, 
                                                                                                            nextIndex, 
                                                                                                            matchIndex >>
                                                                                 /\ UNCHANGED votesGranted
                                                    /\ UNCHANGED << currentTerm, 
                                                                    votedFor >>
                                         /\ UNCHANGED << network, log, 
                                                         commitIndex, leader >>
                                    ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m[self]).mterm) > (currentTerm[self])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                               /\ LET state3 == Follower IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                    /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                                    /\ LET i == self IN
                                                                         LET j == (m[self]).msource IN
                                                                           LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len(log[self])))) /\ (((m[self]).mprevLogTerm) = (((log[self])[(m[self]).mprevLogIndex]).term))) IN
                                                                             /\ Assert(((m[self]).mterm) <= (currentTerm'[self]), 
                                                                                       "Failure of assertion at line 566, column 19.")
                                                                             /\ IF (((m[self]).mterm) = (currentTerm'[self])) /\ ((state3) = (Candidate))
                                                                                   THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                        /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ LET value10 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                        /\ ((network)[j]).enabled
                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 576, column 23.")
                                                                                                   /\ LET index == ((m[self]).prevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log4 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) = ((m[self]).prevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log4, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value20 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value21 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).prevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value22 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value23 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                                                   ELSE /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state3) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ LET value11 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                        /\ ((network)[j]).enabled
                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]]
                                                                                                        /\ state' = [state EXCEPT ![self] = state3]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state3) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 644, column 23.")
                                                                                                   /\ LET index == ((m[self]).prevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log5 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) = ((m[self]).prevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log5, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value24 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value24), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value25 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value25), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                             /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                        /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).prevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value26 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value26), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value27 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value27), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = state3]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len(log[self])))) /\ (((m[self]).mprevLogTerm) = (((log[self])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= (currentTerm[self]), 
                                                                                  "Failure of assertion at line 717, column 17.")
                                                                        /\ IF (((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ LET value12 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                   /\ ((network)[j]).enabled
                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]]
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 727, column 21.")
                                                                                              /\ LET index == ((m[self]).prevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) = ((m[self]).prevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log6, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value28 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value28), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value29 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value29), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).prevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value210 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value210), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value211 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value211), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                      /\ log' = log
                                                                              ELSE /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ LET value13 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                   /\ ((network)[j]).enabled
                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]]
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 794, column 21.")
                                                                                              /\ LET index == ((m[self]).prevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) = ((m[self]).prevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log7, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value212 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value212), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value213 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value213), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).prevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value214 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value214), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value215 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).prevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value215), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
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
                                                                                                      "Failure of assertion at line 866, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = Max({(((nextIndex[self])[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                     ELSE /\ IF ((m[self]).mterm) < (currentTerm[self])
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = (currentTerm[self]), 
                                                                                                      "Failure of assertion at line 882, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![self] = [matchIndex[self] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![self] = [nextIndex[self] EXCEPT ![j] = Max({(((nextIndex[self])[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                          /\ UNCHANGED << currentTerm, 
                                                                                          state, 
                                                                                          votedFor >>
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << currentTerm, 
                                                                               state, 
                                                                               votedFor, 
                                                                               nextIndex, 
                                                                               matchIndex >>
                                                    /\ UNCHANGED << network, 
                                                                    log, 
                                                                    commitIndex, 
                                                                    leader >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted >>
                   /\ UNCHANGED << fd, idx, m >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx[self]) <= (NumServers)
                               THEN /\ IF (idx[self]) # (self)
                                          THEN /\ LET value30 == [mtype |-> RequestVoteRequest, mterm |-> currentTerm[self], mlastLogTerm |-> LastTerm(log[self]), mlastLogIndex |-> Len(log[self]), msource |-> self, mdest |-> idx[self]] IN
                                                    /\ ((network)[idx[self]]).enabled
                                                    /\ network' = [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value30), enabled |-> ((network)[idx[self]]).enabled]]
                                                    /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                    /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                          ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
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
                                            THEN /\ LET prevLogIndex == (nextIndex[self])[idx[self]] IN
                                                      LET prevLogTerm == IF (prevLogIndex) > (0) THEN ((log[self])[prevLogIndex]).term ELSE 0 IN
                                                        LET lastEntry == Min({Len(log[self]), (nextIndex[self])[idx[self]]}) IN
                                                          LET entries == SubSeq(log[self], (nextIndex[self])[idx[self]], lastEntry) IN
                                                            IF (Len(entries)) > (0)
                                                               THEN /\ LET value40 == [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[self], mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries, mcommitIndex |-> Min({commitIndex[self], lastEntry}), msource |-> self, mdest |-> idx[self]] IN
                                                                         /\ ((network)[idx[self]]).enabled
                                                                         /\ network' = [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value40), enabled |-> ((network)[idx[self]]).enabled]]
                                                                         /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                                    /\ UNCHANGED network
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                 /\ UNCHANGED network
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                      /\ UNCHANGED network
                           /\ UNCHANGED << fd, currentTerm, state, votedFor, 
                                           log, commitIndex, nextIndex, 
                                           matchIndex, votesResponded, 
                                           votesGranted, leader, idx, m >>

server(self) == serverLoop(self) \/ handleMsg(self)
                   \/ requestVoteLoop(self) \/ appendEntriesLoop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: server(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Constraints

LimitTerm == \A i \in ServerSet: currentTerm[i] <= MaxTerm
LimitCommitIndex == \A i \in ServerSet: commitIndex[i] <= MaxCommitIndex

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

=============================================================================
