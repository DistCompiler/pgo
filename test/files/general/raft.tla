-------------------------------- MODULE raft --------------------------------

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
                \* mayFail(self, netEnabled);

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
                                    net[j] := [
                                        mtype       |-> AppendEntriesResponse,
                                        mterm       |-> currentTerm,
                                        msuccess    |-> TRUE,
                                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
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
                        assert newCommitIndex >= commitIndex;
                        commitIndex := newCommitIndex;
                    };

                    \* AppendEntries
                    idx := 1;
                appendEntriesLoop:
                    while (netLen[self] < BufferSize /\ idx <= NumServers) {
                        if (idx /= self) {
                            with (
                                prevLogIndex = nextIndex[idx] - 1,
                                prevLogTerm  = IF prevLogIndex > 0
                                               THEN log[prevLogIndex].term
                                               ELSE 0,
                                lastEntry =    Min({Len(log), nextIndex[idx]}),
                                entries =      SubSeq(log, nextIndex[idx], lastEntry)
                            ) {
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
                        idx := idx + 1;
                    };
                };
            } or {
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
            network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
            with (yielded_network2 = readMsg00) {
              m := yielded_network2;
              assert ((m).mdest) = (self);
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
              assert (newCommitIndex1) >= (commitIndex);
              commitIndex := newCommitIndex1;
              idx := 1;
              goto appendEntriesLoop;
            };
          } else {
            goto serverLoop;
          };
        } or {
          if(((state) = (Candidate)) /\ (isQuorum(votesGranted))) {
            state := Leader;
            nextIndex := [j \in ServerSet |-> (Len(log)) + (1)];
            matchIndex := [j \in ServerSet |-> 0];
            goto serverLoop;
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
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]];
                  goto serverLoop;
                };
              } else {
                with (value01 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
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
                await (Len(((network)[j]).queue)) < (BufferSize);
                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]];
                goto serverLoop;
              };
            } else {
              with (value03 = [mtype |-> RequestVoteResponse, mterm |-> currentTerm, mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                await ((network)[j]).enabled;
                await (Len(((network)[j]).queue)) < (BufferSize);
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
                      with (value10 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]];
                        goto serverLoop;
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
                                with (value20 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value21 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
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
                          if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                            log := Append(log, ((m).mentries)[1]);
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value22 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value23 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
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
                    if((((m).mterm) < (currentTerm)) \/ (((((m).mterm) = (currentTerm)) /\ ((state1) = (Follower))) /\ (~ (logOK)))) {
                      with (value11 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]];
                        state := state1;
                        goto serverLoop;
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
                                with (value24 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value24), enabled |-> ((network)[j]).enabled]];
                                  state := state1;
                                  goto serverLoop;
                                };
                              } else {
                                state := state1;
                                goto serverLoop;
                              };
                            } else {
                              if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m).mentries)[1]).term)))) {
                                commitIndex := (m).mcommitIndex;
                                with (value25 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value25), enabled |-> ((network)[j]).enabled]];
                                  log := log5;
                                  state := state1;
                                  goto serverLoop;
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
                              with (value26 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value26), enabled |-> ((network)[j]).enabled]];
                                state := state1;
                                goto serverLoop;
                              };
                            } else {
                              state := state1;
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value27 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value27), enabled |-> ((network)[j]).enabled]];
                                state := state1;
                                goto serverLoop;
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
                    with (value12 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]];
                      goto serverLoop;
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
                              with (value28 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value28), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value29 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
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
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value210 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value210), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value211 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
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
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]];
                      goto serverLoop;
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
                              with (value212 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value212), enabled |-> ((network)[j]).enabled]];
                                goto serverLoop;
                              };
                            } else {
                              goto serverLoop;
                            };
                          } else {
                            if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m).mentries)[1]).term)))) {
                              commitIndex := (m).mcommitIndex;
                              with (value213 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                await ((network)[j]).enabled;
                                await (Len(((network)[j]).queue)) < (BufferSize);
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
                        if((((m).mentries) # (<<>>)) /\ ((Len(log)) = ((m).mprevLogIndex))) {
                          log := Append(log, ((m).mentries)[1]);
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value214 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value214), enabled |-> ((network)[j]).enabled]];
                              goto serverLoop;
                            };
                          } else {
                            goto serverLoop;
                          };
                        } else {
                          if((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len(log)) >= (index))) /\ ((((log)[index]).term) = ((((m).mentries)[1]).term)))) {
                            commitIndex := (m).mcommitIndex;
                            with (value215 = [mtype |-> AppendEntriesResponse, mterm |-> currentTerm, msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
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
          with (value30 = [mtype |-> RequestVoteRequest, mterm |-> currentTerm, mlastLogTerm |-> LastTerm(log), mlastLogIndex |-> Len(log), msource |-> self, mdest |-> idx]) {
            await ((network)[idx]).enabled;
            await (Len(((network)[idx]).queue)) < (BufferSize);
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
      with (yielded_network1 = Len(((network)[self]).queue)) {
        if(((yielded_network1) < (BufferSize)) /\ ((idx) <= (NumServers))) {
          if((idx) # (self)) {
            with (prevLogIndex1 = ((nextIndex)[idx]) - (1), prevLogTerm1 = IF (prevLogIndex1) > (0) THEN ((log)[prevLogIndex1]).term ELSE 0, lastEntry1 = Min({Len(log), (nextIndex)[idx]}), entries1 = SubSeq(log, (nextIndex)[idx], lastEntry1)) {
              with (value40 = [mtype |-> AppendEntriesRequest, mterm |-> currentTerm, mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({commitIndex, lastEntry1}), msource |-> self, mdest |-> idx]) {
                await ((network)[idx]).enabled;
                await (Len(((network)[idx]).queue)) < (BufferSize);
                network := [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value40), enabled |-> ((network)[idx]).enabled]];
                idx := (idx) + (1);
                goto appendEntriesLoop;
              };
            };
          } else {
            idx := (idx) + (1);
            goto appendEntriesLoop;
          };
        } else {
          goto serverLoop;
        };
      };
  }
  
  fair process (client \in ClientSet)
  {
    sndPutReq:
      with (srv = 1) {
        with (value50 = [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv]) {
          await ((network)[srv]).enabled;
          await (Len(((network)[srv]).queue)) < (BufferSize);
          network := [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value50), enabled |-> ((network)[srv]).enabled]];
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
\* BEGIN TRANSLATION (chksum(pcal) = "a64d7311" /\ chksum(tla) = "9b3fab36")
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
                                               "Failure of assertion at line 450, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                          /\ LET yielded_network2 == readMsg00 IN
                                               /\ m' = [m EXCEPT ![self] = yielded_network2]
                                               /\ Assert(((m'[self]).mdest) = (self), 
                                                         "Failure of assertion at line 456, column 15.")
                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, idx>>
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
                                     /\ UNCHANGED <<network, commitIndex, nextIndex, matchIndex, m>>
                                  \/ /\ IF (state[self]) = (Leader)
                                           THEN /\ LET agreeIndexes1 == {index \in (1) .. (Len(log[self])) : isQuorum(({self}) \union ({k \in ServerSet : ((matchIndex[self])[k]) >= (index)}))} IN
                                                     LET newCommitIndex1 == IF ((agreeIndexes1) # ({})) /\ ((((log[self])[Max(agreeIndexes1)]).term) = (currentTerm[self])) THEN Max(agreeIndexes1) ELSE commitIndex[self] IN
                                                       /\ Assert((newCommitIndex1) >= (commitIndex[self]), 
                                                                 "Failure of assertion at line 480, column 15.")
                                                       /\ commitIndex' = [commitIndex EXCEPT ![self] = newCommitIndex1]
                                                       /\ idx' = [idx EXCEPT ![self] = 1]
                                                       /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                /\ UNCHANGED << commitIndex, 
                                                                idx >>
                                     /\ UNCHANGED <<network, currentTerm, state, votedFor, nextIndex, matchIndex, votesResponded, votesGranted, m>>
                                  \/ /\ IF ((state[self]) = (Candidate)) /\ (isQuorum(votesGranted[self]))
                                           THEN /\ PrintT(<<self, votesGranted[self], votesResponded[self]>>)
                                                /\ state' = [state EXCEPT ![self] = Leader]
                                                /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> (Len(log[self])) + (1)]]
                                                /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                /\ UNCHANGED << state, 
                                                                nextIndex, 
                                                                matchIndex >>
                                     /\ UNCHANGED <<network, currentTerm, votedFor, commitIndex, votesResponded, votesGranted, idx, m>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
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
                                                                "Failure of assertion at line 509, column 15.")
                                                      /\ IF grant
                                                            THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                                 /\ LET value00 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                      /\ ((network)[j]).enabled
                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]]
                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                            ELSE /\ LET value01 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                      /\ ((network)[j]).enabled
                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value01), enabled |-> ((network)[j]).enabled]]
                                                                      /\ votedFor' = [votedFor EXCEPT ![self] = votedFor1]
                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                    ELSE /\ LET i == self IN
                                              LET j == (m[self]).msource IN
                                                LET logOK == (((m[self]).mlastLogTerm) > (LastTerm(log[self]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm(log[self]))) /\ (((m[self]).mlastLogIndex) >= (Len(log[self])))) IN
                                                  LET grant == ((((m[self]).mterm) = (currentTerm[self])) /\ (logOK)) /\ ((votedFor[self]) \in ({Nil, j})) IN
                                                    /\ Assert(((m[self]).mterm) <= (currentTerm[self]), 
                                                              "Failure of assertion at line 531, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                               /\ LET value02 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                    /\ ((network)[j]).enabled
                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                          ELSE /\ LET value03 == [mtype |-> RequestVoteResponse, mterm |-> currentTerm[self], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                    /\ ((network)[j]).enabled
                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
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
                                                    /\ state' = [state EXCEPT ![self] = Follower]
                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                    /\ IF ((m[self]).mterm) < (currentTerm'[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = (currentTerm'[self]), 
                                                                                "Failure of assertion at line 560, column 17.")
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
                                                                                "Failure of assertion at line 575, column 17.")
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
                                                                                       "Failure of assertion at line 594, column 19.")
                                                                             /\ IF (((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Candidate))
                                                                                   THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                        /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ LET value10 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                        /\ ((network)[j]).enabled
                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 605, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log4 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log4, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value20 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log4)) >= (index))) /\ ((((log4)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value21 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value21), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log4]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value22 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value23 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                           /\ log' = log
                                                                                   ELSE /\ IF (((m[self]).mterm) < (currentTerm'[self])) \/ (((((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Follower))) /\ (~ (logOK)))
                                                                                              THEN /\ LET value11 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                        /\ ((network)[j]).enabled
                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]]
                                                                                                        /\ state' = [state EXCEPT ![self] = state1]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   commitIndex >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = (currentTerm'[self])) /\ ((state1) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 678, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log5 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                     IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) = ((m[self]).mprevLogIndex))
                                                                                                                        THEN /\ log' = [log EXCEPT ![self] = Append(log5, ((m[self]).mentries)[1])]
                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value24 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value24), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log5)) >= (index))) /\ ((((log5)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                   THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                        /\ LET value25 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value25), enabled |-> ((network)[j]).enabled]]
                                                                                                                                             /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                             /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   ELSE /\ log' = [log EXCEPT ![self] = log5]
                                                                                                                                        /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                        commitIndex >>
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                           /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value26 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value26), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex >>
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                      /\ LET value27 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value27), enabled |-> ((network)[j]).enabled]]
                                                                                                                                           /\ state' = [state EXCEPT ![self] = state1]
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
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
                                                                                  "Failure of assertion at line 755, column 17.")
                                                                        /\ IF (((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![self] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ LET value12 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                   /\ ((network)[j]).enabled
                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]]
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state'[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 766, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log6, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value28 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value28), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log6)) >= (index))) /\ ((((log6)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value29 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value29), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log6]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value210 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value210), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value211 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value211), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                      /\ log' = log
                                                                              ELSE /\ IF (((m[self]).mterm) < (currentTerm[self])) \/ (((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ LET value13 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                   /\ ((network)[j]).enabled
                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]]
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                              /\ UNCHANGED << log, 
                                                                                                              commitIndex >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = (currentTerm[self])) /\ ((state[self]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 838, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [k \in (1) .. ((Len(log[self])) - (1)) |-> (log[self])[k]] IN
                                                                                                                IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) = ((m[self]).mprevLogIndex))
                                                                                                                   THEN /\ log' = [log EXCEPT ![self] = Append(log7, ((m[self]).mentries)[1])]
                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value212 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value212), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log7)) >= (index))) /\ ((((log7)[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                              THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                   /\ LET value213 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value213), enabled |-> ((network)[j]).enabled]]
                                                                                                                                        /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                              ELSE /\ log' = [log EXCEPT ![self] = log7]
                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                   commitIndex >>
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![self] = Append(log[self], ((m[self]).mentries)[1])]
                                                                                                                      /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log'[self])) >= (index))) /\ ((((log'[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value214 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value214), enabled |-> ((network)[j]).enabled]]
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex >>
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len(log[self])) >= (index))) /\ ((((log[self])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (m[self]).mcommitIndex]
                                                                                                                                 /\ LET value215 == [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[self], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
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
                                                                                                      "Failure of assertion at line 914, column 21.")
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
                                                                                                      "Failure of assertion at line 930, column 21.")
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
                                          THEN /\ LET value30 == [mtype |-> RequestVoteRequest, mterm |-> currentTerm[self], mlastLogTerm |-> LastTerm(log[self]), mlastLogIndex |-> Len(log[self]), msource |-> self, mdest |-> idx[self]] IN
                                                    /\ ((network)[idx[self]]).enabled
                                                    /\ (Len(((network)[idx[self]]).queue)) < (BufferSize)
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
                           /\ LET yielded_network1 == Len(((network)[self]).queue) IN
                                IF ((yielded_network1) < (BufferSize)) /\ ((idx[self]) <= (NumServers))
                                   THEN /\ IF (idx[self]) # (self)
                                              THEN /\ LET prevLogIndex1 == ((nextIndex[self])[idx[self]]) - (1) IN
                                                        LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN ((log[self])[prevLogIndex1]).term ELSE 0 IN
                                                          LET lastEntry1 == Min({Len(log[self]), (nextIndex[self])[idx[self]]}) IN
                                                            LET entries1 == SubSeq(log[self], (nextIndex[self])[idx[self]], lastEntry1) IN
                                                              LET value40 == [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[self], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({commitIndex[self], lastEntry1}), msource |-> self, mdest |-> idx[self]] IN
                                                                /\ ((network)[idx[self]]).enabled
                                                                /\ (Len(((network)[idx[self]]).queue)) < (BufferSize)
                                                                /\ network' = [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value40), enabled |-> ((network)[idx[self]]).enabled]]
                                                                /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                                /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                              ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                   /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                   /\ UNCHANGED network
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                        /\ UNCHANGED << network, idx >>
                           /\ UNCHANGED << fd, currentTerm, state, votedFor, 
                                           log, commitIndex, nextIndex, 
                                           matchIndex, votesResponded, 
                                           votesGranted, leader, m >>

server(self) == serverLoop(self) \/ handleMsg(self)
                   \/ requestVoteLoop(self) \/ appendEntriesLoop(self)

sndPutReq(self) == /\ pc[self] = "sndPutReq"
                   /\ LET srv == 1 IN
                        LET value50 == [mtype |-> ClientPutRequest, mkey |-> Key1, mvalue |-> Value1, msource |-> self, mdest |-> srv] IN
                          /\ ((network)[srv]).enabled
                          /\ (Len(((network)[srv]).queue)) < (BufferSize)
                          /\ network' = [network EXCEPT ![srv] = [queue |-> Append(((network)[srv]).queue, value50), enabled |-> ((network)[srv]).enabled]]
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

EventualElection == <>(\E i \in ServerSet: state[i] = Leader)

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

=============================================================================
