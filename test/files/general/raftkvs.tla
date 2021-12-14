-------------------------------- MODULE raftkvs --------------------------------

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
CONSTANT Debug

CONSTANT NumServers
CONSTANT NumClients

CONSTANT BufferSize

CONSTANT MaxTerm
CONSTANT MaxCommitIndex

CONSTANT MaxNodeFail

CONSTANT LogConcat
CONSTANT LogPop

RECURSIVE MinAcc(_, _), MaxAcc(_, _)

Min(s) ==
    LET e == CHOOSE e \in s : TRUE
    IN MinAcc(s \ { e }, e)

MinAcc(s, e1) ==
    IF s = {} THEN e1
    ELSE
        LET e2 == CHOOSE e2 \in s : TRUE
        IN MinAcc(s \ { e2 }, IF e2 < e1 THEN e2 ELSE e1)

Max(s) ==
    LET e == CHOOSE e \in s : TRUE
    IN MaxAcc(s \ { e }, e)

MaxAcc(s, e1) ==
    IF s = {} THEN e1
    ELSE
        LET e2 == CHOOSE e2 \in s : TRUE
        IN MaxAcc(s \ { e2 }, IF e2 > e1 THEN e2 ELSE e1)

RECURSIVE FindAgreeIndicesAcc(_, _, _, _, _)

isQuorum(s) == Cardinality(s) * 2 > NumServers
ServerSet   == 1..NumServers

FindAgreeIndices(logLocal, i, matchIndex) ==
    FindAgreeIndicesAcc(logLocal, i, matchIndex, Len(logLocal), {})

FindAgreeIndicesAcc(logLocal, i, matchIndex, index, acc) ==
    IF index = 0 THEN acc
    ELSE
        IF isQuorum({i} \cup {k \in ServerSet : matchIndex[k] >= index})
        THEN acc \cup {index}
        ELSE FindAgreeIndicesAcc(logLocal, i, matchIndex, index - 1, acc)

RECURSIVE ApplyLog(_, _, _, _, _)

Put == "put"
Get == "get"

ApplyLogEntry(xentry, xsm, xsmDomain) ==
    LET cmd == xentry.cmd
    IN IF cmd.type = Put
       THEN <<xsm @@ (cmd.key :> cmd.value), xsmDomain \cup {cmd.key}>>
       ELSE <<xsm, xsmDomain>>


\* applies range [start, end] from log to the state machine
ApplyLog(xlog, start, end, xsm, xsmDomain) == 
    IF start > end
    THEN <<xsm, xsmDomain>>
    ELSE
        LET result == ApplyLogEntry(xlog[start], xsm, xsmDomain)
        IN ApplyLog(xlog, start+1, end, result[1], result[2])

(********************

--mpcal raftkvs {
    define {
        Follower  == "follower"
        Candidate == "candidate"
        Leader    == "leader"

        RequestVoteRequest    == "rvq"
        RequestVoteResponse   == "rvp"
        AppendEntriesRequest  == "apq"
        AppendEntriesResponse == "app"
        ClientPutRequest      == "cpq"
        ClientPutResponse     == "cpp"
        ClientGetRequest      == "cgq"
        ClientGetResponse     == "cgp"

        Key1   == "key1"
        Key2   == "key2"
        Value1 == "value1"

        \* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
        \* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

        LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

        Nil == 0

        ServerSenderSet == (NumServers+1)..(NumServers+NumServers)
        ClientSet       == (2*NumServers+1)..(2*NumServers+NumClients)
        NodeSet         == ServerSet \cup ServerSenderSet \cup ClientSet

        KeySet == {}
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

    mapping macro InputChannel {
        read {
            await Len($variable) > 0;
            with (res = Head($variable)) {
                $variable := Tail($variable);
                yield res;
            };
        }

        write {
            yield Append($variable, $value);
        }
    }

    mapping macro PersistentLog {
        read {
            yield $variable;
        }

        write {
            if ($value.cmd = LogConcat) {
                yield $variable \o $value.entries;
            } else if ($value.cmd = LogPop) {
                yield SubSeq($variable, 1, Len($variable) - 1);
            };
        }
    }

    archetype AServer(
        ref net[_], ref fd[_], ref netLen[_], ref netEnabled[_],
        ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref timer, ref in,
        ref votedFor, ref plog[_]
    )
    variables
        matchIndex = [i \in ServerSet |-> 0],

        votesResponded = {},
        votesGranted   = {},

        \* added by Shayan
        leader   = Nil,
        idx      = 1,
        sm       = [i \in KeySet |-> Nil],
        smDomain = KeySet,

        newCommitIndex = 0,
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
                                    log[i]  := SubSeq(log[i], 1, Len(log[i]) - 1);
                                    plog[i] := [cmd |-> LogPop];
                                };
                                
                                \* no conflict: append entry
                                if (
                                    /\ m.mentries /= << >>
                                    /\ Len(log[i]) = m.mprevLogIndex
                                ) {
                                    \* TODO
                                    \* log[i] := Append(log[i], m.mentries[1]);
                                    log[i]  := log[i] \o m.mentries;
                                    \* debug(<<"plog concat", i, leader, m.mentries>>);
                                    plog[i] := [cmd |-> LogConcat, entries |-> m.mentries];
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
                                    with (result = ApplyLog(log[i], commitIndex[i]+1, m.mcommitIndex, sm, smDomain)) {
                                        sm := result[1];
                                        smDomain := result[2];
                                    };
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
                } else if (
                    \/ m.mtype = ClientPutRequest
                    \/ m.mtype = ClientGetRequest
                ) {
                    \* ClientRequest
                    if (state[self] = Leader) {
                        with (entry = [term   |-> currentTerm[self], 
                                       cmd    |-> m.mcmd,
                                       client |-> m.msource]
                        ) {
                            log[self]  := Append(log[self], entry);
                            plog[self] := [cmd |-> LogConcat, entries |-> <<entry>>];

                            \* in := TRUE;
                        };
                    } else {
                        with (
                            i = self, j = m.msource,
                            respType = IF m.mcmd.type = Put
                                       THEN ClientPutResponse
                                       ELSE ClientGetResponse
                        ) {
                            net[j] := [
                                mtype       |-> respType,
                                msuccess    |-> FALSE,
                                mresponse   |-> Nil,
                                mleaderHint |-> leader,
                                msource     |-> i,
                                mdest       |-> j
                            ];
                        };
                    };
                };
            } or {
                \* Server times out and starts a new election.
                await state[self] \in {Follower, Candidate};
                await (
                    /\ netLen[self] = 0
                    /\ timer
                );
                if (leader /= Nil) {
                    await fd[leader];
                };
                with (i = self) {
                    state[i]       := Candidate;
                    currentTerm[i] := currentTerm[i] + 1;
                    votedFor       := i;
                    votesResponded := {i};
                    votesGranted   := {i};

                    debug(<<"ServerTimeout", i, currentTerm[i]>>);
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
                    (* agreeIndexes = {index \in 1..Len(log[i]) :
                                        isQuorum({i} \cup {k \in ServerSet : 
                                                                matchIndex[k] >= index})}, *)
                    agreeIndexes = FindAgreeIndices(log[i], i, matchIndex), \* gives a much smaller set than above, proportional to disagreement not log size
                    nCommitIndex =
                        IF /\ agreeIndexes /= {}
                           /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
                        THEN Max(agreeIndexes)
                        ELSE commitIndex[i]
                ) {
                    \* print <<"advance commit index", i, agreeIndexes, newCommitIndex, commitIndex[i]>>;
                    newCommitIndex := nCommitIndex;
                    assert newCommitIndex >= commitIndex[i];
                };

            applyLoop:
                while (commitIndex[self] < newCommitIndex) {
                    commitIndex[self] := commitIndex[self] + 1;
                    with (
                        i = self,
                        k = commitIndex[i],
                        entry = log[i][k],
                        cmd   = entry.cmd,
                        respType = IF cmd.type = Put
                                   THEN ClientPutResponse
                                   ELSE ClientGetResponse
                    ) {
                        if (cmd.type = Put) {
                            sm := sm @@ (cmd.key :> cmd.value); \* allows sm to grow
                            smDomain := smDomain \cup {cmd.key}
                        };
                        with(reqOk = cmd.key \in smDomain) {
                            net[entry.client] := [
                                mtype       |-> respType,
                                msuccess    |-> TRUE,
                                mresponse   |-> [
                                    idx   |-> cmd.idx,
                                    key   |-> cmd.key,
                                    value |-> IF reqOk THEN sm[cmd.key] ELSE Nil,
                                    ok    |-> reqOk
                                ],
                                mleaderHint |-> i,
                                msource     |-> i,
                                mdest       |-> entry.client
                            ];
                        };
                    };
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

    archetype AClient(ref net[_], ref fd[_], ref in, ref out, ref netLen[_], ref timeout)
    variable leader = Nil, req, resp, reqIdx = 0;
    {
    clientLoop:
        while (TRUE) {
            either {
                req := in;
                reqIdx := reqIdx + 1;
            } or {
                resp := net[self]; \* we're not even expecting anything; discard.
                goto clientLoop;
            };

        sndReq:
            if (leader = Nil) {
                with (srv \in ServerSet) {
                    leader := srv;
                };
            };
            debug(<<"clientSndReq", self, leader, req>>);
            if (req.type = Put) {
                Send(net, leader, fd, [
                    mtype   |-> ClientPutRequest,
                    mcmd    |-> [
                        idx   |-> reqIdx,
                        type  |-> Put,
                        key   |-> req.key,
                        value |-> req.value
                    ],
                    msource |-> self,
                    mdest   |-> leader
                ]);
            } else if (req.type = Get) {
                Send(net, leader, fd, [
                    mtype   |-> ClientGetRequest,
                    mcmd    |-> [
                        idx  |-> reqIdx,
                        type |-> Get,
                        key  |-> req.key
                    ],
                    msource |-> self,
                    mdest   |-> leader
                ]);
            };

        rcvResp:
            either {
                resp := net[self];
                debug(<<"resp", resp>>);
                assert resp.mdest = self;

                \* it should be /very likely/ that indexed requests will help us throw out duplicate server responses
                \* one edge case I can think of: start, do one req, immediately stop + restart, immediately get stale response to last req
                if (resp.msuccess /\ resp.mresponse.idx /= reqIdx) {
                    goto rcvResp;
                } else {
                    leader := resp.mleaderHint;
                    assert /\ req.type = Get => resp.mtype = ClientGetResponse
                           /\ req.type = Put => resp.mtype = ClientPutResponse;
                    if (\lnot resp.msuccess) {
                        goto sndReq;
                    } else {
                        assert /\ resp.mresponse.idx = reqIdx
                               /\ resp.mresponse.key = req.key;
                        out := resp;
                    };
                };
            } or {
                await \/ /\ fd[leader] 
                         /\ netLen[self] = 0
                      \/ timeout;
                leader := Nil;
                goto sndReq;
            };
        };
    }

    variables
        network = [i \in NodeSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd = [i \in ServerSet |-> FALSE];
    
        sm = [i \in ServerSenderSet |-> i - NumServers];

        state       = [i \in ServerSet |-> Follower];
        nextIndex   = [i \in ServerSet |-> [j \in ServerSet |-> 1]];
        log         = [i \in ServerSet |-> <<>>];
        currentTerm = [i \in ServerSet |-> 1];
        commitIndex = [i \in ServerSet |-> 0];

        plog        = [i \in ServerSet |-> <<>>];
        
        timer = TRUE;
        in    = TRUE;

        inCh  = <<
            [type |-> Put, key |-> Key1, value |-> Value1],
            \* [type |-> Get, key |-> Key2]
            [type |-> Get, key |-> Key1]
        >>;
        outCh;

    fair process (server \in ServerSet) == instance AServer(
        ref network[_], ref fd[_], ref network[_], ref network[_],
        ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref timer, ref in,
        Nil, ref plog[_]
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @13[_] via PersistentLog;
    
    fair process (sender \in ServerSenderSet) == instance AServerSender(
        ref network[_], ref fd[_], ref network[_],
        sm[sender], ref state[_], ref nextIndex[_], ref log[_], ref currentTerm[_], ref commitIndex[_],
        ref in
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3[_] via NetworkToggle;
    
    fair process (client \in ClientSet) == instance AClient(ref network[_], ref fd[_], ref inCh, ref outCh, ref network[_], FALSE)
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3    via InputChannel
        mapping @5[_] via NetworkBufferLength;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raftkvs {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; sm = [i \in ServerSenderSet |-> (i) - (NumServers)]; state = [i \in ServerSet |-> Follower]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; log = [i \in ServerSet |-> <<>>]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; plog = [i \in ServerSet |-> <<>>]; timer = TRUE; in = TRUE; inCh = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key1]>>; outCh;
  define{
    Follower == "follower"
    Candidate == "candidate"
    Leader == "leader"
    RequestVoteRequest == "rvq"
    RequestVoteResponse == "rvp"
    AppendEntriesRequest == "apq"
    AppendEntriesResponse == "app"
    ClientPutRequest == "cpq"
    ClientPutResponse == "cpp"
    ClientGetRequest == "cgq"
    ClientGetResponse == "cgp"
    Key1 == "key1"
    Key2 == "key2"
    Value1 == "value1"
    LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
    Nil == 0
    ServerSenderSet == ((NumServers) + (1)) .. ((NumServers) + (NumServers))
    ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
    NodeSet == ((ServerSet) \union (ServerSenderSet)) \union (ClientSet)
    KeySet == {}
  }
  
  fair process (server \in ServerSet)
    variables matchIndex = [i \in ServerSet |-> 0]; votesResponded = {}; votesGranted = {}; leader = Nil; idx = 1; sm0 = [i \in KeySet |-> Nil]; smDomain = KeySet; newCommitIndex = 0; m; votedFor = Nil;
  {
    serverLoop:
      if (TRUE) {
        either {
          assert ((network)[self]).enabled;
          await (Len(((network)[self]).queue)) > (0);
          with (
            readMsg00 = Head(((network)[self]).queue), 
            network0 = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]], 
            yielded_network6 = readMsg00
          ) {
            m := yielded_network6;
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
          with (yielded_network00 = Len(((network)[self]).queue)) {
            await ((yielded_network00) = (0)) /\ (timer);
            if ((leader) # (Nil)) {
              with (yielded_fd8 = (fd)[leader]) {
                await yielded_fd8;
                with (i2 = self) {
                  state := [state EXCEPT ![i2] = Candidate];
                  currentTerm := [currentTerm EXCEPT ![i2] = ((currentTerm)[i2]) + (1)];
                  votedFor := i2;
                  votesResponded := {i2};
                  votesGranted := {i2};
                  if (Debug) {
                    print <<"ServerTimeout", i2, (currentTerm)[i2]>>;
                    idx := 1;
                    goto requestVoteLoop;
                  } else {
                    idx := 1;
                    goto requestVoteLoop;
                  };
                };
              };
            } else {
              with (i3 = self) {
                state := [state EXCEPT ![i3] = Candidate];
                currentTerm := [currentTerm EXCEPT ![i3] = ((currentTerm)[i3]) + (1)];
                votedFor := i3;
                votesResponded := {i3};
                votesGranted := {i3};
                if (Debug) {
                  print <<"ServerTimeout", i3, (currentTerm)[i3]>>;
                  idx := 1;
                  goto requestVoteLoop;
                } else {
                  idx := 1;
                  goto requestVoteLoop;
                };
              };
            };
          };
        } or {
          await ((state)[self]) = (Leader);
          with (
            i = self, 
            agreeIndexes = FindAgreeIndices((log)[i], i, matchIndex), 
            nCommitIndex = IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i]
          ) {
            newCommitIndex := nCommitIndex;
            assert (newCommitIndex) >= ((commitIndex)[i]);
            goto applyLoop;
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
                with (value15 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value15), enabled |-> ((network)[j]).enabled]];
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
                with (value16 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]];
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
                with (value17 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]];
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
                with (value18 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]];
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
                          with (
                            log4 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                            value30 = [cmd |-> LogPop]
                          ) {
                            if (((value30).cmd) = (LogConcat)) {
                              with (plog4 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value30).entries)]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                  log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                  with (value40 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value40).cmd) = (LogConcat)) {
                                      plog := [plog4 EXCEPT ![i] = ((plog4)[i]) \o ((value40).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result16 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result16)[1];
                                          smDomain := (result16)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value50 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd20 = (fd)[j]) {
                                              await yielded_fd20;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value40).cmd) = (LogPop)) {
                                        plog := [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result17 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result17)[1];
                                            smDomain := (result17)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value51 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd21 = (fd)[j]) {
                                                await yielded_fd21;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result18 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result18)[1];
                                            smDomain := (result18)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value52 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]];
                                                plog := plog4;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd22 = (fd)[j]) {
                                                await yielded_fd22;
                                                plog := plog4;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog4;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result19 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result19)[1];
                                      smDomain := (result19)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value53 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]];
                                          plog := plog4;
                                          log := log4;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd23 = (fd)[j]) {
                                          await yielded_fd23;
                                          plog := plog4;
                                          log := log4;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    plog := plog4;
                                    log := log4;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value30).cmd) = (LogPop)) {
                                with (plog5 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                    log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                    with (value41 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value41).cmd) = (LogConcat)) {
                                        plog := [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value41).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result20 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result20)[1];
                                            smDomain := (result20)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value54 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd24 = (fd)[j]) {
                                                await yielded_fd24;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value41).cmd) = (LogPop)) {
                                          plog := [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result21 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                              sm0 := (result21)[1];
                                              smDomain := (result21)[2];
                                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                              either {
                                                with (value55 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd25 = (fd)[j]) {
                                                  await yielded_fd25;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result22 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                              sm0 := (result22)[1];
                                              smDomain := (result22)[2];
                                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                              either {
                                                with (value56 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]];
                                                  plog := plog5;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd26 = (fd)[j]) {
                                                  await yielded_fd26;
                                                  plog := plog5;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog5;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result23 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result23)[1];
                                        smDomain := (result23)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value57 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]];
                                            plog := plog5;
                                            log := log4;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd27 = (fd)[j]) {
                                            await yielded_fd27;
                                            plog := plog5;
                                            log := log4;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      plog := plog5;
                                      log := log4;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                  log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                  with (value42 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value42).cmd) = (LogConcat)) {
                                      plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value42).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result24 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result24)[1];
                                          smDomain := (result24)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value58 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd28 = (fd)[j]) {
                                              await yielded_fd28;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value42).cmd) = (LogPop)) {
                                        plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result25 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result25)[1];
                                            smDomain := (result25)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value59 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd29 = (fd)[j]) {
                                                await yielded_fd29;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result26 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result26)[1];
                                            smDomain := (result26)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value510 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd210 = (fd)[j]) {
                                                await yielded_fd210;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result27 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result27)[1];
                                      smDomain := (result27)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value511 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]];
                                          log := log4;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd211 = (fd)[j]) {
                                          await yielded_fd211;
                                          log := log4;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := log4;
                                    goto serverLoop;
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                            log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                            with (value43 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                              if (((value43).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value43).entries)];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result28 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result28)[1];
                                    smDomain := (result28)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value512 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd212 = (fd)[j]) {
                                        await yielded_fd212;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  goto serverLoop;
                                };
                              } else {
                                if (((value43).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result29 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result29)[1];
                                      smDomain := (result29)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value513 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd213 = (fd)[j]) {
                                          await yielded_fd213;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    goto serverLoop;
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result30 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result30)[1];
                                      smDomain := (result30)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value514 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd214 = (fd)[j]) {
                                          await yielded_fd214;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    goto serverLoop;
                                  };
                                };
                              };
                            };
                          } else {
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              with (result31 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                sm0 := (result31)[1];
                                smDomain := (result31)[2];
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value515 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd215 = (fd)[j]) {
                                    await yielded_fd215;
                                    goto serverLoop;
                                  };
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
                          with (
                            log5 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                            value31 = [cmd |-> LogPop]
                          ) {
                            if (((value31).cmd) = (LogConcat)) {
                              with (plog6 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value31).entries)]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                  log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                  with (value44 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value44).cmd) = (LogConcat)) {
                                      plog := [plog6 EXCEPT ![i] = ((plog6)[i]) \o ((value44).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result32 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result32)[1];
                                          smDomain := (result32)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value516 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]];
                                              state := state1;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd216 = (fd)[j]) {
                                              await yielded_fd216;
                                              state := state1;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value44).cmd) = (LogPop)) {
                                        plog := [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result33 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result33)[1];
                                            smDomain := (result33)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value517 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd217 = (fd)[j]) {
                                                await yielded_fd217;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result34 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result34)[1];
                                            smDomain := (result34)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value518 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]];
                                                plog := plog6;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd218 = (fd)[j]) {
                                                await yielded_fd218;
                                                plog := plog6;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog6;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result35 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result35)[1];
                                      smDomain := (result35)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value519 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]];
                                          plog := plog6;
                                          log := log5;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd219 = (fd)[j]) {
                                          await yielded_fd219;
                                          plog := plog6;
                                          log := log5;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    plog := plog6;
                                    log := log5;
                                    state := state1;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value31).cmd) = (LogPop)) {
                                with (plog7 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                    log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                    with (value45 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value45).cmd) = (LogConcat)) {
                                        plog := [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value45).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result36 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result36)[1];
                                            smDomain := (result36)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value520 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd220 = (fd)[j]) {
                                                await yielded_fd220;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value45).cmd) = (LogPop)) {
                                          plog := [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result37 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                              sm0 := (result37)[1];
                                              smDomain := (result37)[2];
                                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                              either {
                                                with (value521 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]];
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd221 = (fd)[j]) {
                                                  await yielded_fd221;
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result38 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                              sm0 := (result38)[1];
                                              smDomain := (result38)[2];
                                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                              either {
                                                with (value522 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]];
                                                  plog := plog7;
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd222 = (fd)[j]) {
                                                  await yielded_fd222;
                                                  plog := plog7;
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog7;
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result39 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result39)[1];
                                        smDomain := (result39)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value523 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]];
                                            plog := plog7;
                                            log := log5;
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd223 = (fd)[j]) {
                                            await yielded_fd223;
                                            plog := plog7;
                                            log := log5;
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      plog := plog7;
                                      log := log5;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                  log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                  with (value46 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value46).cmd) = (LogConcat)) {
                                      plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value46).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result40 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result40)[1];
                                          smDomain := (result40)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value524 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]];
                                              state := state1;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd224 = (fd)[j]) {
                                              await yielded_fd224;
                                              state := state1;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value46).cmd) = (LogPop)) {
                                        plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result41 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result41)[1];
                                            smDomain := (result41)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value525 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd225 = (fd)[j]) {
                                                await yielded_fd225;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result42 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result42)[1];
                                            smDomain := (result42)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value526 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd226 = (fd)[j]) {
                                                await yielded_fd226;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result43 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result43)[1];
                                      smDomain := (result43)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value527 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]];
                                          log := log5;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd227 = (fd)[j]) {
                                          await yielded_fd227;
                                          log := log5;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := log5;
                                    state := state1;
                                    goto serverLoop;
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                            log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                            with (value47 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                              if (((value47).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value47).entries)];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result44 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result44)[1];
                                    smDomain := (result44)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value528 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd228 = (fd)[j]) {
                                        await yielded_fd228;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  state := state1;
                                  goto serverLoop;
                                };
                              } else {
                                if (((value47).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result45 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result45)[1];
                                      smDomain := (result45)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value529 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd229 = (fd)[j]) {
                                          await yielded_fd229;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    state := state1;
                                    goto serverLoop;
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result46 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result46)[1];
                                      smDomain := (result46)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value530 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd230 = (fd)[j]) {
                                          await yielded_fd230;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    state := state1;
                                    goto serverLoop;
                                  };
                                };
                              };
                            };
                          } else {
                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                              with (result47 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                sm0 := (result47)[1];
                                smDomain := (result47)[2];
                                commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                either {
                                  with (value531 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]];
                                    state := state1;
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd231 = (fd)[j]) {
                                    await yielded_fd231;
                                    state := state1;
                                    goto serverLoop;
                                  };
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
                        with (
                          log6 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                          value32 = [cmd |-> LogPop]
                        ) {
                          if (((value32).cmd) = (LogConcat)) {
                            with (plog8 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)]) {
                              if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                with (value48 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value48).cmd) = (LogConcat)) {
                                    plog := [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value48).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result48 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result48)[1];
                                        smDomain := (result48)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value532 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd232 = (fd)[j]) {
                                            await yielded_fd232;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value48).cmd) = (LogPop)) {
                                      plog := [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result49 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result49)[1];
                                          smDomain := (result49)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value533 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd233 = (fd)[j]) {
                                              await yielded_fd233;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result50 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result50)[1];
                                          smDomain := (result50)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value534 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]];
                                              plog := plog8;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd234 = (fd)[j]) {
                                              await yielded_fd234;
                                              plog := plog8;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        plog := plog8;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result51 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result51)[1];
                                    smDomain := (result51)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value535 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]];
                                        plog := plog8;
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd235 = (fd)[j]) {
                                        await yielded_fd235;
                                        plog := plog8;
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  plog := plog8;
                                  log := log6;
                                  goto serverLoop;
                                };
                              };
                            };
                          } else {
                            if (((value32).cmd) = (LogPop)) {
                              with (plog9 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                  log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                  with (value49 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value49).cmd) = (LogConcat)) {
                                      plog := [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value49).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result52 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result52)[1];
                                          smDomain := (result52)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value536 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd236 = (fd)[j]) {
                                              await yielded_fd236;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value49).cmd) = (LogPop)) {
                                        plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result53 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result53)[1];
                                            smDomain := (result53)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value537 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd237 = (fd)[j]) {
                                                await yielded_fd237;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result54 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result54)[1];
                                            smDomain := (result54)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value538 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]];
                                                plog := plog9;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd238 = (fd)[j]) {
                                                await yielded_fd238;
                                                plog := plog9;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog9;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result55 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result55)[1];
                                      smDomain := (result55)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value539 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]];
                                          plog := plog9;
                                          log := log6;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd239 = (fd)[j]) {
                                          await yielded_fd239;
                                          plog := plog9;
                                          log := log6;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    plog := plog9;
                                    log := log6;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                with (value410 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value410).cmd) = (LogConcat)) {
                                    plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value410).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result56 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result56)[1];
                                        smDomain := (result56)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value540 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd240 = (fd)[j]) {
                                            await yielded_fd240;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value410).cmd) = (LogPop)) {
                                      plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result57 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result57)[1];
                                          smDomain := (result57)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value541 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd241 = (fd)[j]) {
                                              await yielded_fd241;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result58 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result58)[1];
                                          smDomain := (result58)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value542 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd242 = (fd)[j]) {
                                              await yielded_fd242;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result59 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result59)[1];
                                    smDomain := (result59)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value543 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]];
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd243 = (fd)[j]) {
                                        await yielded_fd243;
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := log6;
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        };
                      } else {
                        if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                          log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                          with (value411 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                            if (((value411).cmd) = (LogConcat)) {
                              plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value411).entries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (result60 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                  sm0 := (result60)[1];
                                  smDomain := (result60)[2];
                                  commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                  either {
                                    with (value544 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd244 = (fd)[j]) {
                                      await yielded_fd244;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if (((value411).cmd) = (LogPop)) {
                                plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result61 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result61)[1];
                                    smDomain := (result61)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value545 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd245 = (fd)[j]) {
                                        await yielded_fd245;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result62 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result62)[1];
                                    smDomain := (result62)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value546 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd246 = (fd)[j]) {
                                        await yielded_fd246;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            with (result63 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                              sm0 := (result63)[1];
                              smDomain := (result63)[2];
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value547 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd247 = (fd)[j]) {
                                  await yielded_fd247;
                                  goto serverLoop;
                                };
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
                        with (
                          log7 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                          value33 = [cmd |-> LogPop]
                        ) {
                          if (((value33).cmd) = (LogConcat)) {
                            with (plog10 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)]) {
                              if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                with (value412 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value412).cmd) = (LogConcat)) {
                                    plog := [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value412).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result64 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result64)[1];
                                        smDomain := (result64)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value548 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd248 = (fd)[j]) {
                                            await yielded_fd248;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value412).cmd) = (LogPop)) {
                                      plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result65 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result65)[1];
                                          smDomain := (result65)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value549 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd249 = (fd)[j]) {
                                              await yielded_fd249;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result66 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result66)[1];
                                          smDomain := (result66)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value550 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]];
                                              plog := plog10;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd250 = (fd)[j]) {
                                              await yielded_fd250;
                                              plog := plog10;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        plog := plog10;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result67 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result67)[1];
                                    smDomain := (result67)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value551 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]];
                                        plog := plog10;
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd251 = (fd)[j]) {
                                        await yielded_fd251;
                                        plog := plog10;
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  plog := plog10;
                                  log := log7;
                                  goto serverLoop;
                                };
                              };
                            };
                          } else {
                            if (((value33).cmd) = (LogPop)) {
                              with (plog11 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                  log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                  with (value413 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value413).cmd) = (LogConcat)) {
                                      plog := [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value413).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result68 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result68)[1];
                                          smDomain := (result68)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value552 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd252 = (fd)[j]) {
                                              await yielded_fd252;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value413).cmd) = (LogPop)) {
                                        plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result69 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result69)[1];
                                            smDomain := (result69)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value553 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd253 = (fd)[j]) {
                                                await yielded_fd253;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result70 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                            sm0 := (result70)[1];
                                            smDomain := (result70)[2];
                                            commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                            either {
                                              with (value554 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]];
                                                plog := plog11;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd254 = (fd)[j]) {
                                                await yielded_fd254;
                                                plog := plog11;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog11;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result71 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                      sm0 := (result71)[1];
                                      smDomain := (result71)[2];
                                      commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                      either {
                                        with (value555 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]];
                                          plog := plog11;
                                          log := log7;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd255 = (fd)[j]) {
                                          await yielded_fd255;
                                          plog := plog11;
                                          log := log7;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    plog := plog11;
                                    log := log7;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                with (value414 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value414).cmd) = (LogConcat)) {
                                    plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value414).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result72 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                        sm0 := (result72)[1];
                                        smDomain := (result72)[2];
                                        commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                        either {
                                          with (value556 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd256 = (fd)[j]) {
                                            await yielded_fd256;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value414).cmd) = (LogPop)) {
                                      plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result73 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result73)[1];
                                          smDomain := (result73)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value557 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd257 = (fd)[j]) {
                                              await yielded_fd257;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result74 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                          sm0 := (result74)[1];
                                          smDomain := (result74)[2];
                                          commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                          either {
                                            with (value558 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd258 = (fd)[j]) {
                                              await yielded_fd258;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result75 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result75)[1];
                                    smDomain := (result75)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value559 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]];
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd259 = (fd)[j]) {
                                        await yielded_fd259;
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := log7;
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        };
                      } else {
                        if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                          log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                          with (value415 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                            if (((value415).cmd) = (LogConcat)) {
                              plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value415).entries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (result76 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                  sm0 := (result76)[1];
                                  smDomain := (result76)[2];
                                  commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                  either {
                                    with (value560 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd260 = (fd)[j]) {
                                      await yielded_fd260;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if (((value415).cmd) = (LogPop)) {
                                plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result77 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result77)[1];
                                    smDomain := (result77)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value561 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd261 = (fd)[j]) {
                                        await yielded_fd261;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result78 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                                    sm0 := (result78)[1];
                                    smDomain := (result78)[2];
                                    commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                                    either {
                                      with (value562 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd262 = (fd)[j]) {
                                        await yielded_fd262;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            with (result79 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, sm0, smDomain)) {
                              sm0 := (result79)[1];
                              smDomain := (result79)[2];
                              commitIndex := [commitIndex EXCEPT ![i] = (m).mcommitIndex];
                              either {
                                with (value563 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd263 = (fd)[j]) {
                                  await yielded_fd263;
                                  goto serverLoop;
                                };
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
              if ((((m).mtype) = (ClientPutRequest)) \/ (((m).mtype) = (ClientGetRequest))) {
                if (((state)[self]) = (Leader)) {
                  with (entry = [term |-> (currentTerm)[self], cmd |-> (m).mcmd, client |-> (m).msource]) {
                    log := [log EXCEPT ![self] = Append((log)[self], entry)];
                    with (value60 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                      if (((value60).cmd) = (LogConcat)) {
                        plog := [plog EXCEPT ![self] = ((plog)[self]) \o ((value60).entries)];
                        goto serverLoop;
                      } else {
                        if (((value60).cmd) = (LogPop)) {
                          plog := [plog EXCEPT ![self] = SubSeq((plog)[self], 1, (Len((plog)[self])) - (1))];
                          goto serverLoop;
                        } else {
                          goto serverLoop;
                        };
                      };
                    };
                  };
                } else {
                  with (
                    i = self, 
                    j = (m).msource, 
                    respType = IF (((m).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse, 
                    value70 = [mtype |-> respType, msuccess |-> FALSE, mresponse |-> Nil, mleaderHint |-> leader, msource |-> i, mdest |-> j]
                  ) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value70), enabled |-> ((network)[j]).enabled]];
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
    requestVoteLoop:
      if ((idx) <= (NumServers)) {
        if ((idx) # (self)) {
          either {
            with (value80 = [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[self], mlastLogTerm |-> LastTerm((log)[self]), mlastLogIndex |-> Len((log)[self]), msource |-> self, mdest |-> idx]) {
              await ((network)[idx]).enabled;
              await (Len(((network)[idx]).queue)) < (BufferSize);
              with (network1 = [network EXCEPT ![idx] = [queue |-> Append(((network)[idx]).queue, value80), enabled |-> ((network)[idx]).enabled]]) {
                idx := (idx) + (1);
                if (ExploreFail) {
                  either {
                    skip;
                    network := network1;
                    goto requestVoteLoop;
                  } or {
                    with (value90 = FALSE) {
                      network := [network1 EXCEPT ![self] = [queue |-> ((network1)[self]).queue, enabled |-> value90]];
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
                  with (value91 = FALSE) {
                    network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value91]];
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
              with (value92 = FALSE) {
                network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value92]];
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
    applyLoop:
      if (((commitIndex)[self]) < (newCommitIndex)) {
        commitIndex := [commitIndex EXCEPT ![self] = ((commitIndex)[self]) + (1)];
        with (
          i = self, 
          k = (commitIndex)[i], 
          entry = ((log)[i])[k], 
          cmd = (entry).cmd, 
          respType = IF ((cmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse
        ) {
          if (((cmd).type) = (Put)) {
            sm0 := (sm0) @@ (((cmd).key) :> ((cmd).value));
            smDomain := (smDomain) \union ({(cmd).key});
            with (
              reqOk = ((cmd).key) \in (smDomain), 
              value100 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN (sm0)[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value100), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          } else {
            with (
              reqOk = ((cmd).key) \in (smDomain), 
              value101 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN (sm0)[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value101), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          };
        };
      } else {
        goto serverLoop;
      };
    failLabel:
      with (value110 = TRUE) {
        fd := [fd EXCEPT ![self] = value110];
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
                with (value120 = [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[sid], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[sid], lastEntry1}), msource |-> sid, mdest |-> idx0]) {
                  await ((network)[idx0]).enabled;
                  await (Len(((network)[idx0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![idx0] = [queue |-> Append(((network)[idx0]).queue, value120), enabled |-> ((network)[idx0]).enabled]];
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
    variables leader0 = Nil; req; resp; reqIdx = 0; timeout = FALSE;
  {
    clientLoop:
      if (TRUE) {
        either {
          await (Len(inCh)) > (0);
          with (res00 = Head(inCh)) {
            inCh := Tail(inCh);
            with (yielded_inCh0 = res00) {
              req := yielded_inCh0;
              reqIdx := (reqIdx) + (1);
              goto sndReq;
            };
          };
        } or {
          assert ((network)[self]).enabled;
          await (Len(((network)[self]).queue)) > (0);
          with (readMsg10 = Head(((network)[self]).queue)) {
            network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
            with (yielded_network30 = readMsg10) {
              resp := yielded_network30;
              goto clientLoop;
            };
          };
        };
      } else {
        goto Done;
      };
    sndReq:
      if ((leader0) = (Nil)) {
        with (srv1 \in ServerSet) {
          leader0 := srv1;
          if (Debug) {
            print <<"clientSndReq", self, leader0, req>>;
            if (((req).type) = (Put)) {
              either {
                with (value130 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value130), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd50 = (fd)[leader0]) {
                  await yielded_fd50;
                  goto rcvResp;
                };
              };
            } else {
              if (((req).type) = (Get)) {
                either {
                  with (value140 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                    await ((network)[leader0]).enabled;
                    await (Len(((network)[leader0]).queue)) < (BufferSize);
                    network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value140), enabled |-> ((network)[leader0]).enabled]];
                    goto rcvResp;
                  };
                } or {
                  with (yielded_fd60 = (fd)[leader0]) {
                    await yielded_fd60;
                    goto rcvResp;
                  };
                };
              } else {
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Put)) {
              either {
                with (value131 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value131), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd51 = (fd)[leader0]) {
                  await yielded_fd51;
                  goto rcvResp;
                };
              };
            } else {
              if (((req).type) = (Get)) {
                either {
                  with (value141 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                    await ((network)[leader0]).enabled;
                    await (Len(((network)[leader0]).queue)) < (BufferSize);
                    network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value141), enabled |-> ((network)[leader0]).enabled]];
                    goto rcvResp;
                  };
                } or {
                  with (yielded_fd61 = (fd)[leader0]) {
                    await yielded_fd61;
                    goto rcvResp;
                  };
                };
              } else {
                goto rcvResp;
              };
            };
          };
        };
      } else {
        if (Debug) {
          print <<"clientSndReq", self, leader0, req>>;
          if (((req).type) = (Put)) {
            either {
              with (value132 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value132), enabled |-> ((network)[leader0]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd52 = (fd)[leader0]) {
                await yielded_fd52;
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Get)) {
              either {
                with (value142 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value142), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd62 = (fd)[leader0]) {
                  await yielded_fd62;
                  goto rcvResp;
                };
              };
            } else {
              goto rcvResp;
            };
          };
        } else {
          if (((req).type) = (Put)) {
            either {
              with (value133 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value133), enabled |-> ((network)[leader0]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd53 = (fd)[leader0]) {
                await yielded_fd53;
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Get)) {
              either {
                with (value143 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value143), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd63 = (fd)[leader0]) {
                  await yielded_fd63;
                  goto rcvResp;
                };
              };
            } else {
              goto rcvResp;
            };
          };
        };
      };
    rcvResp:
      either {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg20 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network40 = readMsg20) {
            resp := yielded_network40;
            if (Debug) {
              print <<"resp", resp>>;
              assert ((resp).mdest) = (self);
              if (((resp).msuccess) /\ ((((resp).mresponse).idx) # (reqIdx))) {
                goto rcvResp;
              } else {
                leader0 := (resp).mleaderHint;
                assert ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)));
                if (~ ((resp).msuccess)) {
                  goto sndReq;
                } else {
                  assert ((((resp).mresponse).idx) = (reqIdx)) /\ ((((resp).mresponse).key) = ((req).key));
                  outCh := resp;
                  goto clientLoop;
                };
              };
            } else {
              assert ((resp).mdest) = (self);
              if (((resp).msuccess) /\ ((((resp).mresponse).idx) # (reqIdx))) {
                goto rcvResp;
              } else {
                leader0 := (resp).mleaderHint;
                assert ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)));
                if (~ ((resp).msuccess)) {
                  goto sndReq;
                } else {
                  assert ((((resp).mresponse).idx) = (reqIdx)) /\ ((((resp).mresponse).key) = ((req).key));
                  outCh := resp;
                  goto clientLoop;
                };
              };
            };
          };
        };
      } or {
        with (
          yielded_fd70 = (fd)[leader0], 
          yielded_network50 = Len(((network)[self]).queue)
        ) {
          await ((yielded_fd70) /\ ((yielded_network50) = (0))) \/ (timeout);
          leader0 := Nil;
          goto sndReq;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "1ac070a3" /\ chksum(tla) = "c9ea1c8f") PCal-18049938ece8066a38eb5044080cf45c
CONSTANT defaultInitValue
VARIABLES network, fd, sm, state, nextIndex, log, currentTerm, commitIndex, 
          plog, timer, in, inCh, outCh, pc

(* define statement *)
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"
Key1 == "key1"
Key2 == "key2"
Value1 == "value1"
LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
Nil == 0
ServerSenderSet == ((NumServers) + (1)) .. ((NumServers) + (NumServers))
ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
NodeSet == ((ServerSet) \union (ServerSenderSet)) \union (ClientSet)
KeySet == {}

VARIABLES matchIndex, votesResponded, votesGranted, leader, idx, sm0, 
          smDomain, newCommitIndex, m, votedFor, idx0, sid, leader0, req, 
          resp, reqIdx, timeout

vars == << network, fd, sm, state, nextIndex, log, currentTerm, commitIndex, 
           plog, timer, in, inCh, outCh, pc, matchIndex, votesResponded, 
           votesGranted, leader, idx, sm0, smDomain, newCommitIndex, m, 
           votedFor, idx0, sid, leader0, req, resp, reqIdx, timeout >>

ProcSet == (ServerSet) \cup (ServerSenderSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [i \in ServerSet |-> FALSE]
        /\ sm = [i \in ServerSenderSet |-> (i) - (NumServers)]
        /\ state = [i \in ServerSet |-> Follower]
        /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
        /\ log = [i \in ServerSet |-> <<>>]
        /\ currentTerm = [i \in ServerSet |-> 1]
        /\ commitIndex = [i \in ServerSet |-> 0]
        /\ plog = [i \in ServerSet |-> <<>>]
        /\ timer = TRUE
        /\ in = TRUE
        /\ inCh = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key1]>>
        /\ outCh = defaultInitValue
        (* Process server *)
        /\ matchIndex = [self \in ServerSet |-> [i \in ServerSet |-> 0]]
        /\ votesResponded = [self \in ServerSet |-> {}]
        /\ votesGranted = [self \in ServerSet |-> {}]
        /\ leader = [self \in ServerSet |-> Nil]
        /\ idx = [self \in ServerSet |-> 1]
        /\ sm0 = [self \in ServerSet |-> [i \in KeySet |-> Nil]]
        /\ smDomain = [self \in ServerSet |-> KeySet]
        /\ newCommitIndex = [self \in ServerSet |-> 0]
        /\ m = [self \in ServerSet |-> defaultInitValue]
        /\ votedFor = [self \in ServerSet |-> Nil]
        (* Process sender *)
        /\ idx0 = [self \in ServerSenderSet |-> defaultInitValue]
        /\ sid = [self \in ServerSenderSet |-> (sm)[self]]
        (* Process client *)
        /\ leader0 = [self \in ClientSet |-> Nil]
        /\ req = [self \in ClientSet |-> defaultInitValue]
        /\ resp = [self \in ClientSet |-> defaultInitValue]
        /\ reqIdx = [self \in ClientSet |-> 0]
        /\ timeout = [self \in ClientSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ServerSenderSet -> "serverSenderLoop"
                                        [] self \in ClientSet -> "clientLoop"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 781, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          LET network0 == [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]] IN
                                            LET yielded_network6 == readMsg00 IN
                                              /\ m' = [m EXCEPT ![self] = yielded_network6]
                                              /\ Assert(((m'[self]).mdest) = (self), 
                                                        "Failure of assertion at line 789, column 13.")
                                              /\ IF ExploreFail
                                                    THEN /\ \/ /\ TRUE
                                                               /\ network' = network0
                                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                                            \/ /\ LET value00 == FALSE IN
                                                                    /\ network' = [network0 EXCEPT ![self] = [queue |-> ((network0)[self]).queue, enabled |-> value00]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                    ELSE /\ network' = network0
                                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED <<state, nextIndex, currentTerm, in, matchIndex, votesResponded, votesGranted, idx, newCommitIndex, votedFor>>
                                  \/ /\ ((state)[self]) \in ({Follower, Candidate})
                                     /\ LET yielded_network00 == Len(((network)[self]).queue) IN
                                          /\ ((yielded_network00) = (0)) /\ (timer)
                                          /\ IF (leader[self]) # (Nil)
                                                THEN /\ LET yielded_fd8 == (fd)[leader[self]] IN
                                                          /\ yielded_fd8
                                                          /\ LET i2 == self IN
                                                               /\ state' = [state EXCEPT ![i2] = Candidate]
                                                               /\ currentTerm' = [currentTerm EXCEPT ![i2] = ((currentTerm)[i2]) + (1)]
                                                               /\ votedFor' = [votedFor EXCEPT ![self] = i2]
                                                               /\ votesResponded' = [votesResponded EXCEPT ![self] = {i2}]
                                                               /\ votesGranted' = [votesGranted EXCEPT ![self] = {i2}]
                                                               /\ IF Debug
                                                                     THEN /\ PrintT(<<"ServerTimeout", i2, (currentTerm')[i2]>>)
                                                                          /\ idx' = [idx EXCEPT ![self] = 1]
                                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                     ELSE /\ idx' = [idx EXCEPT ![self] = 1]
                                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                ELSE /\ LET i3 == self IN
                                                          /\ state' = [state EXCEPT ![i3] = Candidate]
                                                          /\ currentTerm' = [currentTerm EXCEPT ![i3] = ((currentTerm)[i3]) + (1)]
                                                          /\ votedFor' = [votedFor EXCEPT ![self] = i3]
                                                          /\ votesResponded' = [votesResponded EXCEPT ![self] = {i3}]
                                                          /\ votesGranted' = [votesGranted EXCEPT ![self] = {i3}]
                                                          /\ IF Debug
                                                                THEN /\ PrintT(<<"ServerTimeout", i3, (currentTerm')[i3]>>)
                                                                     /\ idx' = [idx EXCEPT ![self] = 1]
                                                                     /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                ELSE /\ idx' = [idx EXCEPT ![self] = 1]
                                                                     /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                     /\ UNCHANGED <<network, nextIndex, in, matchIndex, newCommitIndex, m>>
                                  \/ /\ ((state)[self]) = (Leader)
                                     /\ LET i == self IN
                                          LET agreeIndexes == FindAgreeIndices((log)[i], i, matchIndex[self]) IN
                                            LET nCommitIndex == IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i] IN
                                              /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                              /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                        "Failure of assertion at line 855, column 13.")
                                              /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                     /\ UNCHANGED <<network, state, nextIndex, currentTerm, in, matchIndex, votesResponded, votesGranted, idx, m, votedFor>>
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
                                     /\ UNCHANGED <<network, currentTerm, votesResponded, votesGranted, idx, newCommitIndex, m, votedFor>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                               /\ UNCHANGED << network, state, nextIndex, 
                                               currentTerm, in, matchIndex, 
                                               votesResponded, votesGranted, 
                                               idx, newCommitIndex, m, 
                                               votedFor >>
                    /\ UNCHANGED << fd, sm, log, commitIndex, plog, timer, 
                                    inCh, outCh, leader, sm0, smDomain, idx0, 
                                    sid, leader0, req, resp, reqIdx, timeout >>

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
                                                                "Failure of assertion at line 888, column 13.")
                                                      /\ IF grant
                                                            THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                                 /\ \/ /\ LET value15 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                            /\ ((network)[j]).enabled
                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value15), enabled |-> ((network)[j]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                    \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                            /\ yielded_fd00
                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ \/ /\ LET value16 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                            /\ ((network)[j]).enabled
                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]]
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
                                                              "Failure of assertion at line 929, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![self] = j]
                                                               /\ \/ /\ LET value17 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                          /\ yielded_fd02
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                          ELSE /\ \/ /\ LET value18 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                          /\ yielded_fd03
                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << state, currentTerm >>
                              /\ UNCHANGED << nextIndex, log, commitIndex, 
                                              plog, matchIndex, votesResponded, 
                                              votesGranted, leader, sm0, 
                                              smDomain >>
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
                                                                                "Failure of assertion at line 975, column 17.")
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
                                                                                "Failure of assertion at line 993, column 17.")
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
                                                         log, commitIndex, 
                                                         plog, matchIndex, 
                                                         leader, sm0, smDomain >>
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
                                                                                       "Failure of assertion at line 1016, column 19.")
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
                                                                                                                   commitIndex, 
                                                                                                                   plog, 
                                                                                                                   sm0, 
                                                                                                                   smDomain >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 1034, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log4 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                     LET value30 == [cmd |-> LogPop] IN
                                                                                                                       IF ((value30).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog4 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value30).entries)] IN
                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                       THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                            /\ LET value40 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                 IF ((value40).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog4 EXCEPT ![i] = ((plog4)[i]) \o ((value40).entries)]
                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                               THEN /\ LET result16 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                         /\ sm0' = [sm0 EXCEPT ![self] = (result16)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![self] = (result16)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                         /\ \/ /\ LET value50 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd20 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd20
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                    sm0, 
                                                                                                                                                                                    smDomain >>
                                                                                                                                                    ELSE /\ IF ((value40).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))]
                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result17 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result17)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result17)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value51 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd21 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd21
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result18 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result18)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result18)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value52 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ plog' = plog4
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd22 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd22
                                                                                                                                                                                               /\ plog' = plog4
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ plog' = plog4
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                  THEN /\ LET result19 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                            /\ sm0' = [sm0 EXCEPT ![self] = (result19)[1]]
                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![self] = (result19)[2]]
                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                            /\ \/ /\ LET value53 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                       /\ plog' = plog4
                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               \/ /\ LET yielded_fd23 == (fd)[j] IN
                                                                                                                                                                       /\ yielded_fd23
                                                                                                                                                                       /\ plog' = plog4
                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                  ELSE /\ plog' = plog4
                                                                                                                                                       /\ log' = log4
                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                       /\ UNCHANGED << network, 
                                                                                                                                                                       commitIndex, 
                                                                                                                                                                       sm0, 
                                                                                                                                                                       smDomain >>
                                                                                                                          ELSE /\ IF ((value30).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog5 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                  THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                       /\ LET value41 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                            IF ((value41).cmd) = (LogConcat)
                                                                                                                                                               THEN /\ plog' = [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value41).entries)]
                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result20 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result20)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result20)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value54 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd24 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd24
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                                               ELSE /\ IF ((value41).cmd) = (LogPop)
                                                                                                                                                                          THEN /\ plog' = [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))]
                                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result21 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result21)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result21)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                               /\ \/ /\ LET value55 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd25 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd25
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                                          sm0, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result22 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result22)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result22)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                               /\ \/ /\ LET value56 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                          /\ plog' = plog5
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd26 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd26
                                                                                                                                                                                                          /\ plog' = plog5
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                                     ELSE /\ plog' = plog5
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                                          sm0, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                             THEN /\ LET result23 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                       /\ sm0' = [sm0 EXCEPT ![self] = (result23)[1]]
                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![self] = (result23)[2]]
                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                       /\ \/ /\ LET value57 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                  /\ plog' = plog5
                                                                                                                                                                                  /\ log' = log4
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          \/ /\ LET yielded_fd27 == (fd)[j] IN
                                                                                                                                                                                  /\ yielded_fd27
                                                                                                                                                                                  /\ plog' = plog5
                                                                                                                                                                                  /\ log' = log4
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                             ELSE /\ plog' = plog5
                                                                                                                                                                  /\ log' = log4
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                  commitIndex, 
                                                                                                                                                                                  sm0, 
                                                                                                                                                                                  smDomain >>
                                                                                                                                     ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ LET value42 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                          IF ((value42).cmd) = (LogConcat)
                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value42).entries)]
                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                        THEN /\ LET result24 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                  /\ sm0' = [sm0 EXCEPT ![self] = (result24)[1]]
                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![self] = (result24)[2]]
                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                  /\ \/ /\ LET value58 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     \/ /\ LET yielded_fd28 == (fd)[j] IN
                                                                                                                                                                                             /\ yielded_fd28
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                             sm0, 
                                                                                                                                                                                             smDomain >>
                                                                                                                                                             ELSE /\ IF ((value42).cmd) = (LogPop)
                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result25 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result25)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result25)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                             /\ \/ /\ LET value59 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd29 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd29
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                                        sm0, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result26 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result26)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result26)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                             /\ \/ /\ LET value510 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd210 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd210
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                                        sm0, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                           THEN /\ LET result27 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                     /\ sm0' = [sm0 EXCEPT ![self] = (result27)[1]]
                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![self] = (result27)[2]]
                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                     /\ \/ /\ LET value511 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ log' = log4
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        \/ /\ LET yielded_fd211 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd211
                                                                                                                                                                                /\ log' = log4
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = log4
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                /\ UNCHANGED << network, 
                                                                                                                                                                                commitIndex, 
                                                                                                                                                                                sm0, 
                                                                                                                                                                                smDomain >>
                                                                                                                                                     /\ plog' = plog
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                           /\ LET value43 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                IF ((value43).cmd) = (LogConcat)
                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value43).entries)]
                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                              THEN /\ LET result28 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result28)[1]]
                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result28)[2]]
                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                        /\ \/ /\ LET value512 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           \/ /\ LET yielded_fd212 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd212
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                   commitIndex, 
                                                                                                                                                                   sm0, 
                                                                                                                                                                   smDomain >>
                                                                                                                                   ELSE /\ IF ((value43).cmd) = (LogPop)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                         THEN /\ LET result29 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result29)[1]]
                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result29)[2]]
                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                   /\ \/ /\ LET value513 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      \/ /\ LET yielded_fd213 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd213
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                                              commitIndex, 
                                                                                                                                                                              sm0, 
                                                                                                                                                                              smDomain >>
                                                                                                                                              ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                         THEN /\ LET result30 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result30)[1]]
                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result30)[2]]
                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                   /\ \/ /\ LET value514 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      \/ /\ LET yielded_fd214 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd214
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                                              commitIndex, 
                                                                                                                                                                              sm0, 
                                                                                                                                                                              smDomain >>
                                                                                                                                                   /\ plog' = plog
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ LET result31 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                           /\ sm0' = [sm0 EXCEPT ![self] = (result31)[1]]
                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![self] = (result31)[2]]
                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                           /\ \/ /\ LET value515 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              \/ /\ LET yielded_fd215 == (fd)[j] IN
                                                                                                                                                      /\ yielded_fd215
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex, 
                                                                                                                                                      sm0, 
                                                                                                                                                      smDomain >>
                                                                                                                           /\ UNCHANGED << log, 
                                                                                                                                           plog >>
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
                                                                                                                   commitIndex, 
                                                                                                                   plog, 
                                                                                                                   sm0, 
                                                                                                                   smDomain >>
                                                                                              ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                             "Failure of assertion at line 1503, column 23.")
                                                                                                   /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                        IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                           THEN /\ LET log5 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                     LET value31 == [cmd |-> LogPop] IN
                                                                                                                       IF ((value31).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog6 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value31).entries)] IN
                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                       THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                            /\ LET value44 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                 IF ((value44).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog6 EXCEPT ![i] = ((plog6)[i]) \o ((value44).entries)]
                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                               THEN /\ LET result32 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                         /\ sm0' = [sm0 EXCEPT ![self] = (result32)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![self] = (result32)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                         /\ \/ /\ LET value516 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd216 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd216
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ state' = state1
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                    sm0, 
                                                                                                                                                                                    smDomain >>
                                                                                                                                                    ELSE /\ IF ((value44).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))]
                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result33 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result33)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result33)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value517 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd217 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd217
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ state' = state1
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result34 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result34)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result34)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value518 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ plog' = plog6
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd218 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd218
                                                                                                                                                                                               /\ plog' = plog6
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ plog' = plog6
                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                  THEN /\ LET result35 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                            /\ sm0' = [sm0 EXCEPT ![self] = (result35)[1]]
                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![self] = (result35)[2]]
                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                            /\ \/ /\ LET value519 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                       /\ plog' = plog6
                                                                                                                                                                       /\ log' = log5
                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               \/ /\ LET yielded_fd219 == (fd)[j] IN
                                                                                                                                                                       /\ yielded_fd219
                                                                                                                                                                       /\ plog' = plog6
                                                                                                                                                                       /\ log' = log5
                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                  ELSE /\ plog' = plog6
                                                                                                                                                       /\ log' = log5
                                                                                                                                                       /\ state' = state1
                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                       /\ UNCHANGED << network, 
                                                                                                                                                                       commitIndex, 
                                                                                                                                                                       sm0, 
                                                                                                                                                                       smDomain >>
                                                                                                                          ELSE /\ IF ((value31).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog7 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                  THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                       /\ LET value45 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                            IF ((value45).cmd) = (LogConcat)
                                                                                                                                                               THEN /\ plog' = [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value45).entries)]
                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                          THEN /\ LET result36 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result36)[1]]
                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result36)[2]]
                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                    /\ \/ /\ LET value520 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       \/ /\ LET yielded_fd220 == (fd)[j] IN
                                                                                                                                                                                               /\ yielded_fd220
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                          ELSE /\ state' = state1
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                               sm0, 
                                                                                                                                                                                               smDomain >>
                                                                                                                                                               ELSE /\ IF ((value45).cmd) = (LogPop)
                                                                                                                                                                          THEN /\ plog' = [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))]
                                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result37 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result37)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result37)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                               /\ \/ /\ LET value521 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd221 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd221
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                                     ELSE /\ state' = state1
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                                          sm0, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result38 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result38)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result38)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                               /\ \/ /\ LET value522 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                          /\ plog' = plog7
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd222 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd222
                                                                                                                                                                                                          /\ plog' = plog7
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                                     ELSE /\ plog' = plog7
                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                                          sm0, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                             THEN /\ LET result39 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                       /\ sm0' = [sm0 EXCEPT ![self] = (result39)[1]]
                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![self] = (result39)[2]]
                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                       /\ \/ /\ LET value523 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                  /\ plog' = plog7
                                                                                                                                                                                  /\ log' = log5
                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          \/ /\ LET yielded_fd223 == (fd)[j] IN
                                                                                                                                                                                  /\ yielded_fd223
                                                                                                                                                                                  /\ plog' = plog7
                                                                                                                                                                                  /\ log' = log5
                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                             ELSE /\ plog' = plog7
                                                                                                                                                                  /\ log' = log5
                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                  commitIndex, 
                                                                                                                                                                                  sm0, 
                                                                                                                                                                                  smDomain >>
                                                                                                                                     ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ LET value46 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                          IF ((value46).cmd) = (LogConcat)
                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value46).entries)]
                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                        THEN /\ LET result40 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                  /\ sm0' = [sm0 EXCEPT ![self] = (result40)[1]]
                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![self] = (result40)[2]]
                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                  /\ \/ /\ LET value524 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     \/ /\ LET yielded_fd224 == (fd)[j] IN
                                                                                                                                                                                             /\ yielded_fd224
                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                        ELSE /\ state' = state1
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                             sm0, 
                                                                                                                                                                                             smDomain >>
                                                                                                                                                             ELSE /\ IF ((value46).cmd) = (LogPop)
                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result41 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result41)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result41)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                             /\ \/ /\ LET value525 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd225 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd225
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                                        sm0, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                        ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result42 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result42)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result42)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                             /\ \/ /\ LET value526 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd226 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd226
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                                        sm0, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                           THEN /\ LET result43 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                     /\ sm0' = [sm0 EXCEPT ![self] = (result43)[1]]
                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![self] = (result43)[2]]
                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                     /\ \/ /\ LET value527 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ log' = log5
                                                                                                                                                                                /\ state' = state1
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        \/ /\ LET yielded_fd227 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd227
                                                                                                                                                                                /\ log' = log5
                                                                                                                                                                                /\ state' = state1
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = log5
                                                                                                                                                                /\ state' = state1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                /\ UNCHANGED << network, 
                                                                                                                                                                                commitIndex, 
                                                                                                                                                                                sm0, 
                                                                                                                                                                                smDomain >>
                                                                                                                                                     /\ plog' = plog
                                                                                                           ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                           /\ LET value47 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                IF ((value47).cmd) = (LogConcat)
                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value47).entries)]
                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                              THEN /\ LET result44 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result44)[1]]
                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result44)[2]]
                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                        /\ \/ /\ LET value528 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           \/ /\ LET yielded_fd228 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd228
                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ state' = state1
                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                   commitIndex, 
                                                                                                                                                                   sm0, 
                                                                                                                                                                   smDomain >>
                                                                                                                                   ELSE /\ IF ((value47).cmd) = (LogPop)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                         THEN /\ LET result45 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result45)[1]]
                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result45)[2]]
                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                   /\ \/ /\ LET value529 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      \/ /\ LET yielded_fd229 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd229
                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ state' = state1
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                                              commitIndex, 
                                                                                                                                                                              sm0, 
                                                                                                                                                                              smDomain >>
                                                                                                                                              ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                         THEN /\ LET result46 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result46)[1]]
                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result46)[2]]
                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                   /\ \/ /\ LET value530 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      \/ /\ LET yielded_fd230 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd230
                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ state' = state1
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                                              commitIndex, 
                                                                                                                                                                              sm0, 
                                                                                                                                                                              smDomain >>
                                                                                                                                                   /\ plog' = plog
                                                                                                                      ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                 THEN /\ LET result47 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                           /\ sm0' = [sm0 EXCEPT ![self] = (result47)[1]]
                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![self] = (result47)[2]]
                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                           /\ \/ /\ LET value531 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                      /\ state' = state1
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              \/ /\ LET yielded_fd231 == (fd)[j] IN
                                                                                                                                                      /\ yielded_fd231
                                                                                                                                                      /\ state' = state1
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                 ELSE /\ state' = state1
                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                      /\ UNCHANGED << network, 
                                                                                                                                                      commitIndex, 
                                                                                                                                                      sm0, 
                                                                                                                                                      smDomain >>
                                                                                                                           /\ UNCHANGED << log, 
                                                                                                                                           plog >>
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                                                  "Failure of assertion at line 2012, column 17.")
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
                                                                                                              commitIndex, 
                                                                                                              plog, 
                                                                                                              sm0, 
                                                                                                              smDomain >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2030, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                LET value32 == [cmd |-> LogPop] IN
                                                                                                                  IF ((value32).cmd) = (LogConcat)
                                                                                                                     THEN /\ LET plog8 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)] IN
                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                  THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                       /\ LET value48 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                            IF ((value48).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value48).entries)]
                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                          THEN /\ LET result48 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result48)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result48)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                    /\ \/ /\ LET value532 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd232 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd232
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               commitIndex, 
                                                                                                                                                                               sm0, 
                                                                                                                                                                               smDomain >>
                                                                                                                                               ELSE /\ IF ((value48).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result49 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result49)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result49)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value533 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd233 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd233
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result50 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result50)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result50)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value534 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd234 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd234
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog8
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET result51 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                       /\ sm0' = [sm0 EXCEPT ![self] = (result51)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![self] = (result51)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                       /\ \/ /\ LET value535 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd235 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd235
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog8
                                                                                                                                                  /\ log' = log6
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  commitIndex, 
                                                                                                                                                                  sm0, 
                                                                                                                                                                  smDomain >>
                                                                                                                     ELSE /\ IF ((value32).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value49 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value49).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value49).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result52 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result52)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result52)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value536 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd236 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd236
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF ((value49).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result53 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                          /\ sm0' = [sm0 EXCEPT ![self] = (result53)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![self] = (result53)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                          /\ \/ /\ LET value537 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd237 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd237
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm0, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result54 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                          /\ sm0' = [sm0 EXCEPT ![self] = (result54)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![self] = (result54)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                          /\ \/ /\ LET value538 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd238 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd238
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog9
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm0, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET result55 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                  /\ sm0' = [sm0 EXCEPT ![self] = (result55)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![self] = (result55)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                  /\ \/ /\ LET value539 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd239 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd239
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog9
                                                                                                                                                             /\ log' = log6
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             commitIndex, 
                                                                                                                                                                             sm0, 
                                                                                                                                                                             smDomain >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value410 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value410).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value410).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET result56 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result56)[1]]
                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result56)[2]]
                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                             /\ \/ /\ LET value540 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd240 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd240
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                        sm0, 
                                                                                                                                                                                        smDomain >>
                                                                                                                                                        ELSE /\ IF ((value410).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result57 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result57)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result57)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                        /\ \/ /\ LET value541 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd241 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd241
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm0, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result58 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result58)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result58)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                        /\ \/ /\ LET value542 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd242 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd242
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm0, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET result59 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                /\ sm0' = [sm0 EXCEPT ![self] = (result59)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![self] = (result59)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                /\ \/ /\ LET value543 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd243 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd243
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log6
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           commitIndex, 
                                                                                                                                                                           sm0, 
                                                                                                                                                                           smDomain >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value411 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value411).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value411).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET result60 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result60)[1]]
                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result60)[2]]
                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                   /\ \/ /\ LET value544 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd244 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd244
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              commitIndex, 
                                                                                                                                                              sm0, 
                                                                                                                                                              smDomain >>
                                                                                                                              ELSE /\ IF ((value411).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result61 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                              /\ sm0' = [sm0 EXCEPT ![self] = (result61)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![self] = (result61)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                              /\ \/ /\ LET value545 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd245 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd245
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm0, 
                                                                                                                                                                         smDomain >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result62 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                              /\ sm0' = [sm0 EXCEPT ![self] = (result62)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![self] = (result62)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                              /\ \/ /\ LET value546 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd246 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd246
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm0, 
                                                                                                                                                                         smDomain >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET result63 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                      /\ sm0' = [sm0 EXCEPT ![self] = (result63)[1]]
                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![self] = (result63)[2]]
                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value547 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd247 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd247
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex, 
                                                                                                                                                 sm0, 
                                                                                                                                                 smDomain >>
                                                                                                                      /\ UNCHANGED << log, 
                                                                                                                                      plog >>
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
                                                                                                              commitIndex, 
                                                                                                              plog, 
                                                                                                              sm0, 
                                                                                                              smDomain >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2497, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                LET value33 == [cmd |-> LogPop] IN
                                                                                                                  IF ((value33).cmd) = (LogConcat)
                                                                                                                     THEN /\ LET plog10 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)] IN
                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                  THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                       /\ LET value412 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                            IF ((value412).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value412).entries)]
                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                          THEN /\ LET result64 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                    /\ sm0' = [sm0 EXCEPT ![self] = (result64)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![self] = (result64)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                    /\ \/ /\ LET value548 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd248 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd248
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               commitIndex, 
                                                                                                                                                                               sm0, 
                                                                                                                                                                               smDomain >>
                                                                                                                                               ELSE /\ IF ((value412).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result65 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result65)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result65)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value549 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd249 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd249
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result66 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result66)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result66)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value550 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd250 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd250
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog10
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET result67 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                       /\ sm0' = [sm0 EXCEPT ![self] = (result67)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![self] = (result67)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                       /\ \/ /\ LET value551 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd251 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd251
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog10
                                                                                                                                                  /\ log' = log7
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  commitIndex, 
                                                                                                                                                                  sm0, 
                                                                                                                                                                  smDomain >>
                                                                                                                     ELSE /\ IF ((value33).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value413 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value413).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value413).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result68 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                               /\ sm0' = [sm0 EXCEPT ![self] = (result68)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![self] = (result68)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                               /\ \/ /\ LET value552 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd252 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd252
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm0, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF ((value413).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result69 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                          /\ sm0' = [sm0 EXCEPT ![self] = (result69)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![self] = (result69)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                          /\ \/ /\ LET value553 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd253 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd253
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm0, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result70 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                          /\ sm0' = [sm0 EXCEPT ![self] = (result70)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![self] = (result70)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                          /\ \/ /\ LET value554 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd254 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd254
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog11
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm0, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET result71 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                  /\ sm0' = [sm0 EXCEPT ![self] = (result71)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![self] = (result71)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                  /\ \/ /\ LET value555 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd255 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd255
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog11
                                                                                                                                                             /\ log' = log7
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             commitIndex, 
                                                                                                                                                                             sm0, 
                                                                                                                                                                             smDomain >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value414 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value414).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value414).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET result72 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                             /\ sm0' = [sm0 EXCEPT ![self] = (result72)[1]]
                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![self] = (result72)[2]]
                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                             /\ \/ /\ LET value556 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd256 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd256
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                        sm0, 
                                                                                                                                                                                        smDomain >>
                                                                                                                                                        ELSE /\ IF ((value414).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result73 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result73)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result73)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                        /\ \/ /\ LET value557 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd257 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd257
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm0, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result74 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                                        /\ sm0' = [sm0 EXCEPT ![self] = (result74)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (result74)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                                        /\ \/ /\ LET value558 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd258 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd258
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm0, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET result75 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                                /\ sm0' = [sm0 EXCEPT ![self] = (result75)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![self] = (result75)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                                /\ \/ /\ LET value559 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd259 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd259
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log7
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           commitIndex, 
                                                                                                                                                                           sm0, 
                                                                                                                                                                           smDomain >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value415 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value415).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value415).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET result76 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                   /\ sm0' = [sm0 EXCEPT ![self] = (result76)[1]]
                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (result76)[2]]
                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                   /\ \/ /\ LET value560 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd260 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd260
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              commitIndex, 
                                                                                                                                                              sm0, 
                                                                                                                                                              smDomain >>
                                                                                                                              ELSE /\ IF ((value415).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result77 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                              /\ sm0' = [sm0 EXCEPT ![self] = (result77)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![self] = (result77)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                              /\ \/ /\ LET value561 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd261 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd261
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm0, 
                                                                                                                                                                         smDomain >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result78 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                                              /\ sm0' = [sm0 EXCEPT ![self] = (result78)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![self] = (result78)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                                              /\ \/ /\ LET value562 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd262 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd262
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm0, 
                                                                                                                                                                         smDomain >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET result79 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, sm0[self], smDomain[self]) IN
                                                                                                                                      /\ sm0' = [sm0 EXCEPT ![self] = (result79)[1]]
                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![self] = (result79)[2]]
                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = (m[self]).mcommitIndex]
                                                                                                                                      /\ \/ /\ LET value563 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd263 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd263
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex, 
                                                                                                                                                 sm0, 
                                                                                                                                                 smDomain >>
                                                                                                                      /\ UNCHANGED << log, 
                                                                                                                                      plog >>
                                                                                   /\ state' = state
                                                               /\ UNCHANGED << currentTerm, 
                                                                               votedFor >>
                                                    /\ UNCHANGED << nextIndex, 
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
                                                                                                      "Failure of assertion at line 2964, column 21.")
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
                                                                                                      "Failure of assertion at line 2983, column 21.")
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
                                                               /\ UNCHANGED << network, 
                                                                               log, 
                                                                               plog >>
                                                          ELSE /\ IF (((m[self]).mtype) = (ClientPutRequest)) \/ (((m[self]).mtype) = (ClientGetRequest))
                                                                     THEN /\ IF ((state)[self]) = (Leader)
                                                                                THEN /\ LET entry == [term |-> (currentTerm)[self], cmd |-> (m[self]).mcmd, client |-> (m[self]).msource] IN
                                                                                          /\ log' = [log EXCEPT ![self] = Append((log)[self], entry)]
                                                                                          /\ LET value60 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                               IF ((value60).cmd) = (LogConcat)
                                                                                                  THEN /\ plog' = [plog EXCEPT ![self] = ((plog)[self]) \o ((value60).entries)]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ IF ((value60).cmd) = (LogPop)
                                                                                                             THEN /\ plog' = [plog EXCEPT ![self] = SubSeq((plog)[self], 1, (Len((plog)[self])) - (1))]
                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                  /\ plog' = plog
                                                                                     /\ UNCHANGED network
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            LET respType == IF (((m[self]).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                              LET value70 == [mtype |-> respType, msuccess |-> FALSE, mresponse |-> Nil, mleaderHint |-> leader[self], msource |-> i, mdest |-> j] IN
                                                                                                /\ ((network)[j]).enabled
                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value70), enabled |-> ((network)[j]).enabled]]
                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << log, 
                                                                                                     plog >>
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED << network, 
                                                                                          log, 
                                                                                          plog >>
                                                               /\ UNCHANGED << state, 
                                                                               nextIndex, 
                                                                               currentTerm, 
                                                                               matchIndex, 
                                                                               votedFor >>
                                                    /\ UNCHANGED << commitIndex, 
                                                                    leader, 
                                                                    sm0, 
                                                                    smDomain >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted >>
                   /\ UNCHANGED << fd, sm, timer, in, inCh, outCh, idx, 
                                   newCommitIndex, m, idx0, sid, leader0, req, 
                                   resp, reqIdx, timeout >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx[self]) <= (NumServers)
                               THEN /\ IF (idx[self]) # (self)
                                          THEN /\ \/ /\ LET value80 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[self], mlastLogTerm |-> LastTerm((log)[self]), mlastLogIndex |-> Len((log)[self]), msource |-> self, mdest |-> idx[self]] IN
                                                          /\ ((network)[idx[self]]).enabled
                                                          /\ (Len(((network)[idx[self]]).queue)) < (BufferSize)
                                                          /\ LET network1 == [network EXCEPT ![idx[self]] = [queue |-> Append(((network)[idx[self]]).queue, value80), enabled |-> ((network)[idx[self]]).enabled]] IN
                                                               /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                               /\ IF ExploreFail
                                                                     THEN /\ \/ /\ TRUE
                                                                                /\ network' = network1
                                                                                /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                             \/ /\ LET value90 == FALSE IN
                                                                                     /\ network' = [network1 EXCEPT ![self] = [queue |-> ((network1)[self]).queue, enabled |-> value90]]
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
                                                                        \/ /\ LET value91 == FALSE IN
                                                                                /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value91]]
                                                                                /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                     /\ UNCHANGED network
                                          ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                               /\ IF ExploreFail
                                                     THEN /\ \/ /\ TRUE
                                                                /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                                /\ UNCHANGED network
                                                             \/ /\ LET value92 == FALSE IN
                                                                     /\ network' = [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value92]]
                                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                          /\ UNCHANGED network
                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                    /\ UNCHANGED << network, idx >>
                         /\ UNCHANGED << fd, sm, state, nextIndex, log, 
                                         currentTerm, commitIndex, plog, timer, 
                                         in, inCh, outCh, matchIndex, 
                                         votesResponded, votesGranted, leader, 
                                         sm0, smDomain, newCommitIndex, m, 
                                         votedFor, idx0, sid, leader0, req, 
                                         resp, reqIdx, timeout >>

applyLoop(self) == /\ pc[self] = "applyLoop"
                   /\ IF ((commitIndex)[self]) < (newCommitIndex[self])
                         THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = ((commitIndex)[self]) + (1)]
                              /\ LET i == self IN
                                   LET k == (commitIndex')[i] IN
                                     LET entry == ((log)[i])[k] IN
                                       LET cmd == (entry).cmd IN
                                         LET respType == IF ((cmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                           IF ((cmd).type) = (Put)
                                              THEN /\ sm0' = [sm0 EXCEPT ![self] = (sm0[self]) @@ (((cmd).key) :> ((cmd).value))]
                                                   /\ smDomain' = [smDomain EXCEPT ![self] = (smDomain[self]) \union ({(cmd).key})]
                                                   /\ LET reqOk == ((cmd).key) \in (smDomain'[self]) IN
                                                        LET value100 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN (sm0'[self])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value100), enabled |-> ((network)[(entry).client]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                              ELSE /\ LET reqOk == ((cmd).key) \in (smDomain[self]) IN
                                                        LET value101 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN (sm0[self])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value101), enabled |-> ((network)[(entry).client]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                                   /\ UNCHANGED << sm0, 
                                                                   smDomain >>
                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                              /\ UNCHANGED << network, commitIndex, sm0, 
                                              smDomain >>
                   /\ UNCHANGED << fd, sm, state, nextIndex, log, currentTerm, 
                                   plog, timer, in, inCh, outCh, matchIndex, 
                                   votesResponded, votesGranted, leader, idx, 
                                   newCommitIndex, m, votedFor, idx0, sid, 
                                   leader0, req, resp, reqIdx, timeout >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value110 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value110]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, sm, state, nextIndex, log, 
                                   currentTerm, commitIndex, plog, timer, in, 
                                   inCh, outCh, matchIndex, votesResponded, 
                                   votesGranted, leader, idx, sm0, smDomain, 
                                   newCommitIndex, m, votedFor, idx0, sid, 
                                   leader0, req, resp, reqIdx, timeout >>

server(self) == serverLoop(self) \/ handleMsg(self)
                   \/ requestVoteLoop(self) \/ applyLoop(self)
                   \/ failLabel(self)

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
                                          log, currentTerm, commitIndex, plog, 
                                          timer, in, inCh, outCh, matchIndex, 
                                          votesResponded, votesGranted, leader, 
                                          idx, sm0, smDomain, newCommitIndex, 
                                          m, votedFor, sid, leader0, req, resp, 
                                          reqIdx, timeout >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ LET yielded_network2 == ((network)[sid[self]]).enabled IN
                                IF ((yielded_network2) /\ (((state)[sid[self]]) = (Leader))) /\ ((idx0[self]) <= (NumServers))
                                   THEN /\ IF (idx0[self]) # (sid[self])
                                              THEN /\ LET prevLogIndex1 == (((nextIndex)[sid[self]])[idx0[self]]) - (1) IN
                                                        LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN (((log)[sid[self]])[prevLogIndex1]).term ELSE 0 IN
                                                          LET lastEntry1 == Min({Len((log)[sid[self]]), ((nextIndex)[sid[self]])[idx0[self]]}) IN
                                                            LET entries1 == SubSeq((log)[sid[self]], ((nextIndex)[sid[self]])[idx0[self]], lastEntry1) IN
                                                              \/ /\ LET value120 == [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[sid[self]], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[sid[self]], lastEntry1}), msource |-> sid[self], mdest |-> idx0[self]] IN
                                                                      /\ ((network)[idx0[self]]).enabled
                                                                      /\ (Len(((network)[idx0[self]]).queue)) < (BufferSize)
                                                                      /\ network' = [network EXCEPT ![idx0[self]] = [queue |-> Append(((network)[idx0[self]]).queue, value120), enabled |-> ((network)[idx0[self]]).enabled]]
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
                                           currentTerm, commitIndex, plog, 
                                           timer, in, inCh, outCh, matchIndex, 
                                           votesResponded, votesGranted, 
                                           leader, idx, sm0, smDomain, 
                                           newCommitIndex, m, votedFor, sid, 
                                           leader0, req, resp, reqIdx, timeout >>

sender(self) == serverSenderLoop(self) \/ appendEntriesLoop(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ (Len(inCh)) > (0)
                                     /\ LET res00 == Head(inCh) IN
                                          /\ inCh' = Tail(inCh)
                                          /\ LET yielded_inCh0 == res00 IN
                                               /\ req' = [req EXCEPT ![self] = yielded_inCh0]
                                               /\ reqIdx' = [reqIdx EXCEPT ![self] = (reqIdx[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                     /\ UNCHANGED <<network, resp>>
                                  \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 3215, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg10 == Head(((network)[self]).queue) IN
                                          /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                          /\ LET yielded_network30 == readMsg10 IN
                                               /\ resp' = [resp EXCEPT ![self] = yielded_network30]
                                               /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                     /\ UNCHANGED <<inCh, req, reqIdx>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, inCh, req, resp, 
                                               reqIdx >>
                    /\ UNCHANGED << fd, sm, state, nextIndex, log, currentTerm, 
                                    commitIndex, plog, timer, in, outCh, 
                                    matchIndex, votesResponded, votesGranted, 
                                    leader, idx, sm0, smDomain, newCommitIndex, 
                                    m, votedFor, idx0, sid, leader0, timeout >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (leader0[self]) = (Nil)
                      THEN /\ \E srv1 \in ServerSet:
                                /\ leader0' = [leader0 EXCEPT ![self] = srv1]
                                /\ IF Debug
                                      THEN /\ PrintT(<<"clientSndReq", self, leader0'[self], req[self]>>)
                                           /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value130 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value130), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd50 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd50
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value140 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value140), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                    \/ /\ LET yielded_fd60 == (fd)[leader0'[self]] IN
                                                                            /\ yielded_fd60
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                 /\ UNCHANGED network
                                      ELSE /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value131 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value131), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd51 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd51
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value141 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value141), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                    \/ /\ LET yielded_fd61 == (fd)[leader0'[self]] IN
                                                                            /\ yielded_fd61
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                 /\ UNCHANGED network
                      ELSE /\ IF Debug
                                 THEN /\ PrintT(<<"clientSndReq", self, leader0[self], req[self]>>)
                                      /\ IF ((req[self]).type) = (Put)
                                            THEN /\ \/ /\ LET value132 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value132), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd52 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd52
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value142 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value142), enabled |-> ((network)[leader0[self]]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                               \/ /\ LET yielded_fd62 == (fd)[leader0[self]] IN
                                                                       /\ yielded_fd62
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED network
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                 ELSE /\ IF ((req[self]).type) = (Put)
                                            THEN /\ \/ /\ LET value133 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value133), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd53 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd53
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value143 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value143), enabled |-> ((network)[leader0[self]]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                               \/ /\ LET yielded_fd63 == (fd)[leader0[self]] IN
                                                                       /\ yielded_fd63
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED network
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                           /\ UNCHANGED leader0
                /\ UNCHANGED << fd, sm, state, nextIndex, log, currentTerm, 
                                commitIndex, plog, timer, in, inCh, outCh, 
                                matchIndex, votesResponded, votesGranted, 
                                leader, idx, sm0, smDomain, newCommitIndex, m, 
                                votedFor, idx0, sid, req, resp, reqIdx, 
                                timeout >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 3377, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg20 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network40 == readMsg20 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network40]
                                 /\ IF Debug
                                       THEN /\ PrintT(<<"resp", resp'[self]>>)
                                            /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3385, column 15.")
                                            /\ IF ((resp'[self]).msuccess) /\ ((((resp'[self]).mresponse).idx) # (reqIdx[self]))
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << outCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3390, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ outCh' = outCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3394, column 19.")
                                                                  /\ outCh' = resp'[self]
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                       ELSE /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3400, column 15.")
                                            /\ IF ((resp'[self]).msuccess) /\ ((((resp'[self]).mresponse).idx) # (reqIdx[self]))
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << outCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3405, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ outCh' = outCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3409, column 19.")
                                                                  /\ outCh' = resp'[self]
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                    \/ /\ LET yielded_fd70 == (fd)[leader0[self]] IN
                            LET yielded_network50 == Len(((network)[self]).queue) IN
                              /\ ((yielded_fd70) /\ ((yielded_network50) = (0))) \/ (timeout[self])
                              /\ leader0' = [leader0 EXCEPT ![self] = Nil]
                              /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                       /\ UNCHANGED <<network, outCh, resp>>
                 /\ UNCHANGED << fd, sm, state, nextIndex, log, currentTerm, 
                                 commitIndex, plog, timer, in, inCh, 
                                 matchIndex, votesResponded, votesGranted, 
                                 leader, idx, sm0, smDomain, newCommitIndex, m, 
                                 votedFor, idx0, sid, req, reqIdx, timeout >>

client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

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

ApplyLogOK == \A i, j \in ServerSet:
                    commitIndex[i] = commitIndex[j] => 
                        /\ sm0[i] = sm0[j]
                        /\ smDomain[i] = smDomain[j]

plogOK == \A i \in ServerSet: log[i] = plog[i]

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
