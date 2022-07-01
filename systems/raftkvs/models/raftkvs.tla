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
CONSTANT NumHandlers

CONSTANT BufferSize

CONSTANT MaxTerm
CONSTANT MaxCommitIndex

CONSTANT MaxNodeFail

CONSTANT LogConcat
CONSTANT LogPop

CONSTANT LeaderTimeoutReset

\* This is only used for model checking / simulation
CONSTANT NumRequests

Nil == 0

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

RECURSIVE FindMaxAgreeIndexRec(_, _, _, _)

isQuorum(s) == Cardinality(s) * 2 > NumServers
ServerSet   == 1..NumServers

FindMaxAgreeIndex(logLocal, i, matchIndex) ==
    FindMaxAgreeIndexRec(logLocal, i, matchIndex, Len(logLocal))

FindMaxAgreeIndexRec(logLocal, i, matchIndex, index) ==
    IF index = 0 THEN Nil
    ELSE
        IF isQuorum({i} \cup {k \in ServerSet : matchIndex[k] >= index})
        THEN index
        ELSE FindMaxAgreeIndexRec(logLocal, i, matchIndex, index - 1)

RECURSIVE ApplyLog(_, _, _, _, _)

Put == "put"
Get == "get"

ApplyLogEntry(xentry, xsm, xsmDomain) ==
    LET cmd == xentry.cmd
    IN IF cmd.type = Put
       THEN <<xsm @@ (cmd.key :> cmd.value), xsmDomain \cup {cmd.key}>>
       ELSE <<xsm, xsmDomain>>

\* applies range [start, end] from the log to the state machine
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

        LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

        ServerRequestVoteSet        == (1*NumServers+1)..(2*NumServers)
        ServerAppendEntriesSet      == (2*NumServers+1)..(3*NumServers)
        ServerAdvanceCommitIndexSet == (3*NumServers+1)..(4*NumServers)
        ServerBecomeLeaderSet       == (4*NumServers+1)..(5*NumServers)
        ServerHandlerSet            == (5*NumServers+1)..(5*NumServers+NumHandlers*NumServers)

        \* TODO: MaxNodeFail \in Int /\ 1 <= MaxNodeFail <= NumServers?
        \* TODO: change ServerCrasherSet and ClientSet id
        ServerCrasherSet == IF ExploreFail 
                            THEN (5*NumServers+NumHandlers*NumServers+1)..(5*NumServers+NumHandlers*NumServers+MaxNodeFail)
                            ELSE {}
        ServerOffset == 5*NumServers+NumHandlers*NumServers+MaxNodeFail

        ClientSet == (ServerOffset+1)..(ServerOffset+NumClients)

        NodeSet   == ServerSet \cup ClientSet

        KeySet == {}
    }

    macro checkFail(selfId, netEnabled) {
        if (ExploreFail) {
            if (\lnot netEnabled[selfId]) {
                await FALSE;
            };
        };
    }

    macro debug(toPrint) {
        if (Debug) {
            print toPrint;
        };
    }

    macro Send(net, dest, fd, m) {
        either {
            net[dest] := m;
        } or {
            await fd[dest];
        };
    }

    macro UpdateTerm(i, m, currentTerm, state, votedFor, leader) {
        if (m.mterm > currentTerm[i]) {
            currentTerm[i] := m.mterm;
            state[i]       := Follower;
            votedFor[i]    := Nil;
            leader[i]      := Nil;
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

    mapping macro Channel {
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
                yield SubSeq($variable, 1, Len($variable) - $value.cnt);
            };
        }
    }

    archetype AServerListener(
      srvId,
      ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
      ref state[_], ref currentTerm[_],
      ref log[_], ref plog[_],
      ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
      ref votedFor[_], ref votesResponded[_], ref votesGranted[_],
        \* added by Shayan
      ref leader[_],
      ref sm[_], ref smDomain[_],
      ref leaderTimeout,
      ref appendEntriesCh, ref becomeLeaderCh[_],
      ref handlerCh[_]
    ) 
    variables
        m;
    {
    listenerLoop:  
      while (TRUE) {
        m := net[srvId];
        assert m.mdest = srvId;
        handlerCh[srvId] := m;
      }
    }

    archetype AServerHandler(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_],
        ref handlerCh[_]
    )
    variables
        idx = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            \* checkFail(self, netEnabled);

            m := handlerCh[srvId];

        handleMsg:
            \* checkFail(self, netEnabled);

            if (m.mtype = RequestVoteRequest) {
                UpdateTerm(srvId, m, currentTerm, state, votedFor, leader);

                \* HandleRequestVoteRequest
                with (
                    i = srvId, j = m.msource,
                    logOK = \/ m.mlastLogTerm > LastTerm(log[i])
                            \/ /\ m.mlastLogTerm = LastTerm(log[i])
                               /\ m.mlastLogIndex >= Len(log[i]),
                    grant = /\ m.mterm = currentTerm[i]
                            /\ logOK
                            /\ votedFor[srvId] \in {Nil, j}
                ) {
                    assert m.mterm <= currentTerm[i];
                    if (grant) {
                        votedFor[i] := j;
                    };
                    Send(net, j, fd, [
                        mtype        |-> RequestVoteResponse,
                        mterm        |-> currentTerm[i],
                        mvoteGranted |-> grant,
                        msource      |-> i,
                        mdest        |-> j
                    ]);

                    debug(<<"HandleRequestVoteRequest", i, j, currentTerm[i], grant>>);
                };
            } else if (m.mtype = RequestVoteResponse) {
                UpdateTerm(srvId, m, currentTerm, state, votedFor, leader);

                \* DropStaleResponse
                if (m.mterm < currentTerm[srvId]) {
                    \* goto serverLoop;
                    skip;
                } else {
                    \* HandleRequestVoteResponse
                    with (i = srvId, j = m.msource) {
                        assert m.mterm = currentTerm[i];
                        votesResponded[i] := votesResponded[i] \cup {j};
                        if (m.mvoteGranted) {
                            votesGranted[i] := votesGranted[i] \cup {j};
                            if (
                                /\ state[i] = Candidate
                                /\ isQuorum(votesGranted[i])
                            ) {
                                becomeLeaderCh[i] := TRUE;
                            };
                        }; 
                    };
                };
            } else if (m.mtype = AppendEntriesRequest) {
                UpdateTerm(srvId, m, currentTerm, state, votedFor, leader);

                \* HandleAppendEntriesRequest
                with (
                    i = srvId, j = m.msource,
                    logOK = \/ m.mprevLogIndex = 0
                            \/ /\ m.mprevLogIndex > 0
                               /\ m.mprevLogIndex <= Len(log[i])
                               /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
                ) {
                    assert m.mterm <= currentTerm[i];

                    if (m.mterm = currentTerm[i]) {
                        leader[i] := m.msource;
                        leaderTimeout := LeaderTimeoutReset;
                    };

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
                            plog[i] := [
                                cmd |-> LogPop, 
                                cnt |-> Len(log[i]) - m.mprevLogIndex
                            ];
                            log[i]  := SubSeq(log[i], 1, m.mprevLogIndex);

                            plog[i] := [
                                cmd     |-> LogConcat, 
                                entries |-> m.mentries
                            ];
                            log[i]  := log[i] \o m.mentries;

                            assert m.mcommitIndex <= Len(log[i]);
                            with (result = ApplyLog(log[i], commitIndex[i]+1, m.mcommitIndex, sm[i], smDomain[i])) {
                                sm[i]       := result[1];
                                smDomain[i] := result[2];
                            };
                            commitIndex[i] := Max({commitIndex[i], m.mcommitIndex});
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
            } else if (m.mtype = AppendEntriesResponse) {
                UpdateTerm(srvId, m, currentTerm, state, votedFor, leader);

                \* DropStaleResponse
                if (m.mterm < currentTerm[srvId]) {
                    \* goto serverLoop;
                    skip;
                } else {
                    \* HandleAppendEntriesResponse
                    with (i = srvId, j = m.msource) {
                        assert m.mterm = currentTerm[i];
                        if (m.msuccess) {
                            \* nextIndex[j]  := m.mmatchIndex + 1;
                            nextIndex[i] := [nextIndex[i] EXCEPT ![j] = m.mmatchIndex + 1];
                            \* matchIndex[j] := m.mmatchIndex;
                            matchIndex[i] := [matchIndex[i] EXCEPT ![j] = m.mmatchIndex];
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
                \* HandleClientRequest

                debug(<<"HandleClientRequest", srvId, m.msource, currentTerm[srvId], state[srvId]>>);

                if (state[srvId] = Leader) {
                    with (entry = [term   |-> currentTerm[srvId],
                                   cmd    |-> m.mcmd,
                                   client |-> m.msource]
                    ) {
                        log[srvId]  := Append(log[srvId], entry);
                        plog[srvId] := [cmd |-> LogConcat, entries |-> <<entry>>];

                        \* commented out for perf optimization
                        \* appendEntriesCh := TRUE;
                    };
                } else {
                    with (
                        i = srvId, j = m.msource,
                        respType = IF m.mcmd.type = Put
                                   THEN ClientPutResponse
                                   ELSE ClientGetResponse
                    ) {
                        net[j] := [
                            mtype       |-> respType,
                            msuccess    |-> FALSE,
                            mresponse   |-> [
                                idx |-> m.mcmd.idx,
                                key |-> m.mcmd.key
                            ],
                            mleaderHint |-> leader[i],
                            msource     |-> i,
                            mdest       |-> j
                        ];
                    };
                };
            };
        };
    }

    archetype AServerRequestVote(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
    variable idx = 1;
    {
    serverRequestVoteLoop:
        while (TRUE) {
            \* checkFail(srvId, netEnabled);

            \* Server times out and starts a new election.
            await leaderTimeout;
            await netLen[srvId] = 0;

            await state[srvId] \in {Follower, Candidate};

            with (i = srvId) {
                state[i]          := Candidate;
                currentTerm[i]    := currentTerm[i] + 1;
                votedFor[i]       := i;
                votesResponded[i] := {i};
                votesGranted[i]   := {i};
                leader[i]         := Nil;

                debug(<<"ServerTimeout", i, currentTerm[i]>>);
            };

            idx := 1;
        requestVoteLoop:
            while (idx <= NumServers) {
                \* checkFail(srvId, netEnabled);

                \* RequestVote
                if (idx /= srvId) {
                    Send(net, idx, fd, [
                        mtype         |-> RequestVoteRequest,
                        mterm         |-> currentTerm[srvId],
                        mlastLogTerm  |-> LastTerm(log[srvId]),
                        mlastLogIndex |-> Len(log[srvId]),
                        msource       |-> srvId,
                        mdest         |-> idx
                    ]);
                };
                idx := idx + 1;
            };
        }
    }

    archetype AServerAppendEntries(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
    variable idx;
    {
    serverAppendEntriesLoop:
        while (appendEntriesCh) {
            \* checkFail(srvId, netEnabled);

            await state[srvId] = Leader;
            idx := 1;

        appendEntriesLoop:
            \* AppendEntries
            while (
                /\ state[srvId] = Leader
                /\ idx <= NumServers
            ) {
                \* checkFail(srvId, netEnabled);

                if (idx /= srvId) {
                    with (
                        prevLogIndex = nextIndex[srvId][idx] - 1,
                        prevLogTerm  = IF prevLogIndex > 0
                                       THEN log[srvId][prevLogIndex].term
                                       ELSE 0,
                        \* lastEntry    = Min({Len(log[srvId]), nextIndex[srvId][idx]}),
                        entries      = SubSeq(log[srvId], nextIndex[srvId][idx], Len(log[srvId]))
                    ) {
                        Send(net, idx, fd, [
                            mtype         |-> AppendEntriesRequest,
                            mterm         |-> currentTerm[srvId],
                            mprevLogIndex |-> prevLogIndex,
                            mprevLogTerm  |-> prevLogTerm,
                            mentries      |-> entries,
                            mcommitIndex  |-> commitIndex[srvId],
                            msource       |-> srvId,
                            mdest         |-> idx
                        ]);
                    };
                };
                idx := idx + 1;
            };
        };
    }

    archetype AServerAdvanceCommitIndex(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
    variable newCommitIndex = 0,
    {
    serverAdvanceCommitIndexLoop:
        while (TRUE) {
            \* checkFail(srvId, netEnabled);

            await state[srvId] = Leader;

            \* AdvanceCommitIndex
            with (
                i = srvId,

                \* explores a much smaller space than the previous version,
                \* proportional to disagreement not the log size
                maxAgreeIndex = FindMaxAgreeIndex(log[i], i, matchIndex[i]),

                nCommitIndex =
                    IF /\ maxAgreeIndex /= Nil
                       /\ log[i][maxAgreeIndex].term = currentTerm[i]
                    THEN maxAgreeIndex
                    ELSE commitIndex[i]
            ) {
                newCommitIndex := nCommitIndex;
                assert newCommitIndex >= commitIndex[i];
            };

        applyLoop:
            while (commitIndex[srvId] < newCommitIndex) {
                \* checkFail(srvId, netEnabled);

                commitIndex[srvId] := commitIndex[srvId] + 1;
                with (
                    i = srvId,
                    k = commitIndex[i],
                    entry = log[i][k],
                    cmd   = entry.cmd,
                    respType = IF cmd.type = Put
                               THEN ClientPutResponse
                               ELSE ClientGetResponse
                ) {
                    if (cmd.type = Put) {
                        sm[i]       := sm[i] @@ (cmd.key :> cmd.value); \* allows sm[i] to grow
                        smDomain[i] := smDomain[i] \cup {cmd.key};
                    };
                    with (reqOk = cmd.key \in smDomain[i]) {
                        net[entry.client] := [
                            mtype       |-> respType,
                            msuccess    |-> TRUE,
                            mresponse   |-> [
                                idx   |-> cmd.idx,
                                key   |-> cmd.key,
                                value |-> IF reqOk THEN sm[i][cmd.key] ELSE Nil,
                                ok    |-> reqOk
                            ],
                            mleaderHint |-> i,
                            msource     |-> i,
                            mdest       |-> entry.client
                        ];
                    };
                };
            };
        };
    }

    archetype AServerBecomeLeader(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
    {
    serverBecomeLeaderLoop:
        while (becomeLeaderCh[srvId]) {
        \* while (TRUE) {
            \* checkFail(srvId, netEnabled);

            \* BecomeLeader
            await state[srvId] = Candidate;
            await isQuorum(votesGranted[srvId]);

            with (i = srvId) {
                state[i]      := Leader;
                nextIndex[i]  := [j \in ServerSet |-> Len(log[i]) + 1];
                matchIndex[i] := [j \in ServerSet |-> 0];
                leader[i]     := i;

                appendEntriesCh := TRUE;
                debug(<<"BecomeLeader", i, currentTerm[i], state[i], leader[i]>>);
            };
        };
    }

    archetype AClient(ref net[_], ref netLen[_], ref fd[_], ref reqCh, ref respCh, ref timeout)
    variables leader = Nil, req, resp, reqIdx = 0;
    {
    clientLoop:
        while (TRUE) {
            req := reqCh;
            reqIdx := reqIdx + 1;

        sndReq:
            if (leader = Nil) {
                with (srv \in ServerSet) {
                    leader := srv;
                };
            };
            debug(<<"ClientSndReq", self, leader, reqIdx, req>>);
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
                debug(<<"ClientRcvResp", self, leader, reqIdx, resp>>);
                assert resp.mdest = self;

                \* it should be /very likely/ that indexed requests will help us
                \* throw out duplicate server responses.
                \* one edge case I can think of: start, do one req, immediately
                \* stop + restart, immediately get stale response to last req.
                if (resp.mresponse.idx /= reqIdx) {
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
                        respCh := resp;
                        debug(<<"ClientRcvChDone", self, leader, reqIdx, resp>>);
                    };
                };
            } or {
                await \/ /\ fd[leader] 
                         /\ netLen[self] = 0
                      \/ timeout;
                debug(<<"ClientTimeout", self, leader, reqIdx>>);
                leader := Nil;
                goto sndReq;
            };
        };
    }

    archetype AServerCrasher(srvId, ref netEnabled[_], ref fd[_]) {
    serverCrash:
        netEnabled[srvId] := FALSE;
    fdUpdate:
        fd[srvId] := TRUE;
    block:
        await FALSE;
    }

    variables
        network = [i \in NodeSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd      = [i \in ServerSet |-> FALSE];

        state       = [i \in ServerSet |-> Follower];
        currentTerm = [i \in ServerSet |-> 1];

        commitIndex = [i \in ServerSet |-> 0];
        nextIndex   = [i \in ServerSet |-> [j \in ServerSet |-> 1]];
        matchIndex  = [i \in ServerSet |-> [j \in ServerSet |-> 0]];

        log  = [i \in ServerSet |-> <<>>];
        plog = [i \in ServerSet |-> <<>>];

        votedFor       = [i \in ServerSet |-> Nil];
        votesResponded = [i \in ServerSet |-> {}];
        votesGranted   = [i \in ServerSet |-> {}];

        leader = [i \in ServerSet |-> Nil];

        sm       = [i \in ServerSet |-> [k \in KeySet |-> Nil]];
        smDomain = [i \in ServerSet |-> KeySet];

        leaderTimeout   = TRUE;
        appendEntriesCh = TRUE;
        becomeLeaderCh  = [i \in ServerSet |-> 
            IF NumServers > 1 
            THEN <<>>
            ELSE <<TRUE>>
        ];
        handlerCh = [i \in ServerSet |-> <<>>];

        allReqs = <<
            [type |-> Put, key |-> Key1, value |-> Value1],
            [type |-> Get, key |-> Key2],
            [type |-> Get, key |-> Key1]
        >>;

        reqCh = SubSeq(allReqs, 1, NumRequests);
        respCh;

        requestVoteSrvId        = [i \in ServerRequestVoteSet        |-> i - 1*NumServers];
        appendEntriesSrvId      = [i \in ServerAppendEntriesSet      |-> i - 2*NumServers];
        advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> i - 3*NumServers];
        becomeLeaderSrvId       = [i \in ServerBecomeLeaderSet       |-> i - 4*NumServers];
        \* TODO: NumHandlers > 0, ÷ = integer division
        handlerSrvId            = [i \in ServerHandlerSet            |-> (i - 5*NumServers - 1) \div NumHandlers + 1];
        \* TODO: change crasherSrvId
        crasherSrvId            = [i \in ServerCrasherSet            |-> i - 5*NumServers - NumHandlers*NumServers];
    
    fair process (s00 \in ServerSet) == instance AServerListener(
        s00,
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_],
        ref handlerCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s01 \in ServerHandlerSet) == instance AServerHandler(
        handlerSrvId[s01],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_],
        ref handlerCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s1 \in ServerRequestVoteSet) == instance AServerRequestVote(
        requestVoteSrvId[s1],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog;

    fair process (s2 \in ServerAppendEntriesSet) == instance AServerAppendEntries(
        appendEntriesSrvId[s2],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog;

    fair process (s3 \in ServerAdvanceCommitIndexSet) == instance AServerAdvanceCommitIndex(
        advanceCommitIndexSrvId[s3],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog;

    fair process (s4 \in ServerBecomeLeaderSet) == instance AServerBecomeLeader(
        becomeLeaderSrvId[s4],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog
        mapping @21[_] via Channel;

    fair process (client \in ClientSet) == instance AClient(
        ref network[_], ref network[_], ref fd[_],
        ref reqCh, ref respCh, FALSE
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via NetworkBufferLength
        mapping @3[_] via PerfectFD
        mapping @4    via Channel;
    
    fair process (crasher \in ServerCrasherSet) == instance AServerCrasher(
        crasherSrvId[crasher],
        ref network[_], ref fd[_]
    )
        mapping @2[_] via NetworkToggle
        mapping @3[_] via PerfectFD;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raftkvs {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; state = [i \in ServerSet |-> Follower]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]; log = [i \in ServerSet |-> <<>>]; plog = [i \in ServerSet |-> <<>>]; votedFor = [i \in ServerSet |-> Nil]; votesResponded = [i \in ServerSet |-> {}]; votesGranted = [i \in ServerSet |-> {}]; leader = [i \in ServerSet |-> Nil]; sm = [i \in ServerSet |-> [k \in KeySet |-> Nil]]; smDomain = [i \in ServerSet |-> KeySet]; leaderTimeout = TRUE; appendEntriesCh = TRUE; becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]; handlerCh = [i \in ServerSet |-> <<>>]; allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>; reqCh = SubSeq(allReqs, 1, NumRequests); respCh; requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]; appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]; advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]; becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]; handlerSrvId = [i \in ServerHandlerSet |-> ((((i) - ((5) * (NumServers))) - (1)) \div (NumHandlers)) + (1)]; crasherSrvId = [i \in ServerCrasherSet |-> ((i) - ((5) * (NumServers))) - ((NumHandlers) * (NumServers))];
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
    ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
    ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
    ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
    ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
    ServerHandlerSet == (((5) * (NumServers)) + (1)) .. (((5) * (NumServers)) + ((NumHandlers) * (NumServers)))
    ServerCrasherSet == IF ExploreFail THEN ((((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (1)) .. ((((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (MaxNodeFail)) ELSE {}
    ServerOffset == (((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (MaxNodeFail)
    ClientSet == ((ServerOffset) + (1)) .. ((ServerOffset) + (NumClients))
    NodeSet == (ServerSet) \union (ClientSet)
    KeySet == {}
  }
  
  fair process (s00 \in ServerSet)
    variables m; srvId = self;
  {
    listenerLoop:
      if (TRUE) {
        assert ((network)[srvId]).enabled;
        await (Len(((network)[srvId]).queue)) > (0);
        with (readMsg00 = Head(((network)[srvId]).queue)) {
          network := [network EXCEPT ![srvId] = [queue |-> Tail(((network)[srvId]).queue), enabled |-> ((network)[srvId]).enabled]];
          with (yielded_network3 = readMsg00) {
            m := yielded_network3;
            assert ((m).mdest) = (srvId);
            with (value00 = m) {
              handlerCh := [handlerCh EXCEPT ![srvId] = Append((handlerCh)[srvId], value00)];
              goto listenerLoop;
            };
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (s01 \in ServerHandlerSet)
    variables idx = 1; m0; srvId0 = (handlerSrvId)[self];
  {
    serverLoop:
      if (TRUE) {
        await (Len((handlerCh)[srvId0])) > (0);
        with (res00 = Head((handlerCh)[srvId0])) {
          handlerCh := [handlerCh EXCEPT ![srvId0] = Tail((handlerCh)[srvId0])];
          with (yielded_handlerCh0 = res00) {
            m0 := yielded_handlerCh0;
            goto handleMsg;
          };
        };
      } else {
        goto Done;
      };
    handleMsg:
      if (((m0).mtype) = (RequestVoteRequest)) {
        if (((m0).mterm) > ((currentTerm)[srvId0])) {
          currentTerm := [currentTerm EXCEPT ![srvId0] = (m0).mterm];
          state := [state EXCEPT ![srvId0] = Follower];
          with (votedFor1 = [votedFor EXCEPT ![srvId0] = Nil]) {
            leader := [leader EXCEPT ![srvId0] = Nil];
            with (
              i = srvId0, 
              j = (m0).msource, 
              logOK = (((m0).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m0).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m0).mlastLogIndex) >= (Len((log)[i])))), 
              grant = ((((m0).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor1)[srvId0]) \in ({Nil, j}))
            ) {
              assert ((m0).mterm) <= ((currentTerm)[i]);
              if (grant) {
                votedFor := [votedFor1 EXCEPT ![i] = j];
                either {
                  with (value16 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]];
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      goto serverLoop;
                    } else {
                      goto serverLoop;
                    };
                  };
                } or {
                  with (yielded_fd7 = (fd)[j]) {
                    await yielded_fd7;
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      goto serverLoop;
                    } else {
                      goto serverLoop;
                    };
                  };
                };
              } else {
                either {
                  with (value17 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]];
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      votedFor := votedFor1;
                      goto serverLoop;
                    } else {
                      votedFor := votedFor1;
                      goto serverLoop;
                    };
                  };
                } or {
                  with (yielded_fd8 = (fd)[j]) {
                    await yielded_fd8;
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      votedFor := votedFor1;
                      goto serverLoop;
                    } else {
                      votedFor := votedFor1;
                      goto serverLoop;
                    };
                  };
                };
              };
            };
          };
        } else {
          with (
            i = srvId0, 
            j = (m0).msource, 
            logOK = (((m0).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m0).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m0).mlastLogIndex) >= (Len((log)[i])))), 
            grant = ((((m0).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[srvId0]) \in ({Nil, j}))
          ) {
            assert ((m0).mterm) <= ((currentTerm)[i]);
            if (grant) {
              votedFor := [votedFor EXCEPT ![i] = j];
              either {
                with (value18 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]];
                  if (Debug) {
                    print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              } or {
                with (yielded_fd9 = (fd)[j]) {
                  await yielded_fd9;
                  if (Debug) {
                    print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              };
            } else {
              either {
                with (value19 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value19), enabled |-> ((network)[j]).enabled]];
                  if (Debug) {
                    print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              } or {
                with (yielded_fd10 = (fd)[j]) {
                  await yielded_fd10;
                  if (Debug) {
                    print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              };
            };
          };
        };
      } else {
        if (((m0).mtype) = (RequestVoteResponse)) {
          if (((m0).mterm) > ((currentTerm)[srvId0])) {
            currentTerm := [currentTerm EXCEPT ![srvId0] = (m0).mterm];
            state := [state EXCEPT ![srvId0] = Follower];
            votedFor := [votedFor EXCEPT ![srvId0] = Nil];
            leader := [leader EXCEPT ![srvId0] = Nil];
            if (((m0).mterm) < ((currentTerm)[srvId0])) {
              skip;
              goto serverLoop;
            } else {
              with (
                i = srvId0, 
                j = (m0).msource
              ) {
                assert ((m0).mterm) = ((currentTerm)[i]);
                votesResponded := [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})];
                if ((m0).mvoteGranted) {
                  votesGranted := [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})];
                  if ((((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted)[i]))) {
                    with (value20 = TRUE) {
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value20)];
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
          } else {
            if (((m0).mterm) < ((currentTerm)[srvId0])) {
              skip;
              goto serverLoop;
            } else {
              with (
                i = srvId0, 
                j = (m0).msource
              ) {
                assert ((m0).mterm) = ((currentTerm)[i]);
                votesResponded := [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})];
                if ((m0).mvoteGranted) {
                  votesGranted := [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})];
                  if ((((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted)[i]))) {
                    with (value21 = TRUE) {
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value21)];
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
        } else {
          if (((m0).mtype) = (AppendEntriesRequest)) {
            if (((m0).mterm) > ((currentTerm)[srvId0])) {
              currentTerm := [currentTerm EXCEPT ![srvId0] = (m0).mterm];
              with (state1 = [state EXCEPT ![srvId0] = Follower]) {
                votedFor := [votedFor EXCEPT ![srvId0] = Nil];
                with (
                  leader1 = [leader EXCEPT ![srvId0] = Nil], 
                  i = srvId0, 
                  j = (m0).msource, 
                  logOK = (((m0).mprevLogIndex) = (0)) \/ (((((m0).mprevLogIndex) > (0)) /\ (((m0).mprevLogIndex) <= (Len((log)[i])))) /\ (((m0).mprevLogTerm) = ((((log)[i])[(m0).mprevLogIndex]).term)))
                ) {
                  assert ((m0).mterm) <= ((currentTerm)[i]);
                  if (((m0).mterm) = ((currentTerm)[i])) {
                    leader := [leader1 EXCEPT ![i] = (m0).msource];
                    leaderTimeout := LeaderTimeoutReset;
                    if ((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Candidate))) {
                      state := [state1 EXCEPT ![i] = Follower];
                      if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value30 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value30), enabled |-> ((network)[j]).enabled]];
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd00 = (fd)[j]) {
                            await yielded_fd00;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m0).mprevLogIndex) + (1), 
                          value40 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                        ) {
                          if (((value40).cmd) = (LogConcat)) {
                            with (
                              plog8 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value40).entries)], 
                              log8 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value50 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value50).cmd) = (LogConcat)) {
                                plog := [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value50).entries)];
                                log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result8 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result8)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result8)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value60 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value60), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd11 = (fd)[j]) {
                                      await yielded_fd11;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value50).cmd) = (LogPop)) {
                                  plog := [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - ((value50).cnt))];
                                  log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result9 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result9)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result9)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value61 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value61), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd12 = (fd)[j]) {
                                        await yielded_fd12;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result10 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result10)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result10)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value62 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value62), enabled |-> ((network)[j]).enabled]];
                                        plog := plog8;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd13 = (fd)[j]) {
                                        await yielded_fd13;
                                        plog := plog8;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if (((value40).cmd) = (LogPop)) {
                              with (
                                plog9 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value40).cnt))], 
                                log9 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value51 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value51).cmd) = (LogConcat)) {
                                  plog := [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value51).entries)];
                                  log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result11 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result11)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result11)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value63 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value63), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd14 = (fd)[j]) {
                                        await yielded_fd14;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value51).cmd) = (LogPop)) {
                                    plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - ((value51).cnt))];
                                    log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result12 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result12)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result12)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value64 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value64), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd15 = (fd)[j]) {
                                          await yielded_fd15;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result13 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result13)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result13)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value65 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value65), enabled |-> ((network)[j]).enabled]];
                                          plog := plog9;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd16 = (fd)[j]) {
                                          await yielded_fd16;
                                          plog := plog9;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            } else {
                              with (
                                log10 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value52 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value52).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value52).entries)];
                                  log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result14 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result14)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result14)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value66 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value66), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd17 = (fd)[j]) {
                                        await yielded_fd17;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value52).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value52).cnt))];
                                    log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result15 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result15)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result15)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value67 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value67), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd18 = (fd)[j]) {
                                          await yielded_fd18;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result16 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result16)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result16)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value68 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value68), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd19 = (fd)[j]) {
                                          await yielded_fd19;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    } else {
                      if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value31 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value31), enabled |-> ((network)[j]).enabled]];
                            state := state1;
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd01 = (fd)[j]) {
                            await yielded_fd01;
                            state := state1;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m0).mprevLogIndex) + (1), 
                          value41 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                        ) {
                          if (((value41).cmd) = (LogConcat)) {
                            with (
                              plog10 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value41).entries)], 
                              log11 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value53 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value53).cmd) = (LogConcat)) {
                                plog := [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value53).entries)];
                                log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result17 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result17)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result17)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value69 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value69), enabled |-> ((network)[j]).enabled]];
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd110 = (fd)[j]) {
                                      await yielded_fd110;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value53).cmd) = (LogPop)) {
                                  plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - ((value53).cnt))];
                                  log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result18 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result18)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result18)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value610 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value610), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd111 = (fd)[j]) {
                                        await yielded_fd111;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result19 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result19)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result19)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value611 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value611), enabled |-> ((network)[j]).enabled]];
                                        plog := plog10;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd112 = (fd)[j]) {
                                        await yielded_fd112;
                                        plog := plog10;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if (((value41).cmd) = (LogPop)) {
                              with (
                                plog11 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value41).cnt))], 
                                log12 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value54 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value54).cmd) = (LogConcat)) {
                                  plog := [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value54).entries)];
                                  log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result20 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result20)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result20)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value612 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value612), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd113 = (fd)[j]) {
                                        await yielded_fd113;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value54).cmd) = (LogPop)) {
                                    plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - ((value54).cnt))];
                                    log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result21 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result21)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result21)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value613 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value613), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd114 = (fd)[j]) {
                                          await yielded_fd114;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result22 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result22)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result22)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value614 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value614), enabled |-> ((network)[j]).enabled]];
                                          plog := plog11;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd115 = (fd)[j]) {
                                          await yielded_fd115;
                                          plog := plog11;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            } else {
                              with (
                                log13 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value55 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value55).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value55).entries)];
                                  log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result23 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result23)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result23)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value615 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value615), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd116 = (fd)[j]) {
                                        await yielded_fd116;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value55).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value55).cnt))];
                                    log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result24 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result24)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result24)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value616 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value616), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd117 = (fd)[j]) {
                                          await yielded_fd117;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result25 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result25)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result25)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value617 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value617), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd118 = (fd)[j]) {
                                          await yielded_fd118;
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
                        };
                      };
                    };
                  } else {
                    if ((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Candidate))) {
                      state := [state1 EXCEPT ![i] = Follower];
                      if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value32 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value32), enabled |-> ((network)[j]).enabled]];
                            leader := leader1;
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd02 = (fd)[j]) {
                            await yielded_fd02;
                            leader := leader1;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m0).mprevLogIndex) + (1), 
                          value42 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                        ) {
                          if (((value42).cmd) = (LogConcat)) {
                            with (
                              plog12 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value42).entries)], 
                              log14 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value56 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value56).cmd) = (LogConcat)) {
                                plog := [plog12 EXCEPT ![i] = ((plog12)[i]) \o ((value56).entries)];
                                log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result26 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result26)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result26)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value618 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value618), enabled |-> ((network)[j]).enabled]];
                                      leader := leader1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd119 = (fd)[j]) {
                                      await yielded_fd119;
                                      leader := leader1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value56).cmd) = (LogPop)) {
                                  plog := [plog12 EXCEPT ![i] = SubSeq((plog12)[i], 1, (Len((plog12)[i])) - ((value56).cnt))];
                                  log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result27 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result27)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result27)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value619 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value619), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd120 = (fd)[j]) {
                                        await yielded_fd120;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result28 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result28)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result28)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value620 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value620), enabled |-> ((network)[j]).enabled]];
                                        plog := plog12;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd121 = (fd)[j]) {
                                        await yielded_fd121;
                                        plog := plog12;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if (((value42).cmd) = (LogPop)) {
                              with (
                                plog13 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value42).cnt))], 
                                log15 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value57 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value57).cmd) = (LogConcat)) {
                                  plog := [plog13 EXCEPT ![i] = ((plog13)[i]) \o ((value57).entries)];
                                  log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result29 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result29)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result29)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value621 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value621), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd122 = (fd)[j]) {
                                        await yielded_fd122;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value57).cmd) = (LogPop)) {
                                    plog := [plog13 EXCEPT ![i] = SubSeq((plog13)[i], 1, (Len((plog13)[i])) - ((value57).cnt))];
                                    log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result30 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result30)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result30)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value622 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value622), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd123 = (fd)[j]) {
                                          await yielded_fd123;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result31 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result31)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result31)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value623 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value623), enabled |-> ((network)[j]).enabled]];
                                          plog := plog13;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd124 = (fd)[j]) {
                                          await yielded_fd124;
                                          plog := plog13;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            } else {
                              with (
                                log16 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value58 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value58).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value58).entries)];
                                  log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result32 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result32)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result32)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value624 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value624), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd125 = (fd)[j]) {
                                        await yielded_fd125;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value58).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value58).cnt))];
                                    log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result33 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result33)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result33)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value625 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value625), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd126 = (fd)[j]) {
                                          await yielded_fd126;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result34 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result34)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result34)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value626 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value626), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd127 = (fd)[j]) {
                                          await yielded_fd127;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    } else {
                      if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value33 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value33), enabled |-> ((network)[j]).enabled]];
                            leader := leader1;
                            state := state1;
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd03 = (fd)[j]) {
                            await yielded_fd03;
                            leader := leader1;
                            state := state1;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m0).mprevLogIndex) + (1), 
                          value43 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                        ) {
                          if (((value43).cmd) = (LogConcat)) {
                            with (
                              plog14 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value43).entries)], 
                              log17 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value59 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value59).cmd) = (LogConcat)) {
                                plog := [plog14 EXCEPT ![i] = ((plog14)[i]) \o ((value59).entries)];
                                log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result35 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result35)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result35)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value627 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value627), enabled |-> ((network)[j]).enabled]];
                                      leader := leader1;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd128 = (fd)[j]) {
                                      await yielded_fd128;
                                      leader := leader1;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value59).cmd) = (LogPop)) {
                                  plog := [plog14 EXCEPT ![i] = SubSeq((plog14)[i], 1, (Len((plog14)[i])) - ((value59).cnt))];
                                  log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result36 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result36)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result36)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value628 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value628), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd129 = (fd)[j]) {
                                        await yielded_fd129;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result37 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result37)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result37)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value629 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value629), enabled |-> ((network)[j]).enabled]];
                                        plog := plog14;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd130 = (fd)[j]) {
                                        await yielded_fd130;
                                        plog := plog14;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if (((value43).cmd) = (LogPop)) {
                              with (
                                plog15 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value43).cnt))], 
                                log18 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value510 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value510).cmd) = (LogConcat)) {
                                  plog := [plog15 EXCEPT ![i] = ((plog15)[i]) \o ((value510).entries)];
                                  log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result38 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result38)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result38)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value630 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value630), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd131 = (fd)[j]) {
                                        await yielded_fd131;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value510).cmd) = (LogPop)) {
                                    plog := [plog15 EXCEPT ![i] = SubSeq((plog15)[i], 1, (Len((plog15)[i])) - ((value510).cnt))];
                                    log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result39 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result39)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result39)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value631 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value631), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd132 = (fd)[j]) {
                                          await yielded_fd132;
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result40 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result40)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result40)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value632 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value632), enabled |-> ((network)[j]).enabled]];
                                          plog := plog15;
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd133 = (fd)[j]) {
                                          await yielded_fd133;
                                          plog := plog15;
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              };
                            } else {
                              with (
                                log19 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                                value511 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                              ) {
                                if (((value511).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value511).entries)];
                                  log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result41 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result41)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result41)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value633 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value633), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd134 = (fd)[j]) {
                                        await yielded_fd134;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value511).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value511).cnt))];
                                    log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result42 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result42)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result42)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value634 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value634), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd135 = (fd)[j]) {
                                          await yielded_fd135;
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0).mentries)];
                                    assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                    with (result43 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result43)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result43)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                      either {
                                        with (value635 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value635), enabled |-> ((network)[j]).enabled]];
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd136 = (fd)[j]) {
                                          await yielded_fd136;
                                          leader := leader1;
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
                        };
                      };
                    };
                  };
                };
              };
            } else {
              with (
                i = srvId0, 
                j = (m0).msource, 
                logOK = (((m0).mprevLogIndex) = (0)) \/ (((((m0).mprevLogIndex) > (0)) /\ (((m0).mprevLogIndex) <= (Len((log)[i])))) /\ (((m0).mprevLogTerm) = ((((log)[i])[(m0).mprevLogIndex]).term)))
              ) {
                assert ((m0).mterm) <= ((currentTerm)[i]);
                if (((m0).mterm) = ((currentTerm)[i])) {
                  leader := [leader EXCEPT ![i] = (m0).msource];
                  leaderTimeout := LeaderTimeoutReset;
                  if ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))) {
                    state := [state EXCEPT ![i] = Follower];
                    if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value34 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value34), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd04 = (fd)[j]) {
                          await yielded_fd04;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m0).mprevLogIndex) + (1), 
                        value44 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                      ) {
                        if (((value44).cmd) = (LogConcat)) {
                          with (
                            plog16 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value44).entries)], 
                            log20 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                            value512 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                          ) {
                            if (((value512).cmd) = (LogConcat)) {
                              plog := [plog16 EXCEPT ![i] = ((plog16)[i]) \o ((value512).entries)];
                              log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0).mentries)];
                              assert ((m0).mcommitIndex) <= (Len((log)[i]));
                              with (result44 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                sm := [sm EXCEPT ![i] = (result44)[1]];
                                smDomain := [smDomain EXCEPT ![i] = (result44)[2]];
                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                either {
                                  with (value636 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value636), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd137 = (fd)[j]) {
                                    await yielded_fd137;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value512).cmd) = (LogPop)) {
                                plog := [plog16 EXCEPT ![i] = SubSeq((plog16)[i], 1, (Len((plog16)[i])) - ((value512).cnt))];
                                log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result45 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result45)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result45)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value637 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value637), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd138 = (fd)[j]) {
                                      await yielded_fd138;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result46 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result46)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result46)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value638 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value638), enabled |-> ((network)[j]).enabled]];
                                      plog := plog16;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd139 = (fd)[j]) {
                                      await yielded_fd139;
                                      plog := plog16;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value44).cmd) = (LogPop)) {
                            with (
                              plog17 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value44).cnt))], 
                              log21 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value513 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value513).cmd) = (LogConcat)) {
                                plog := [plog17 EXCEPT ![i] = ((plog17)[i]) \o ((value513).entries)];
                                log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result47 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result47)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result47)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value639 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value639), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd140 = (fd)[j]) {
                                      await yielded_fd140;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value513).cmd) = (LogPop)) {
                                  plog := [plog17 EXCEPT ![i] = SubSeq((plog17)[i], 1, (Len((plog17)[i])) - ((value513).cnt))];
                                  log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result48 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result48)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result48)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value640 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value640), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd141 = (fd)[j]) {
                                        await yielded_fd141;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result49 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result49)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result49)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value641 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value641), enabled |-> ((network)[j]).enabled]];
                                        plog := plog17;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd142 = (fd)[j]) {
                                        await yielded_fd142;
                                        plog := plog17;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            with (
                              log22 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value514 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value514).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value514).entries)];
                                log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result50 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result50)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result50)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value642 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value642), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd143 = (fd)[j]) {
                                      await yielded_fd143;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value514).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value514).cnt))];
                                  log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result51 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result51)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result51)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value643 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value643), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd144 = (fd)[j]) {
                                        await yielded_fd144;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result52 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result52)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result52)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value644 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value644), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd145 = (fd)[j]) {
                                        await yielded_fd145;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    };
                  } else {
                    if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value35 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value35), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd05 = (fd)[j]) {
                          await yielded_fd05;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m0).mprevLogIndex) + (1), 
                        value45 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                      ) {
                        if (((value45).cmd) = (LogConcat)) {
                          with (
                            plog18 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value45).entries)], 
                            log23 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                            value515 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                          ) {
                            if (((value515).cmd) = (LogConcat)) {
                              plog := [plog18 EXCEPT ![i] = ((plog18)[i]) \o ((value515).entries)];
                              log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0).mentries)];
                              assert ((m0).mcommitIndex) <= (Len((log)[i]));
                              with (result53 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                sm := [sm EXCEPT ![i] = (result53)[1]];
                                smDomain := [smDomain EXCEPT ![i] = (result53)[2]];
                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                either {
                                  with (value645 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value645), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd146 = (fd)[j]) {
                                    await yielded_fd146;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value515).cmd) = (LogPop)) {
                                plog := [plog18 EXCEPT ![i] = SubSeq((plog18)[i], 1, (Len((plog18)[i])) - ((value515).cnt))];
                                log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result54 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result54)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result54)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value646 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value646), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd147 = (fd)[j]) {
                                      await yielded_fd147;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result55 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result55)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result55)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value647 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value647), enabled |-> ((network)[j]).enabled]];
                                      plog := plog18;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd148 = (fd)[j]) {
                                      await yielded_fd148;
                                      plog := plog18;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value45).cmd) = (LogPop)) {
                            with (
                              plog19 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value45).cnt))], 
                              log24 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value516 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value516).cmd) = (LogConcat)) {
                                plog := [plog19 EXCEPT ![i] = ((plog19)[i]) \o ((value516).entries)];
                                log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result56 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result56)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result56)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value648 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value648), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd149 = (fd)[j]) {
                                      await yielded_fd149;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value516).cmd) = (LogPop)) {
                                  plog := [plog19 EXCEPT ![i] = SubSeq((plog19)[i], 1, (Len((plog19)[i])) - ((value516).cnt))];
                                  log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result57 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result57)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result57)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value649 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value649), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd150 = (fd)[j]) {
                                        await yielded_fd150;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result58 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result58)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result58)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value650 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value650), enabled |-> ((network)[j]).enabled]];
                                        plog := plog19;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd151 = (fd)[j]) {
                                        await yielded_fd151;
                                        plog := plog19;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            with (
                              log25 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value517 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value517).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value517).entries)];
                                log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result59 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result59)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result59)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value651 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value651), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd152 = (fd)[j]) {
                                      await yielded_fd152;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value517).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value517).cnt))];
                                  log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result60 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result60)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result60)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value652 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value652), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd153 = (fd)[j]) {
                                        await yielded_fd153;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result61 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result61)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result61)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value653 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value653), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd154 = (fd)[j]) {
                                        await yielded_fd154;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    };
                  };
                } else {
                  if ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))) {
                    state := [state EXCEPT ![i] = Follower];
                    if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value36 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value36), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd06 = (fd)[j]) {
                          await yielded_fd06;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m0).mprevLogIndex) + (1), 
                        value46 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                      ) {
                        if (((value46).cmd) = (LogConcat)) {
                          with (
                            plog20 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value46).entries)], 
                            log26 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                            value518 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                          ) {
                            if (((value518).cmd) = (LogConcat)) {
                              plog := [plog20 EXCEPT ![i] = ((plog20)[i]) \o ((value518).entries)];
                              log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0).mentries)];
                              assert ((m0).mcommitIndex) <= (Len((log)[i]));
                              with (result62 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                sm := [sm EXCEPT ![i] = (result62)[1]];
                                smDomain := [smDomain EXCEPT ![i] = (result62)[2]];
                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                either {
                                  with (value654 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value654), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd155 = (fd)[j]) {
                                    await yielded_fd155;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value518).cmd) = (LogPop)) {
                                plog := [plog20 EXCEPT ![i] = SubSeq((plog20)[i], 1, (Len((plog20)[i])) - ((value518).cnt))];
                                log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result63 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result63)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result63)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value655 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value655), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd156 = (fd)[j]) {
                                      await yielded_fd156;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result64 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result64)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result64)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value656 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value656), enabled |-> ((network)[j]).enabled]];
                                      plog := plog20;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd157 = (fd)[j]) {
                                      await yielded_fd157;
                                      plog := plog20;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value46).cmd) = (LogPop)) {
                            with (
                              plog21 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value46).cnt))], 
                              log27 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value519 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value519).cmd) = (LogConcat)) {
                                plog := [plog21 EXCEPT ![i] = ((plog21)[i]) \o ((value519).entries)];
                                log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result65 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result65)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result65)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value657 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value657), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd158 = (fd)[j]) {
                                      await yielded_fd158;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value519).cmd) = (LogPop)) {
                                  plog := [plog21 EXCEPT ![i] = SubSeq((plog21)[i], 1, (Len((plog21)[i])) - ((value519).cnt))];
                                  log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result66 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result66)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result66)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value658 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value658), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd159 = (fd)[j]) {
                                        await yielded_fd159;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result67 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result67)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result67)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value659 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value659), enabled |-> ((network)[j]).enabled]];
                                        plog := plog21;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd160 = (fd)[j]) {
                                        await yielded_fd160;
                                        plog := plog21;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            with (
                              log28 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value520 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value520).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value520).entries)];
                                log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result68 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result68)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result68)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value660 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value660), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd161 = (fd)[j]) {
                                      await yielded_fd161;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value520).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value520).cnt))];
                                  log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result69 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result69)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result69)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value661 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value661), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd162 = (fd)[j]) {
                                        await yielded_fd162;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result70 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result70)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result70)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value662 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value662), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd163 = (fd)[j]) {
                                        await yielded_fd163;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    };
                  } else {
                    if ((((m0).mterm) < ((currentTerm)[i])) \/ (((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value37 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value37), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd07 = (fd)[j]) {
                          await yielded_fd07;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m0).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m0).mprevLogIndex) + (1), 
                        value47 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0).mprevLogIndex)]
                      ) {
                        if (((value47).cmd) = (LogConcat)) {
                          with (
                            plog22 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value47).entries)], 
                            log29 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                            value521 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                          ) {
                            if (((value521).cmd) = (LogConcat)) {
                              plog := [plog22 EXCEPT ![i] = ((plog22)[i]) \o ((value521).entries)];
                              log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0).mentries)];
                              assert ((m0).mcommitIndex) <= (Len((log)[i]));
                              with (result71 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                sm := [sm EXCEPT ![i] = (result71)[1]];
                                smDomain := [smDomain EXCEPT ![i] = (result71)[2]];
                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                either {
                                  with (value663 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value663), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd164 = (fd)[j]) {
                                    await yielded_fd164;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value521).cmd) = (LogPop)) {
                                plog := [plog22 EXCEPT ![i] = SubSeq((plog22)[i], 1, (Len((plog22)[i])) - ((value521).cnt))];
                                log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result72 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result72)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result72)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value664 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value664), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd165 = (fd)[j]) {
                                      await yielded_fd165;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result73 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result73)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result73)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value665 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value665), enabled |-> ((network)[j]).enabled]];
                                      plog := plog22;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd166 = (fd)[j]) {
                                      await yielded_fd166;
                                      plog := plog22;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value47).cmd) = (LogPop)) {
                            with (
                              plog23 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value47).cnt))], 
                              log30 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value522 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value522).cmd) = (LogConcat)) {
                                plog := [plog23 EXCEPT ![i] = ((plog23)[i]) \o ((value522).entries)];
                                log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result74 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result74)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result74)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value666 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value666), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd167 = (fd)[j]) {
                                      await yielded_fd167;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value522).cmd) = (LogPop)) {
                                  plog := [plog23 EXCEPT ![i] = SubSeq((plog23)[i], 1, (Len((plog23)[i])) - ((value522).cnt))];
                                  log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result75 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result75)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result75)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value667 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value667), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd168 = (fd)[j]) {
                                        await yielded_fd168;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result76 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result76)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result76)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value668 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value668), enabled |-> ((network)[j]).enabled]];
                                        plog := plog23;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd169 = (fd)[j]) {
                                        await yielded_fd169;
                                        plog := plog23;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            with (
                              log31 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0).mprevLogIndex)], 
                              value523 = [cmd |-> LogConcat, entries |-> (m0).mentries]
                            ) {
                              if (((value523).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value523).entries)];
                                log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0).mentries)];
                                assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                with (result77 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result77)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result77)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                  either {
                                    with (value669 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value669), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd170 = (fd)[j]) {
                                      await yielded_fd170;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value523).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value523).cnt))];
                                  log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result78 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result78)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result78)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value670 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value670), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd171 = (fd)[j]) {
                                        await yielded_fd171;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0).mentries)];
                                  assert ((m0).mcommitIndex) <= (Len((log)[i]));
                                  with (result79 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m0).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result79)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result79)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0).mcommitIndex})];
                                    either {
                                      with (value671 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0).mprevLogIndex) + (Len((m0).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value671), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd172 = (fd)[j]) {
                                        await yielded_fd172;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    };
                  };
                };
              };
            };
          } else {
            if (((m0).mtype) = (AppendEntriesResponse)) {
              if (((m0).mterm) > ((currentTerm)[srvId0])) {
                currentTerm := [currentTerm EXCEPT ![srvId0] = (m0).mterm];
                state := [state EXCEPT ![srvId0] = Follower];
                votedFor := [votedFor EXCEPT ![srvId0] = Nil];
                leader := [leader EXCEPT ![srvId0] = Nil];
                if (((m0).mterm) < ((currentTerm)[srvId0])) {
                  skip;
                  goto serverLoop;
                } else {
                  with (
                    i = srvId0, 
                    j = (m0).msource
                  ) {
                    assert ((m0).mterm) = ((currentTerm)[i]);
                    if ((m0).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m0).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m0).mmatchIndex]];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                      goto serverLoop;
                    };
                  };
                };
              } else {
                if (((m0).mterm) < ((currentTerm)[srvId0])) {
                  skip;
                  goto serverLoop;
                } else {
                  with (
                    i = srvId0, 
                    j = (m0).msource
                  ) {
                    assert ((m0).mterm) = ((currentTerm)[i]);
                    if ((m0).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m0).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m0).mmatchIndex]];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                      goto serverLoop;
                    };
                  };
                };
              };
            } else {
              if ((((m0).mtype) = (ClientPutRequest)) \/ (((m0).mtype) = (ClientGetRequest))) {
                if (Debug) {
                  print <<"HandleClientRequest", srvId0, (m0).msource, (currentTerm)[srvId0], (state)[srvId0]>>;
                  if (((state)[srvId0]) = (Leader)) {
                    with (entry = [term |-> (currentTerm)[srvId0], cmd |-> (m0).mcmd, client |-> (m0).msource]) {
                      log := [log EXCEPT ![srvId0] = Append((log)[srvId0], entry)];
                      with (value70 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                        if (((value70).cmd) = (LogConcat)) {
                          plog := [plog EXCEPT ![srvId0] = ((plog)[srvId0]) \o ((value70).entries)];
                          goto serverLoop;
                        } else {
                          if (((value70).cmd) = (LogPop)) {
                            plog := [plog EXCEPT ![srvId0] = SubSeq((plog)[srvId0], 1, (Len((plog)[srvId0])) - ((value70).cnt))];
                            goto serverLoop;
                          } else {
                            goto serverLoop;
                          };
                        };
                      };
                    };
                  } else {
                    with (
                      i = srvId0, 
                      j = (m0).msource, 
                      respType = IF (((m0).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse, 
                      value80 = [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m0).mcmd).idx, key |-> ((m0).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value80), enabled |-> ((network)[j]).enabled]];
                      goto serverLoop;
                    };
                  };
                } else {
                  if (((state)[srvId0]) = (Leader)) {
                    with (entry = [term |-> (currentTerm)[srvId0], cmd |-> (m0).mcmd, client |-> (m0).msource]) {
                      log := [log EXCEPT ![srvId0] = Append((log)[srvId0], entry)];
                      with (value71 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                        if (((value71).cmd) = (LogConcat)) {
                          plog := [plog EXCEPT ![srvId0] = ((plog)[srvId0]) \o ((value71).entries)];
                          goto serverLoop;
                        } else {
                          if (((value71).cmd) = (LogPop)) {
                            plog := [plog EXCEPT ![srvId0] = SubSeq((plog)[srvId0], 1, (Len((plog)[srvId0])) - ((value71).cnt))];
                            goto serverLoop;
                          } else {
                            goto serverLoop;
                          };
                        };
                      };
                    };
                  } else {
                    with (
                      i = srvId0, 
                      j = (m0).msource, 
                      respType = IF (((m0).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse, 
                      value81 = [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m0).mcmd).idx, key |-> ((m0).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value81), enabled |-> ((network)[j]).enabled]];
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
  }
  
  fair process (s1 \in ServerRequestVoteSet)
    variables idx0 = 1; srvId1 = (requestVoteSrvId)[self];
  {
    serverRequestVoteLoop:
      if (TRUE) {
        await leaderTimeout;
        with (yielded_network00 = Len(((network)[srvId1]).queue)) {
          await (yielded_network00) = (0);
          await ((state)[srvId1]) \in ({Follower, Candidate});
          with (i1 = srvId1) {
            state := [state EXCEPT ![i1] = Candidate];
            currentTerm := [currentTerm EXCEPT ![i1] = ((currentTerm)[i1]) + (1)];
            votedFor := [votedFor EXCEPT ![i1] = i1];
            votesResponded := [votesResponded EXCEPT ![i1] = {i1}];
            votesGranted := [votesGranted EXCEPT ![i1] = {i1}];
            leader := [leader EXCEPT ![i1] = Nil];
            if (Debug) {
              print <<"ServerTimeout", i1, (currentTerm)[i1]>>;
              idx0 := 1;
              goto requestVoteLoop;
            } else {
              idx0 := 1;
              goto requestVoteLoop;
            };
          };
        };
      } else {
        goto Done;
      };
    requestVoteLoop:
      if ((idx0) <= (NumServers)) {
        if ((idx0) # (srvId1)) {
          either {
            with (value90 = [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId1], mlastLogTerm |-> LastTerm((log)[srvId1]), mlastLogIndex |-> Len((log)[srvId1]), msource |-> srvId1, mdest |-> idx0]) {
              await ((network)[idx0]).enabled;
              await (Len(((network)[idx0]).queue)) < (BufferSize);
              network := [network EXCEPT ![idx0] = [queue |-> Append(((network)[idx0]).queue, value90), enabled |-> ((network)[idx0]).enabled]];
              idx0 := (idx0) + (1);
              goto requestVoteLoop;
            };
          } or {
            with (yielded_fd20 = (fd)[idx0]) {
              await yielded_fd20;
              idx0 := (idx0) + (1);
              goto requestVoteLoop;
            };
          };
        } else {
          idx0 := (idx0) + (1);
          goto requestVoteLoop;
        };
      } else {
        goto serverRequestVoteLoop;
      };
  }
  
  fair process (s2 \in ServerAppendEntriesSet)
    variables idx1; srvId2 = (appendEntriesSrvId)[self];
  {
    serverAppendEntriesLoop:
      if (appendEntriesCh) {
        await ((state)[srvId2]) = (Leader);
        idx1 := 1;
        goto appendEntriesLoop;
      } else {
        goto Done;
      };
    appendEntriesLoop:
      if ((((state)[srvId2]) = (Leader)) /\ ((idx1) <= (NumServers))) {
        if ((idx1) # (srvId2)) {
          with (
            prevLogIndex1 = (((nextIndex)[srvId2])[idx1]) - (1), 
            prevLogTerm1 = IF (prevLogIndex1) > (0) THEN (((log)[srvId2])[prevLogIndex1]).term ELSE 0, 
            entries1 = SubSeq((log)[srvId2], ((nextIndex)[srvId2])[idx1], Len((log)[srvId2]))
          ) {
            either {
              with (value100 = [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId2], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> (commitIndex)[srvId2], msource |-> srvId2, mdest |-> idx1]) {
                await ((network)[idx1]).enabled;
                await (Len(((network)[idx1]).queue)) < (BufferSize);
                network := [network EXCEPT ![idx1] = [queue |-> Append(((network)[idx1]).queue, value100), enabled |-> ((network)[idx1]).enabled]];
                idx1 := (idx1) + (1);
                goto appendEntriesLoop;
              };
            } or {
              with (yielded_fd30 = (fd)[idx1]) {
                await yielded_fd30;
                idx1 := (idx1) + (1);
                goto appendEntriesLoop;
              };
            };
          };
        } else {
          idx1 := (idx1) + (1);
          goto appendEntriesLoop;
        };
      } else {
        goto serverAppendEntriesLoop;
      };
  }
  
  fair process (s3 \in ServerAdvanceCommitIndexSet)
    variables newCommitIndex = 0; srvId3 = (advanceCommitIndexSrvId)[self];
  {
    serverAdvanceCommitIndexLoop:
      if (TRUE) {
        await ((state)[srvId3]) = (Leader);
        with (
          i = srvId3, 
          maxAgreeIndex = FindMaxAgreeIndex((log)[i], i, (matchIndex)[i]), 
          nCommitIndex = IF ((maxAgreeIndex) # (Nil)) /\ (((((log)[i])[maxAgreeIndex]).term) = ((currentTerm)[i])) THEN maxAgreeIndex ELSE (commitIndex)[i]
        ) {
          newCommitIndex := nCommitIndex;
          assert (newCommitIndex) >= ((commitIndex)[i]);
          goto applyLoop;
        };
      } else {
        goto Done;
      };
    applyLoop:
      if (((commitIndex)[srvId3]) < (newCommitIndex)) {
        commitIndex := [commitIndex EXCEPT ![srvId3] = ((commitIndex)[srvId3]) + (1)];
        with (
          i = srvId3, 
          k = (commitIndex)[i], 
          entry = ((log)[i])[k], 
          cmd = (entry).cmd, 
          respType = IF ((cmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse
        ) {
          if (((cmd).type) = (Put)) {
            sm := [sm EXCEPT ![i] = ((sm)[i]) @@ (((cmd).key) :> ((cmd).value))];
            smDomain := [smDomain EXCEPT ![i] = ((smDomain)[i]) \union ({(cmd).key})];
            with (
              reqOk = ((cmd).key) \in ((smDomain)[i]), 
              value110 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value110), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          } else {
            with (
              reqOk = ((cmd).key) \in ((smDomain)[i]), 
              value111 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value111), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          };
        };
      } else {
        goto serverAdvanceCommitIndexLoop;
      };
  }
  
  fair process (s4 \in ServerBecomeLeaderSet)
    variables srvId4 = (becomeLeaderSrvId)[self];
  {
    serverBecomeLeaderLoop:
      await (Len((becomeLeaderCh)[srvId4])) > (0);
      with (res1 = Head((becomeLeaderCh)[srvId4])) {
        becomeLeaderCh := [becomeLeaderCh EXCEPT ![srvId4] = Tail((becomeLeaderCh)[srvId4])];
        with (yielded_becomeLeaderCh = res1) {
          if (yielded_becomeLeaderCh) {
            await ((state)[srvId4]) = (Candidate);
            await isQuorum((votesGranted)[srvId4]);
            with (i = srvId4) {
              state := [state EXCEPT ![i] = Leader];
              nextIndex := [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]];
              matchIndex := [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]];
              leader := [leader EXCEPT ![i] = i];
              appendEntriesCh := TRUE;
              if (Debug) {
                print <<"BecomeLeader", i, (currentTerm)[i], (state)[i], (leader)[i]>>;
                goto serverBecomeLeaderLoop;
              } else {
                goto serverBecomeLeaderLoop;
              };
            };
          } else {
            goto Done;
          };
        };
      };
  }
  
  fair process (client \in ClientSet)
    variables leader0 = Nil; req; resp; reqIdx = 0; timeout = FALSE;
  {
    clientLoop:
      if (TRUE) {
        await (Len(reqCh)) > (0);
        with (res20 = Head(reqCh)) {
          reqCh := Tail(reqCh);
          with (yielded_reqCh0 = res20) {
            req := yielded_reqCh0;
            reqIdx := (reqIdx) + (1);
            goto sndReq;
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
            print <<"ClientSndReq", self, leader0, reqIdx, req>>;
            if (((req).type) = (Put)) {
              either {
                with (value120 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value120), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd40 = (fd)[leader0]) {
                  await yielded_fd40;
                  goto rcvResp;
                };
              };
            } else {
              if (((req).type) = (Get)) {
                either {
                  with (value130 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
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
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Put)) {
              either {
                with (value121 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value121), enabled |-> ((network)[leader0]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd41 = (fd)[leader0]) {
                  await yielded_fd41;
                  goto rcvResp;
                };
              };
            } else {
              if (((req).type) = (Get)) {
                either {
                  with (value131 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
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
                goto rcvResp;
              };
            };
          };
        };
      } else {
        if (Debug) {
          print <<"ClientSndReq", self, leader0, reqIdx, req>>;
          if (((req).type) = (Put)) {
            either {
              with (value122 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value122), enabled |-> ((network)[leader0]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd42 = (fd)[leader0]) {
                await yielded_fd42;
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Get)) {
              either {
                with (value132 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
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
              goto rcvResp;
            };
          };
        } else {
          if (((req).type) = (Put)) {
            either {
              with (value123 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value123), enabled |-> ((network)[leader0]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd43 = (fd)[leader0]) {
                await yielded_fd43;
                goto rcvResp;
              };
            };
          } else {
            if (((req).type) = (Get)) {
              either {
                with (value133 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
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
              goto rcvResp;
            };
          };
        };
      };
    rcvResp:
      either {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg10 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network10 = readMsg10) {
            resp := yielded_network10;
            if (Debug) {
              print <<"ClientRcvResp", self, leader0, reqIdx, resp>>;
              assert ((resp).mdest) = (self);
              if ((((resp).mresponse).idx) # (reqIdx)) {
                goto rcvResp;
              } else {
                leader0 := (resp).mleaderHint;
                assert ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)));
                if (~ ((resp).msuccess)) {
                  goto sndReq;
                } else {
                  assert ((((resp).mresponse).idx) = (reqIdx)) /\ ((((resp).mresponse).key) = ((req).key));
                  respCh := resp;
                  if (Debug) {
                    print <<"ClientRcvChDone", self, leader0, reqIdx, resp>>;
                    goto clientLoop;
                  } else {
                    goto clientLoop;
                  };
                };
              };
            } else {
              assert ((resp).mdest) = (self);
              if ((((resp).mresponse).idx) # (reqIdx)) {
                goto rcvResp;
              } else {
                leader0 := (resp).mleaderHint;
                assert ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)));
                if (~ ((resp).msuccess)) {
                  goto sndReq;
                } else {
                  assert ((((resp).mresponse).idx) = (reqIdx)) /\ ((((resp).mresponse).key) = ((req).key));
                  respCh := resp;
                  if (Debug) {
                    print <<"ClientRcvChDone", self, leader0, reqIdx, resp>>;
                    goto clientLoop;
                  } else {
                    goto clientLoop;
                  };
                };
              };
            };
          };
        };
      } or {
        with (
          yielded_fd60 = (fd)[leader0], 
          yielded_network20 = Len(((network)[self]).queue)
        ) {
          await ((yielded_fd60) /\ ((yielded_network20) = (0))) \/ (timeout);
          if (Debug) {
            print <<"ClientTimeout", self, leader0, reqIdx>>;
            leader0 := Nil;
            goto sndReq;
          } else {
            leader0 := Nil;
            goto sndReq;
          };
        };
      };
  }
  
  fair process (crasher \in ServerCrasherSet)
    variables srvId5 = (crasherSrvId)[self];
  {
    serverCrash:
      with (value140 = FALSE) {
        network := [network EXCEPT ![srvId5] = [queue |-> ((network)[srvId5]).queue, enabled |-> value140]];
        goto fdUpdate;
      };
    fdUpdate:
      with (value150 = TRUE) {
        fd := [fd EXCEPT ![srvId5] = value150];
        goto block;
      };
    block:
      await FALSE;
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "752611bb" /\ chksum(tla) = "4486f488") PCal-18049938ece8066a38eb5044080cf45c
CONSTANT defaultInitValue
VARIABLES network, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, 
          log, plog, votedFor, votesResponded, votesGranted, leader, sm, 
          smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, handlerCh, 
          allReqs, reqCh, respCh, requestVoteSrvId, appendEntriesSrvId, 
          advanceCommitIndexSrvId, becomeLeaderSrvId, handlerSrvId, 
          crasherSrvId, pc

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
ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
ServerHandlerSet == (((5) * (NumServers)) + (1)) .. (((5) * (NumServers)) + ((NumHandlers) * (NumServers)))
ServerCrasherSet == IF ExploreFail THEN ((((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (1)) .. ((((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (MaxNodeFail)) ELSE {}
ServerOffset == (((5) * (NumServers)) + ((NumHandlers) * (NumServers))) + (MaxNodeFail)
ClientSet == ((ServerOffset) + (1)) .. ((ServerOffset) + (NumClients))
NodeSet == (ServerSet) \union (ClientSet)
KeySet == {}

VARIABLES m, srvId, idx, m0, srvId0, idx0, srvId1, idx1, srvId2, 
          newCommitIndex, srvId3, srvId4, leader0, req, resp, reqIdx, timeout, 
          srvId5

vars == << network, fd, state, currentTerm, commitIndex, nextIndex, 
           matchIndex, log, plog, votedFor, votesResponded, votesGranted, 
           leader, sm, smDomain, leaderTimeout, appendEntriesCh, 
           becomeLeaderCh, handlerCh, allReqs, reqCh, respCh, 
           requestVoteSrvId, appendEntriesSrvId, advanceCommitIndexSrvId, 
           becomeLeaderSrvId, handlerSrvId, crasherSrvId, pc, m, srvId, idx, 
           m0, srvId0, idx0, srvId1, idx1, srvId2, newCommitIndex, srvId3, 
           srvId4, leader0, req, resp, reqIdx, timeout, srvId5 >>

ProcSet == (ServerSet) \cup (ServerHandlerSet) \cup (ServerRequestVoteSet) \cup (ServerAppendEntriesSet) \cup (ServerAdvanceCommitIndexSet) \cup (ServerBecomeLeaderSet) \cup (ClientSet) \cup (ServerCrasherSet)

Init == (* Global variables *)
        /\ network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [i \in ServerSet |-> FALSE]
        /\ state = [i \in ServerSet |-> Follower]
        /\ currentTerm = [i \in ServerSet |-> 1]
        /\ commitIndex = [i \in ServerSet |-> 0]
        /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
        /\ matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]
        /\ log = [i \in ServerSet |-> <<>>]
        /\ plog = [i \in ServerSet |-> <<>>]
        /\ votedFor = [i \in ServerSet |-> Nil]
        /\ votesResponded = [i \in ServerSet |-> {}]
        /\ votesGranted = [i \in ServerSet |-> {}]
        /\ leader = [i \in ServerSet |-> Nil]
        /\ sm = [i \in ServerSet |-> [k \in KeySet |-> Nil]]
        /\ smDomain = [i \in ServerSet |-> KeySet]
        /\ leaderTimeout = TRUE
        /\ appendEntriesCh = TRUE
        /\ becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]
        /\ handlerCh = [i \in ServerSet |-> <<>>]
        /\ allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>
        /\ reqCh = SubSeq(allReqs, 1, NumRequests)
        /\ respCh = defaultInitValue
        /\ requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]
        /\ appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]
        /\ advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]
        /\ becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]
        /\ handlerSrvId = [i \in ServerHandlerSet |-> ((((i) - ((5) * (NumServers))) - (1)) \div (NumHandlers)) + (1)]
        /\ crasherSrvId = [i \in ServerCrasherSet |-> ((i) - ((5) * (NumServers))) - ((NumHandlers) * (NumServers))]
        (* Process s00 *)
        /\ m = [self \in ServerSet |-> defaultInitValue]
        /\ srvId = [self \in ServerSet |-> self]
        (* Process s01 *)
        /\ idx = [self \in ServerHandlerSet |-> 1]
        /\ m0 = [self \in ServerHandlerSet |-> defaultInitValue]
        /\ srvId0 = [self \in ServerHandlerSet |-> (handlerSrvId)[self]]
        (* Process s1 *)
        /\ idx0 = [self \in ServerRequestVoteSet |-> 1]
        /\ srvId1 = [self \in ServerRequestVoteSet |-> (requestVoteSrvId)[self]]
        (* Process s2 *)
        /\ idx1 = [self \in ServerAppendEntriesSet |-> defaultInitValue]
        /\ srvId2 = [self \in ServerAppendEntriesSet |-> (appendEntriesSrvId)[self]]
        (* Process s3 *)
        /\ newCommitIndex = [self \in ServerAdvanceCommitIndexSet |-> 0]
        /\ srvId3 = [self \in ServerAdvanceCommitIndexSet |-> (advanceCommitIndexSrvId)[self]]
        (* Process s4 *)
        /\ srvId4 = [self \in ServerBecomeLeaderSet |-> (becomeLeaderSrvId)[self]]
        (* Process client *)
        /\ leader0 = [self \in ClientSet |-> Nil]
        /\ req = [self \in ClientSet |-> defaultInitValue]
        /\ resp = [self \in ClientSet |-> defaultInitValue]
        /\ reqIdx = [self \in ClientSet |-> 0]
        /\ timeout = [self \in ClientSet |-> FALSE]
        (* Process crasher *)
        /\ srvId5 = [self \in ServerCrasherSet |-> (crasherSrvId)[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "listenerLoop"
                                        [] self \in ServerHandlerSet -> "serverLoop"
                                        [] self \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                                        [] self \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                                        [] self \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                                        [] self \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                                        [] self \in ClientSet -> "clientLoop"
                                        [] self \in ServerCrasherSet -> "serverCrash"]

listenerLoop(self) == /\ pc[self] = "listenerLoop"
                      /\ IF TRUE
                            THEN /\ Assert(((network)[srvId[self]]).enabled, 
                                           "Failure of assertion at line 1026, column 9.")
                                 /\ (Len(((network)[srvId[self]]).queue)) > (0)
                                 /\ LET readMsg00 == Head(((network)[srvId[self]]).queue) IN
                                      /\ network' = [network EXCEPT ![srvId[self]] = [queue |-> Tail(((network)[srvId[self]]).queue), enabled |-> ((network)[srvId[self]]).enabled]]
                                      /\ LET yielded_network3 == readMsg00 IN
                                           /\ m' = [m EXCEPT ![self] = yielded_network3]
                                           /\ Assert(((m'[self]).mdest) = (srvId[self]), 
                                                     "Failure of assertion at line 1032, column 13.")
                                           /\ LET value00 == m'[self] IN
                                                /\ handlerCh' = [handlerCh EXCEPT ![srvId[self]] = Append((handlerCh)[srvId[self]], value00)]
                                                /\ pc' = [pc EXCEPT ![self] = "listenerLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << network, handlerCh, m >>
                      /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                      nextIndex, matchIndex, log, plog, 
                                      votedFor, votesResponded, votesGranted, 
                                      leader, sm, smDomain, leaderTimeout, 
                                      appendEntriesCh, becomeLeaderCh, allReqs, 
                                      reqCh, respCh, requestVoteSrvId, 
                                      appendEntriesSrvId, 
                                      advanceCommitIndexSrvId, 
                                      becomeLeaderSrvId, handlerSrvId, 
                                      crasherSrvId, srvId, idx, m0, srvId0, 
                                      idx0, srvId1, idx1, srvId2, 
                                      newCommitIndex, srvId3, srvId4, leader0, 
                                      req, resp, reqIdx, timeout, srvId5 >>

s00(self) == listenerLoop(self)

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ (Len((handlerCh)[srvId0[self]])) > (0)
                               /\ LET res00 == Head((handlerCh)[srvId0[self]]) IN
                                    /\ handlerCh' = [handlerCh EXCEPT ![srvId0[self]] = Tail((handlerCh)[srvId0[self]])]
                                    /\ LET yielded_handlerCh0 == res00 IN
                                         /\ m0' = [m0 EXCEPT ![self] = yielded_handlerCh0]
                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << handlerCh, m0 >>
                    /\ UNCHANGED << network, fd, state, currentTerm, 
                                    commitIndex, nextIndex, matchIndex, log, 
                                    plog, votedFor, votesResponded, 
                                    votesGranted, leader, sm, smDomain, 
                                    leaderTimeout, appendEntriesCh, 
                                    becomeLeaderCh, allReqs, reqCh, respCh, 
                                    requestVoteSrvId, appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    handlerSrvId, crasherSrvId, m, srvId, idx, 
                                    srvId0, idx0, srvId1, idx1, srvId2, 
                                    newCommitIndex, srvId3, srvId4, leader0, 
                                    req, resp, reqIdx, timeout, srvId5 >>

handleMsg(self) == /\ pc[self] = "handleMsg"
                   /\ IF ((m0[self]).mtype) = (RequestVoteRequest)
                         THEN /\ IF ((m0[self]).mterm) > ((currentTerm)[srvId0[self]])
                                    THEN /\ currentTerm' = [currentTerm EXCEPT ![srvId0[self]] = (m0[self]).mterm]
                                         /\ state' = [state EXCEPT ![srvId0[self]] = Follower]
                                         /\ LET votedFor1 == [votedFor EXCEPT ![srvId0[self]] = Nil] IN
                                              /\ leader' = [leader EXCEPT ![srvId0[self]] = Nil]
                                              /\ LET i == srvId0[self] IN
                                                   LET j == (m0[self]).msource IN
                                                     LET logOK == (((m0[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m0[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m0[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                       LET grant == ((((m0[self]).mterm) = ((currentTerm')[i])) /\ (logOK)) /\ (((votedFor1)[srvId0[self]]) \in ({Nil, j})) IN
                                                         /\ Assert(((m0[self]).mterm) <= ((currentTerm')[i]), 
                                                                   "Failure of assertion at line 1073, column 15.")
                                                         /\ IF grant
                                                               THEN /\ votedFor' = [votedFor1 EXCEPT ![i] = j]
                                                                    /\ \/ /\ LET value16 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]]
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       \/ /\ LET yielded_fd7 == (fd)[j] IN
                                                                               /\ yielded_fd7
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED network
                                                               ELSE /\ \/ /\ LET value17 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]]
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       \/ /\ LET yielded_fd8 == (fd)[j] IN
                                                                               /\ yielded_fd8
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED network
                                    ELSE /\ LET i == srvId0[self] IN
                                              LET j == (m0[self]).msource IN
                                                LET logOK == (((m0[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m0[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m0[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                  LET grant == ((((m0[self]).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[srvId0[self]]) \in ({Nil, j})) IN
                                                    /\ Assert(((m0[self]).mterm) <= ((currentTerm)[i]), 
                                                              "Failure of assertion at line 1137, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                                               /\ \/ /\ LET value18 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]]
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd9 == (fd)[j] IN
                                                                          /\ yielded_fd9
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                          ELSE /\ \/ /\ LET value19 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value19), enabled |-> ((network)[j]).enabled]]
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd10 == (fd)[j] IN
                                                                          /\ yielded_fd10
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << state, currentTerm, 
                                                         leader >>
                              /\ UNCHANGED << commitIndex, nextIndex, 
                                              matchIndex, log, plog, 
                                              votesResponded, votesGranted, sm, 
                                              smDomain, leaderTimeout, 
                                              becomeLeaderCh >>
                         ELSE /\ IF ((m0[self]).mtype) = (RequestVoteResponse)
                                    THEN /\ IF ((m0[self]).mterm) > ((currentTerm)[srvId0[self]])
                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![srvId0[self]] = (m0[self]).mterm]
                                                    /\ state' = [state EXCEPT ![srvId0[self]] = Follower]
                                                    /\ votedFor' = [votedFor EXCEPT ![srvId0[self]] = Nil]
                                                    /\ leader' = [leader EXCEPT ![srvId0[self]] = Nil]
                                                    /\ IF ((m0[self]).mterm) < ((currentTerm')[srvId0[self]])
                                                          THEN /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted, 
                                                                               becomeLeaderCh >>
                                                          ELSE /\ LET i == srvId0[self] IN
                                                                    LET j == (m0[self]).msource IN
                                                                      /\ Assert(((m0[self]).mterm) = ((currentTerm')[i]), 
                                                                                "Failure of assertion at line 1205, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m0[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state')[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value20 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value20)]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            /\ UNCHANGED becomeLeaderCh
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED << votesGranted, 
                                                                                                 becomeLeaderCh >>
                                               ELSE /\ IF ((m0[self]).mterm) < ((currentTerm)[srvId0[self]])
                                                          THEN /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted, 
                                                                               becomeLeaderCh >>
                                                          ELSE /\ LET i == srvId0[self] IN
                                                                    LET j == (m0[self]).msource IN
                                                                      /\ Assert(((m0[self]).mterm) = ((currentTerm)[i]), 
                                                                                "Failure of assertion at line 1231, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m0[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value21 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value21)]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            /\ UNCHANGED becomeLeaderCh
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED << votesGranted, 
                                                                                                 becomeLeaderCh >>
                                                    /\ UNCHANGED << state, 
                                                                    currentTerm, 
                                                                    votedFor, 
                                                                    leader >>
                                         /\ UNCHANGED << network, commitIndex, 
                                                         nextIndex, matchIndex, 
                                                         log, plog, sm, 
                                                         smDomain, 
                                                         leaderTimeout >>
                                    ELSE /\ IF ((m0[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m0[self]).mterm) > ((currentTerm)[srvId0[self]])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![srvId0[self]] = (m0[self]).mterm]
                                                               /\ LET state1 == [state EXCEPT ![srvId0[self]] = Follower] IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![srvId0[self]] = Nil]
                                                                    /\ LET leader1 == [leader EXCEPT ![srvId0[self]] = Nil] IN
                                                                         LET i == srvId0[self] IN
                                                                           LET j == (m0[self]).msource IN
                                                                             LET logOK == (((m0[self]).mprevLogIndex) = (0)) \/ (((((m0[self]).mprevLogIndex) > (0)) /\ (((m0[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m0[self]).mprevLogTerm) = ((((log)[i])[(m0[self]).mprevLogIndex]).term))) IN
                                                                               /\ Assert(((m0[self]).mterm) <= ((currentTerm')[i]), 
                                                                                         "Failure of assertion at line 1261, column 19.")
                                                                               /\ IF ((m0[self]).mterm) = ((currentTerm')[i])
                                                                                     THEN /\ leader' = [leader1 EXCEPT ![i] = (m0[self]).msource]
                                                                                          /\ leaderTimeout' = LeaderTimeoutReset
                                                                                          /\ IF (((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                                THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                                     /\ IF (((m0[self]).mterm) < ((currentTerm')[i])) \/ (((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                           THEN /\ \/ /\ LET value30 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value30), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                                                                           /\ yielded_fd00
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      /\ UNCHANGED network
                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                log, 
                                                                                                                                plog, 
                                                                                                                                sm, 
                                                                                                                                smDomain >>
                                                                                                           ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                          "Failure of assertion at line 1282, column 25.")
                                                                                                                /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                                     LET value40 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                       IF ((value40).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog8 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value40).entries)] IN
                                                                                                                                    LET log8 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                      LET value50 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                        IF ((value50).cmd) = (LogConcat)
                                                                                                                                           THEN /\ plog' = [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value50).entries)]
                                                                                                                                                /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                          "Failure of assertion at line 1296, column 33.")
                                                                                                                                                /\ LET result8 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result8)[1]]
                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result8)[2]]
                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                     /\ \/ /\ LET value60 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value60), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                                                                                /\ yielded_fd11
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                           ELSE /\ IF ((value50).cmd) = (LogPop)
                                                                                                                                                      THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - ((value50).cnt))]
                                                                                                                                                           /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1319, column 35.")
                                                                                                                                                           /\ LET result9 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result9)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result9)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value61 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value61), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd12
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1340, column 35.")
                                                                                                                                                           /\ LET result10 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result10)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result10)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value62 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value62), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ plog' = plog8
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd13
                                                                                                                                                                           /\ plog' = plog8
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                          ELSE /\ IF ((value40).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value40).cnt))] IN
                                                                                                                                               LET log9 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                                 LET value51 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                   IF ((value51).cmd) = (LogConcat)
                                                                                                                                                      THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value51).entries)]
                                                                                                                                                           /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1374, column 35.")
                                                                                                                                                           /\ LET result11 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result11)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result11)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value63 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value63), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd14 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd14
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ IF ((value51).cmd) = (LogPop)
                                                                                                                                                                 THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - ((value51).cnt))]
                                                                                                                                                                      /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1397, column 37.")
                                                                                                                                                                      /\ LET result12 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result12)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result12)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value64 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value64), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd15 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd15
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                                                 ELSE /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1418, column 37.")
                                                                                                                                                                      /\ LET result13 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result13)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result13)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value65 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value65), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ plog' = plog9
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd16 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd16
                                                                                                                                                                                      /\ plog' = plog9
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                     ELSE /\ LET log10 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                               LET value52 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                 IF ((value52).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value52).entries)]
                                                                                                                                                         /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                   "Failure of assertion at line 1450, column 35.")
                                                                                                                                                         /\ LET result14 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result14)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result14)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value66 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value66), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd17 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd17
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ IF ((value52).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value52).cnt))]
                                                                                                                                                                    /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 1473, column 37.")
                                                                                                                                                                    /\ LET result15 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result15)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result15)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value67 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value67), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd18 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd18
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 1494, column 37.")
                                                                                                                                                                    /\ LET result16 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result16)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result16)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value68 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value68), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd19 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd19
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                    /\ plog' = plog
                                                                                                ELSE /\ IF (((m0[self]).mterm) < ((currentTerm')[i])) \/ (((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                           THEN /\ \/ /\ LET value31 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value31), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ state' = state1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   \/ /\ LET yielded_fd01 == (fd)[j] IN
                                                                                                                           /\ yielded_fd01
                                                                                                                           /\ state' = state1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      /\ UNCHANGED network
                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                log, 
                                                                                                                                plog, 
                                                                                                                                sm, 
                                                                                                                                smDomain >>
                                                                                                           ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                          "Failure of assertion at line 1538, column 25.")
                                                                                                                /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                                     LET value41 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                       IF ((value41).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog10 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value41).entries)] IN
                                                                                                                                    LET log11 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                      LET value53 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                        IF ((value53).cmd) = (LogConcat)
                                                                                                                                           THEN /\ plog' = [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value53).entries)]
                                                                                                                                                /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                          "Failure of assertion at line 1552, column 33.")
                                                                                                                                                /\ LET result17 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result17)[1]]
                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result17)[2]]
                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                     /\ \/ /\ LET value69 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value69), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                /\ state' = state1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        \/ /\ LET yielded_fd110 == (fd)[j] IN
                                                                                                                                                                /\ yielded_fd110
                                                                                                                                                                /\ state' = state1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                           ELSE /\ IF ((value53).cmd) = (LogPop)
                                                                                                                                                      THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - ((value53).cnt))]
                                                                                                                                                           /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1577, column 35.")
                                                                                                                                                           /\ LET result18 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result18)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result18)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value610 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value610), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd111 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd111
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1600, column 35.")
                                                                                                                                                           /\ LET result19 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result19)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result19)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value611 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value611), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ plog' = plog10
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd112 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd112
                                                                                                                                                                           /\ plog' = plog10
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                          ELSE /\ IF ((value41).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value41).cnt))] IN
                                                                                                                                               LET log12 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                                 LET value54 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                   IF ((value54).cmd) = (LogConcat)
                                                                                                                                                      THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value54).entries)]
                                                                                                                                                           /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1636, column 35.")
                                                                                                                                                           /\ LET result20 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result20)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result20)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value612 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value612), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd113 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd113
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ IF ((value54).cmd) = (LogPop)
                                                                                                                                                                 THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - ((value54).cnt))]
                                                                                                                                                                      /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1661, column 37.")
                                                                                                                                                                      /\ LET result21 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result21)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result21)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value613 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value613), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd114 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd114
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                                                 ELSE /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1684, column 37.")
                                                                                                                                                                      /\ LET result22 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result22)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result22)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value614 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value614), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ plog' = plog11
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd115 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd115
                                                                                                                                                                                      /\ plog' = plog11
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                     ELSE /\ LET log13 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                               LET value55 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                 IF ((value55).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value55).entries)]
                                                                                                                                                         /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                   "Failure of assertion at line 1718, column 35.")
                                                                                                                                                         /\ LET result23 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result23)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result23)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value615 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value615), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd116 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd116
                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ IF ((value55).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value55).cnt))]
                                                                                                                                                                    /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 1743, column 37.")
                                                                                                                                                                    /\ LET result24 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result24)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result24)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value616 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value616), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd117 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd117
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 1766, column 37.")
                                                                                                                                                                    /\ LET result25 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result25)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result25)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value617 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value617), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd118 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd118
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                    /\ plog' = plog
                                                                                     ELSE /\ IF (((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                                THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                                     /\ IF (((m0[self]).mterm) < ((currentTerm')[i])) \/ (((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                           THEN /\ \/ /\ LET value32 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value32), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ leader' = leader1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                                                                           /\ yielded_fd02
                                                                                                                           /\ leader' = leader1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      /\ UNCHANGED network
                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                log, 
                                                                                                                                plog, 
                                                                                                                                sm, 
                                                                                                                                smDomain >>
                                                                                                           ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                          "Failure of assertion at line 1815, column 25.")
                                                                                                                /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                                     LET value42 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                       IF ((value42).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog12 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value42).entries)] IN
                                                                                                                                    LET log14 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                      LET value56 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                        IF ((value56).cmd) = (LogConcat)
                                                                                                                                           THEN /\ plog' = [plog12 EXCEPT ![i] = ((plog12)[i]) \o ((value56).entries)]
                                                                                                                                                /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                          "Failure of assertion at line 1829, column 33.")
                                                                                                                                                /\ LET result26 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result26)[1]]
                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result26)[2]]
                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                     /\ \/ /\ LET value618 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value618), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                /\ leader' = leader1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        \/ /\ LET yielded_fd119 == (fd)[j] IN
                                                                                                                                                                /\ yielded_fd119
                                                                                                                                                                /\ leader' = leader1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                           ELSE /\ IF ((value56).cmd) = (LogPop)
                                                                                                                                                      THEN /\ plog' = [plog12 EXCEPT ![i] = SubSeq((plog12)[i], 1, (Len((plog12)[i])) - ((value56).cnt))]
                                                                                                                                                           /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1854, column 35.")
                                                                                                                                                           /\ LET result27 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result27)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result27)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value619 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value619), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd120 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd120
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1877, column 35.")
                                                                                                                                                           /\ LET result28 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result28)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result28)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value620 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value620), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ plog' = plog12
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd121 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd121
                                                                                                                                                                           /\ plog' = plog12
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                          ELSE /\ IF ((value42).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog13 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value42).cnt))] IN
                                                                                                                                               LET log15 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                                 LET value57 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                   IF ((value57).cmd) = (LogConcat)
                                                                                                                                                      THEN /\ plog' = [plog13 EXCEPT ![i] = ((plog13)[i]) \o ((value57).entries)]
                                                                                                                                                           /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 1913, column 35.")
                                                                                                                                                           /\ LET result29 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result29)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result29)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value621 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value621), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd122 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd122
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ IF ((value57).cmd) = (LogPop)
                                                                                                                                                                 THEN /\ plog' = [plog13 EXCEPT ![i] = SubSeq((plog13)[i], 1, (Len((plog13)[i])) - ((value57).cnt))]
                                                                                                                                                                      /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1938, column 37.")
                                                                                                                                                                      /\ LET result30 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result30)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result30)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value622 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value622), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd123 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd123
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                                                 ELSE /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 1961, column 37.")
                                                                                                                                                                      /\ LET result31 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result31)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result31)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value623 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value623), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ plog' = plog13
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd124 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd124
                                                                                                                                                                                      /\ plog' = plog13
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                     ELSE /\ LET log16 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                               LET value58 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                 IF ((value58).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value58).entries)]
                                                                                                                                                         /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                   "Failure of assertion at line 1995, column 35.")
                                                                                                                                                         /\ LET result32 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result32)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result32)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value624 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value624), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ leader' = leader1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd125 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd125
                                                                                                                                                                         /\ leader' = leader1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ IF ((value58).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value58).cnt))]
                                                                                                                                                                    /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 2020, column 37.")
                                                                                                                                                                    /\ LET result33 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result33)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result33)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value625 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value625), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd126 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd126
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 2043, column 37.")
                                                                                                                                                                    /\ LET result34 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result34)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result34)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value626 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value626), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd127 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd127
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                    /\ plog' = plog
                                                                                                ELSE /\ IF (((m0[self]).mterm) < ((currentTerm')[i])) \/ (((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                           THEN /\ \/ /\ LET value33 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value33), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ leader' = leader1
                                                                                                                           /\ state' = state1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                                                                           /\ yielded_fd03
                                                                                                                           /\ leader' = leader1
                                                                                                                           /\ state' = state1
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      /\ UNCHANGED network
                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                log, 
                                                                                                                                plog, 
                                                                                                                                sm, 
                                                                                                                                smDomain >>
                                                                                                           ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                          "Failure of assertion at line 2091, column 25.")
                                                                                                                /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                                     LET value43 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                       IF ((value43).cmd) = (LogConcat)
                                                                                                                          THEN /\ LET plog14 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value43).entries)] IN
                                                                                                                                    LET log17 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                      LET value59 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                        IF ((value59).cmd) = (LogConcat)
                                                                                                                                           THEN /\ plog' = [plog14 EXCEPT ![i] = ((plog14)[i]) \o ((value59).entries)]
                                                                                                                                                /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                          "Failure of assertion at line 2105, column 33.")
                                                                                                                                                /\ LET result35 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result35)[1]]
                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result35)[2]]
                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                     /\ \/ /\ LET value627 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value627), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                /\ leader' = leader1
                                                                                                                                                                /\ state' = state1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        \/ /\ LET yielded_fd128 == (fd)[j] IN
                                                                                                                                                                /\ yielded_fd128
                                                                                                                                                                /\ leader' = leader1
                                                                                                                                                                /\ state' = state1
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                           ELSE /\ IF ((value59).cmd) = (LogPop)
                                                                                                                                                      THEN /\ plog' = [plog14 EXCEPT ![i] = SubSeq((plog14)[i], 1, (Len((plog14)[i])) - ((value59).cnt))]
                                                                                                                                                           /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 2132, column 35.")
                                                                                                                                                           /\ LET result36 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result36)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result36)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value628 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value628), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd129 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd129
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 2157, column 35.")
                                                                                                                                                           /\ LET result37 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result37)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result37)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value629 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value629), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ plog' = plog14
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd130 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd130
                                                                                                                                                                           /\ plog' = plog14
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                          ELSE /\ IF ((value43).cmd) = (LogPop)
                                                                                                                                     THEN /\ LET plog15 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value43).cnt))] IN
                                                                                                                                               LET log18 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                                 LET value510 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                   IF ((value510).cmd) = (LogConcat)
                                                                                                                                                      THEN /\ plog' = [plog15 EXCEPT ![i] = ((plog15)[i]) \o ((value510).entries)]
                                                                                                                                                           /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                           /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                     "Failure of assertion at line 2195, column 35.")
                                                                                                                                                           /\ LET result38 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result38)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result38)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value630 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value630), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd131 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd131
                                                                                                                                                                           /\ leader' = leader1
                                                                                                                                                                           /\ state' = state1
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ IF ((value510).cmd) = (LogPop)
                                                                                                                                                                 THEN /\ plog' = [plog15 EXCEPT ![i] = SubSeq((plog15)[i], 1, (Len((plog15)[i])) - ((value510).cnt))]
                                                                                                                                                                      /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 2222, column 37.")
                                                                                                                                                                      /\ LET result39 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result39)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result39)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value631 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value631), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd132 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd132
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                                                 ELSE /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                      /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                "Failure of assertion at line 2247, column 37.")
                                                                                                                                                                      /\ LET result40 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result40)[1]]
                                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result40)[2]]
                                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                           /\ \/ /\ LET value632 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                      /\ ((network)[j]).enabled
                                                                                                                                                                                      /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                      /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value632), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                      /\ plog' = plog15
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              \/ /\ LET yielded_fd133 == (fd)[j] IN
                                                                                                                                                                                      /\ yielded_fd133
                                                                                                                                                                                      /\ plog' = plog15
                                                                                                                                                                                      /\ leader' = leader1
                                                                                                                                                                                      /\ state' = state1
                                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED network
                                                                                                                                     ELSE /\ LET log19 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                               LET value511 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                                 IF ((value511).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value511).entries)]
                                                                                                                                                         /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                   "Failure of assertion at line 2283, column 35.")
                                                                                                                                                         /\ LET result41 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result41)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result41)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value633 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value633), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ leader' = leader1
                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd134 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd134
                                                                                                                                                                         /\ leader' = leader1
                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ IF ((value511).cmd) = (LogPop)
                                                                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value511).cnt))]
                                                                                                                                                                    /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 2310, column 37.")
                                                                                                                                                                    /\ LET result42 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result42)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result42)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value634 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value634), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd135 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd135
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                               ELSE /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                              "Failure of assertion at line 2335, column 37.")
                                                                                                                                                                    /\ LET result43 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result43)[1]]
                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result43)[2]]
                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                         /\ \/ /\ LET value635 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value635), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            \/ /\ LET yielded_fd136 == (fd)[j] IN
                                                                                                                                                                                    /\ yielded_fd136
                                                                                                                                                                                    /\ leader' = leader1
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                    /\ plog' = plog
                                                                                          /\ UNCHANGED leaderTimeout
                                                          ELSE /\ LET i == srvId0[self] IN
                                                                    LET j == (m0[self]).msource IN
                                                                      LET logOK == (((m0[self]).mprevLogIndex) = (0)) \/ (((((m0[self]).mprevLogIndex) > (0)) /\ (((m0[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m0[self]).mprevLogTerm) = ((((log)[i])[(m0[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m0[self]).mterm) <= ((currentTerm)[i]), 
                                                                                  "Failure of assertion at line 2375, column 17.")
                                                                        /\ IF ((m0[self]).mterm) = ((currentTerm)[i])
                                                                              THEN /\ leader' = [leader EXCEPT ![i] = (m0[self]).msource]
                                                                                   /\ leaderTimeout' = LeaderTimeoutReset
                                                                                   /\ IF (((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                                         THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                              /\ IF (((m0[self]).mterm) < ((currentTerm)[i])) \/ (((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                    THEN /\ \/ /\ LET value34 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value34), enabled |-> ((network)[j]).enabled]]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                            \/ /\ LET yielded_fd04 == (fd)[j] IN
                                                                                                                    /\ yielded_fd04
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               /\ UNCHANGED network
                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                         log, 
                                                                                                                         plog, 
                                                                                                                         sm, 
                                                                                                                         smDomain >>
                                                                                                    ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                   "Failure of assertion at line 2396, column 23.")
                                                                                                         /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                              LET value44 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                IF ((value44).cmd) = (LogConcat)
                                                                                                                   THEN /\ LET plog16 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value44).entries)] IN
                                                                                                                             LET log20 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                               LET value512 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                 IF ((value512).cmd) = (LogConcat)
                                                                                                                                    THEN /\ plog' = [plog16 EXCEPT ![i] = ((plog16)[i]) \o ((value512).entries)]
                                                                                                                                         /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0[self]).mentries)]
                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                   "Failure of assertion at line 2410, column 31.")
                                                                                                                                         /\ LET result44 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result44)[1]]
                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result44)[2]]
                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                              /\ \/ /\ LET value636 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value636), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 \/ /\ LET yielded_fd137 == (fd)[j] IN
                                                                                                                                                         /\ yielded_fd137
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                    ELSE /\ IF ((value512).cmd) = (LogPop)
                                                                                                                                               THEN /\ plog' = [plog16 EXCEPT ![i] = SubSeq((plog16)[i], 1, (Len((plog16)[i])) - ((value512).cnt))]
                                                                                                                                                    /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2433, column 33.")
                                                                                                                                                    /\ LET result45 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result45)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result45)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value637 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value637), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd138 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd138
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2454, column 33.")
                                                                                                                                                    /\ LET result46 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result46)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result46)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value638 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value638), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ plog' = plog16
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd139 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd139
                                                                                                                                                                    /\ plog' = plog16
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                   ELSE /\ IF ((value44).cmd) = (LogPop)
                                                                                                                              THEN /\ LET plog17 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value44).cnt))] IN
                                                                                                                                        LET log21 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                          LET value513 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                            IF ((value513).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog17 EXCEPT ![i] = ((plog17)[i]) \o ((value513).entries)]
                                                                                                                                                    /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2488, column 33.")
                                                                                                                                                    /\ LET result47 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result47)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result47)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value639 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value639), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd140 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd140
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ IF ((value513).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog17 EXCEPT ![i] = SubSeq((plog17)[i], 1, (Len((plog17)[i])) - ((value513).cnt))]
                                                                                                                                                               /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 2511, column 35.")
                                                                                                                                                               /\ LET result48 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result48)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result48)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value640 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value640), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd141 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd141
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 2532, column 35.")
                                                                                                                                                               /\ LET result49 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result49)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result49)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value641 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value641), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ plog' = plog17
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd142 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd142
                                                                                                                                                                               /\ plog' = plog17
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                              ELSE /\ LET log22 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                        LET value514 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                          IF ((value514).cmd) = (LogConcat)
                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value514).entries)]
                                                                                                                                                  /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                  /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                            "Failure of assertion at line 2564, column 33.")
                                                                                                                                                  /\ LET result50 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result50)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result50)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value642 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value642), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd143 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd143
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ IF ((value514).cmd) = (LogPop)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value514).cnt))]
                                                                                                                                                             /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 2587, column 35.")
                                                                                                                                                             /\ LET result51 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result51)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result51)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value643 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value643), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd144 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd144
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 2608, column 35.")
                                                                                                                                                             /\ LET result52 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result52)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result52)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value644 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value644), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd145 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd145
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                             /\ plog' = plog
                                                                                         ELSE /\ IF (((m0[self]).mterm) < ((currentTerm)[i])) \/ (((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                    THEN /\ \/ /\ LET value35 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value35), enabled |-> ((network)[j]).enabled]]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                            \/ /\ LET yielded_fd05 == (fd)[j] IN
                                                                                                                    /\ yielded_fd05
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               /\ UNCHANGED network
                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                         log, 
                                                                                                                         plog, 
                                                                                                                         sm, 
                                                                                                                         smDomain >>
                                                                                                    ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                                   "Failure of assertion at line 2650, column 23.")
                                                                                                         /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                              LET value45 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                IF ((value45).cmd) = (LogConcat)
                                                                                                                   THEN /\ LET plog18 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value45).entries)] IN
                                                                                                                             LET log23 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                               LET value515 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                 IF ((value515).cmd) = (LogConcat)
                                                                                                                                    THEN /\ plog' = [plog18 EXCEPT ![i] = ((plog18)[i]) \o ((value515).entries)]
                                                                                                                                         /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0[self]).mentries)]
                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                   "Failure of assertion at line 2664, column 31.")
                                                                                                                                         /\ LET result53 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result53)[1]]
                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result53)[2]]
                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                              /\ \/ /\ LET value645 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value645), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 \/ /\ LET yielded_fd146 == (fd)[j] IN
                                                                                                                                                         /\ yielded_fd146
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                    ELSE /\ IF ((value515).cmd) = (LogPop)
                                                                                                                                               THEN /\ plog' = [plog18 EXCEPT ![i] = SubSeq((plog18)[i], 1, (Len((plog18)[i])) - ((value515).cnt))]
                                                                                                                                                    /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2687, column 33.")
                                                                                                                                                    /\ LET result54 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result54)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result54)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value646 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value646), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd147 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd147
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2708, column 33.")
                                                                                                                                                    /\ LET result55 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result55)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result55)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value647 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value647), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ plog' = plog18
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd148 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd148
                                                                                                                                                                    /\ plog' = plog18
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                   ELSE /\ IF ((value45).cmd) = (LogPop)
                                                                                                                              THEN /\ LET plog19 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value45).cnt))] IN
                                                                                                                                        LET log24 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                          LET value516 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                            IF ((value516).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog19 EXCEPT ![i] = ((plog19)[i]) \o ((value516).entries)]
                                                                                                                                                    /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2742, column 33.")
                                                                                                                                                    /\ LET result56 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result56)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result56)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value648 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value648), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd149 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd149
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ IF ((value516).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog19 EXCEPT ![i] = SubSeq((plog19)[i], 1, (Len((plog19)[i])) - ((value516).cnt))]
                                                                                                                                                               /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 2765, column 35.")
                                                                                                                                                               /\ LET result57 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result57)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result57)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value649 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value649), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd150 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd150
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 2786, column 35.")
                                                                                                                                                               /\ LET result58 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result58)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result58)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value650 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value650), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ plog' = plog19
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd151 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd151
                                                                                                                                                                               /\ plog' = plog19
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                              ELSE /\ LET log25 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                        LET value517 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                          IF ((value517).cmd) = (LogConcat)
                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value517).entries)]
                                                                                                                                                  /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                  /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                            "Failure of assertion at line 2818, column 33.")
                                                                                                                                                  /\ LET result59 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result59)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result59)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value651 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value651), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd152 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd152
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ IF ((value517).cmd) = (LogPop)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value517).cnt))]
                                                                                                                                                             /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 2841, column 35.")
                                                                                                                                                             /\ LET result60 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result60)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result60)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value652 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value652), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd153 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd153
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 2862, column 35.")
                                                                                                                                                             /\ LET result61 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result61)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result61)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value653 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value653), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd154 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd154
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                             /\ plog' = plog
                                                                                              /\ state' = state
                                                                              ELSE /\ IF (((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                                         THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                              /\ IF (((m0[self]).mterm) < ((currentTerm)[i])) \/ (((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                    THEN /\ \/ /\ LET value36 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value36), enabled |-> ((network)[j]).enabled]]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                            \/ /\ LET yielded_fd06 == (fd)[j] IN
                                                                                                                    /\ yielded_fd06
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               /\ UNCHANGED network
                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                         log, 
                                                                                                                         plog, 
                                                                                                                         sm, 
                                                                                                                         smDomain >>
                                                                                                    ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                   "Failure of assertion at line 2907, column 23.")
                                                                                                         /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                              LET value46 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                IF ((value46).cmd) = (LogConcat)
                                                                                                                   THEN /\ LET plog20 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value46).entries)] IN
                                                                                                                             LET log26 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                               LET value518 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                 IF ((value518).cmd) = (LogConcat)
                                                                                                                                    THEN /\ plog' = [plog20 EXCEPT ![i] = ((plog20)[i]) \o ((value518).entries)]
                                                                                                                                         /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0[self]).mentries)]
                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                   "Failure of assertion at line 2921, column 31.")
                                                                                                                                         /\ LET result62 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result62)[1]]
                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result62)[2]]
                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                              /\ \/ /\ LET value654 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value654), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 \/ /\ LET yielded_fd155 == (fd)[j] IN
                                                                                                                                                         /\ yielded_fd155
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                    ELSE /\ IF ((value518).cmd) = (LogPop)
                                                                                                                                               THEN /\ plog' = [plog20 EXCEPT ![i] = SubSeq((plog20)[i], 1, (Len((plog20)[i])) - ((value518).cnt))]
                                                                                                                                                    /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2944, column 33.")
                                                                                                                                                    /\ LET result63 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result63)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result63)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value655 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value655), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd156 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd156
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2965, column 33.")
                                                                                                                                                    /\ LET result64 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result64)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result64)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value656 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value656), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ plog' = plog20
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd157 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd157
                                                                                                                                                                    /\ plog' = plog20
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                   ELSE /\ IF ((value46).cmd) = (LogPop)
                                                                                                                              THEN /\ LET plog21 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value46).cnt))] IN
                                                                                                                                        LET log27 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                          LET value519 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                            IF ((value519).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog21 EXCEPT ![i] = ((plog21)[i]) \o ((value519).entries)]
                                                                                                                                                    /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 2999, column 33.")
                                                                                                                                                    /\ LET result65 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result65)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result65)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value657 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value657), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd158 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd158
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ IF ((value519).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog21 EXCEPT ![i] = SubSeq((plog21)[i], 1, (Len((plog21)[i])) - ((value519).cnt))]
                                                                                                                                                               /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 3022, column 35.")
                                                                                                                                                               /\ LET result66 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result66)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result66)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value658 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value658), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd159 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd159
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 3043, column 35.")
                                                                                                                                                               /\ LET result67 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result67)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result67)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value659 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value659), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ plog' = plog21
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd160 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd160
                                                                                                                                                                               /\ plog' = plog21
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                              ELSE /\ LET log28 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                        LET value520 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                          IF ((value520).cmd) = (LogConcat)
                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value520).entries)]
                                                                                                                                                  /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                  /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                            "Failure of assertion at line 3075, column 33.")
                                                                                                                                                  /\ LET result68 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result68)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result68)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value660 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value660), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd161 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd161
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ IF ((value520).cmd) = (LogPop)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value520).cnt))]
                                                                                                                                                             /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 3098, column 35.")
                                                                                                                                                             /\ LET result69 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result69)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result69)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value661 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value661), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd162 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd162
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 3119, column 35.")
                                                                                                                                                             /\ LET result70 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result70)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result70)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value662 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value662), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd163 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd163
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                             /\ plog' = plog
                                                                                         ELSE /\ IF (((m0[self]).mterm) < ((currentTerm)[i])) \/ (((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                    THEN /\ \/ /\ LET value37 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value37), enabled |-> ((network)[j]).enabled]]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                            \/ /\ LET yielded_fd07 == (fd)[j] IN
                                                                                                                    /\ yielded_fd07
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               /\ UNCHANGED network
                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                         log, 
                                                                                                                         plog, 
                                                                                                                         sm, 
                                                                                                                         smDomain >>
                                                                                                    ELSE /\ Assert(((((m0[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                                   "Failure of assertion at line 3161, column 23.")
                                                                                                         /\ LET index == ((m0[self]).mprevLogIndex) + (1) IN
                                                                                                              LET value47 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m0[self]).mprevLogIndex)] IN
                                                                                                                IF ((value47).cmd) = (LogConcat)
                                                                                                                   THEN /\ LET plog22 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value47).entries)] IN
                                                                                                                             LET log29 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                               LET value521 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                 IF ((value521).cmd) = (LogConcat)
                                                                                                                                    THEN /\ plog' = [plog22 EXCEPT ![i] = ((plog22)[i]) \o ((value521).entries)]
                                                                                                                                         /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0[self]).mentries)]
                                                                                                                                         /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                   "Failure of assertion at line 3175, column 31.")
                                                                                                                                         /\ LET result71 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result71)[1]]
                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result71)[2]]
                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                              /\ \/ /\ LET value663 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value663), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 \/ /\ LET yielded_fd164 == (fd)[j] IN
                                                                                                                                                         /\ yielded_fd164
                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                    ELSE /\ IF ((value521).cmd) = (LogPop)
                                                                                                                                               THEN /\ plog' = [plog22 EXCEPT ![i] = SubSeq((plog22)[i], 1, (Len((plog22)[i])) - ((value521).cnt))]
                                                                                                                                                    /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 3198, column 33.")
                                                                                                                                                    /\ LET result72 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result72)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result72)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value664 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value664), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd165 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd165
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 3219, column 33.")
                                                                                                                                                    /\ LET result73 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result73)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result73)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value665 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value665), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ plog' = plog22
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd166 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd166
                                                                                                                                                                    /\ plog' = plog22
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                   ELSE /\ IF ((value47).cmd) = (LogPop)
                                                                                                                              THEN /\ LET plog23 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value47).cnt))] IN
                                                                                                                                        LET log30 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                          LET value522 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                            IF ((value522).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog23 EXCEPT ![i] = ((plog23)[i]) \o ((value522).entries)]
                                                                                                                                                    /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                    /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                              "Failure of assertion at line 3253, column 33.")
                                                                                                                                                    /\ LET result74 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result74)[1]]
                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result74)[2]]
                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                         /\ \/ /\ LET value666 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value666), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            \/ /\ LET yielded_fd167 == (fd)[j] IN
                                                                                                                                                                    /\ yielded_fd167
                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                               ELSE /\ IF ((value522).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog23 EXCEPT ![i] = SubSeq((plog23)[i], 1, (Len((plog23)[i])) - ((value522).cnt))]
                                                                                                                                                               /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 3276, column 35.")
                                                                                                                                                               /\ LET result75 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result75)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result75)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value667 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value667), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd168 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd168
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                               /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                         "Failure of assertion at line 3297, column 35.")
                                                                                                                                                               /\ LET result76 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result76)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result76)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value668 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value668), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ plog' = plog23
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd169 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd169
                                                                                                                                                                               /\ plog' = plog23
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                              ELSE /\ LET log31 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m0[self]).mprevLogIndex)] IN
                                                                                                                                        LET value523 == [cmd |-> LogConcat, entries |-> (m0[self]).mentries] IN
                                                                                                                                          IF ((value523).cmd) = (LogConcat)
                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value523).entries)]
                                                                                                                                                  /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                  /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                            "Failure of assertion at line 3329, column 33.")
                                                                                                                                                  /\ LET result77 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result77)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result77)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value669 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value669), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd170 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd170
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ IF ((value523).cmd) = (LogPop)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value523).cnt))]
                                                                                                                                                             /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 3352, column 35.")
                                                                                                                                                             /\ LET result78 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result78)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result78)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value670 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value670), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd171 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd171
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m0[self]).mentries)]
                                                                                                                                                             /\ Assert(((m0[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                       "Failure of assertion at line 3373, column 35.")
                                                                                                                                                             /\ LET result79 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m0[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result79)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result79)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m0[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value671 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m0[self]).mprevLogIndex) + (Len((m0[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value671), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd172 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd172
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                             /\ plog' = plog
                                                                                              /\ state' = state
                                                                                   /\ UNCHANGED << leader, 
                                                                                                   leaderTimeout >>
                                                               /\ UNCHANGED << currentTerm, 
                                                                               votedFor >>
                                                    /\ UNCHANGED << nextIndex, 
                                                                    matchIndex >>
                                               ELSE /\ IF ((m0[self]).mtype) = (AppendEntriesResponse)
                                                          THEN /\ IF ((m0[self]).mterm) > ((currentTerm)[srvId0[self]])
                                                                     THEN /\ currentTerm' = [currentTerm EXCEPT ![srvId0[self]] = (m0[self]).mterm]
                                                                          /\ state' = [state EXCEPT ![srvId0[self]] = Follower]
                                                                          /\ votedFor' = [votedFor EXCEPT ![srvId0[self]] = Nil]
                                                                          /\ leader' = [leader EXCEPT ![srvId0[self]] = Nil]
                                                                          /\ IF ((m0[self]).mterm) < ((currentTerm')[srvId0[self]])
                                                                                THEN /\ TRUE
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == srvId0[self] IN
                                                                                          LET j == (m0[self]).msource IN
                                                                                            /\ Assert(((m0[self]).mterm) = ((currentTerm')[i]), 
                                                                                                      "Failure of assertion at line 3418, column 21.")
                                                                                            /\ IF (m0[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m0[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m0[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                     ELSE /\ IF ((m0[self]).mterm) < ((currentTerm)[srvId0[self]])
                                                                                THEN /\ TRUE
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == srvId0[self] IN
                                                                                          LET j == (m0[self]).msource IN
                                                                                            /\ Assert(((m0[self]).mterm) = ((currentTerm)[i]), 
                                                                                                      "Failure of assertion at line 3438, column 21.")
                                                                                            /\ IF (m0[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m0[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m0[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                          /\ UNCHANGED << state, 
                                                                                          currentTerm, 
                                                                                          votedFor, 
                                                                                          leader >>
                                                               /\ UNCHANGED << network, 
                                                                               log, 
                                                                               plog >>
                                                          ELSE /\ IF (((m0[self]).mtype) = (ClientPutRequest)) \/ (((m0[self]).mtype) = (ClientGetRequest))
                                                                     THEN /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleClientRequest", srvId0[self], (m0[self]).msource, (currentTerm)[srvId0[self]], (state)[srvId0[self]]>>)
                                                                                     /\ IF ((state)[srvId0[self]]) = (Leader)
                                                                                           THEN /\ LET entry == [term |-> (currentTerm)[srvId0[self]], cmd |-> (m0[self]).mcmd, client |-> (m0[self]).msource] IN
                                                                                                     /\ log' = [log EXCEPT ![srvId0[self]] = Append((log)[srvId0[self]], entry)]
                                                                                                     /\ LET value70 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                          IF ((value70).cmd) = (LogConcat)
                                                                                                             THEN /\ plog' = [plog EXCEPT ![srvId0[self]] = ((plog)[srvId0[self]]) \o ((value70).entries)]
                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                             ELSE /\ IF ((value70).cmd) = (LogPop)
                                                                                                                        THEN /\ plog' = [plog EXCEPT ![srvId0[self]] = SubSeq((plog)[srvId0[self]], 1, (Len((plog)[srvId0[self]])) - ((value70).cnt))]
                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                             /\ plog' = plog
                                                                                                /\ UNCHANGED network
                                                                                           ELSE /\ LET i == srvId0[self] IN
                                                                                                     LET j == (m0[self]).msource IN
                                                                                                       LET respType == IF (((m0[self]).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                                         LET value80 == [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m0[self]).mcmd).idx, key |-> ((m0[self]).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j] IN
                                                                                                           /\ ((network)[j]).enabled
                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value80), enabled |-> ((network)[j]).enabled]]
                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                /\ UNCHANGED << log, 
                                                                                                                plog >>
                                                                                ELSE /\ IF ((state)[srvId0[self]]) = (Leader)
                                                                                           THEN /\ LET entry == [term |-> (currentTerm)[srvId0[self]], cmd |-> (m0[self]).mcmd, client |-> (m0[self]).msource] IN
                                                                                                     /\ log' = [log EXCEPT ![srvId0[self]] = Append((log)[srvId0[self]], entry)]
                                                                                                     /\ LET value71 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                          IF ((value71).cmd) = (LogConcat)
                                                                                                             THEN /\ plog' = [plog EXCEPT ![srvId0[self]] = ((plog)[srvId0[self]]) \o ((value71).entries)]
                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                             ELSE /\ IF ((value71).cmd) = (LogPop)
                                                                                                                        THEN /\ plog' = [plog EXCEPT ![srvId0[self]] = SubSeq((plog)[srvId0[self]], 1, (Len((plog)[srvId0[self]])) - ((value71).cnt))]
                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                             /\ plog' = plog
                                                                                                /\ UNCHANGED network
                                                                                           ELSE /\ LET i == srvId0[self] IN
                                                                                                     LET j == (m0[self]).msource IN
                                                                                                       LET respType == IF (((m0[self]).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                                         LET value81 == [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m0[self]).mcmd).idx, key |-> ((m0[self]).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j] IN
                                                                                                           /\ ((network)[j]).enabled
                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value81), enabled |-> ((network)[j]).enabled]]
                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                /\ UNCHANGED << log, 
                                                                                                                plog >>
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED << network, 
                                                                                          log, 
                                                                                          plog >>
                                                               /\ UNCHANGED << state, 
                                                                               currentTerm, 
                                                                               nextIndex, 
                                                                               matchIndex, 
                                                                               votedFor, 
                                                                               leader >>
                                                    /\ UNCHANGED << commitIndex, 
                                                                    sm, 
                                                                    smDomain, 
                                                                    leaderTimeout >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted, 
                                                         becomeLeaderCh >>
                   /\ UNCHANGED << fd, appendEntriesCh, handlerCh, allReqs, 
                                   reqCh, respCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, handlerSrvId, 
                                   crasherSrvId, m, srvId, idx, m0, srvId0, 
                                   idx0, srvId1, idx1, srvId2, newCommitIndex, 
                                   srvId3, srvId4, leader0, req, resp, reqIdx, 
                                   timeout, srvId5 >>

s01(self) == serverLoop(self) \/ handleMsg(self)

serverRequestVoteLoop(self) == /\ pc[self] = "serverRequestVoteLoop"
                               /\ IF TRUE
                                     THEN /\ leaderTimeout
                                          /\ LET yielded_network00 == Len(((network)[srvId1[self]]).queue) IN
                                               /\ (yielded_network00) = (0)
                                               /\ ((state)[srvId1[self]]) \in ({Follower, Candidate})
                                               /\ LET i1 == srvId1[self] IN
                                                    /\ state' = [state EXCEPT ![i1] = Candidate]
                                                    /\ currentTerm' = [currentTerm EXCEPT ![i1] = ((currentTerm)[i1]) + (1)]
                                                    /\ votedFor' = [votedFor EXCEPT ![i1] = i1]
                                                    /\ votesResponded' = [votesResponded EXCEPT ![i1] = {i1}]
                                                    /\ votesGranted' = [votesGranted EXCEPT ![i1] = {i1}]
                                                    /\ leader' = [leader EXCEPT ![i1] = Nil]
                                                    /\ IF Debug
                                                          THEN /\ PrintT(<<"ServerTimeout", i1, (currentTerm')[i1]>>)
                                                               /\ idx0' = [idx0 EXCEPT ![self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                          ELSE /\ idx0' = [idx0 EXCEPT ![self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                          /\ UNCHANGED << state, currentTerm, 
                                                          votedFor, 
                                                          votesResponded, 
                                                          votesGranted, leader, 
                                                          idx0 >>
                               /\ UNCHANGED << network, fd, commitIndex, 
                                               nextIndex, matchIndex, log, 
                                               plog, sm, smDomain, 
                                               leaderTimeout, appendEntriesCh, 
                                               becomeLeaderCh, handlerCh, 
                                               allReqs, reqCh, respCh, 
                                               requestVoteSrvId, 
                                               appendEntriesSrvId, 
                                               advanceCommitIndexSrvId, 
                                               becomeLeaderSrvId, handlerSrvId, 
                                               crasherSrvId, m, srvId, idx, m0, 
                                               srvId0, srvId1, idx1, srvId2, 
                                               newCommitIndex, srvId3, srvId4, 
                                               leader0, req, resp, reqIdx, 
                                               timeout, srvId5 >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx0[self]) <= (NumServers)
                               THEN /\ IF (idx0[self]) # (srvId1[self])
                                          THEN /\ \/ /\ LET value90 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId1[self]], mlastLogTerm |-> LastTerm((log)[srvId1[self]]), mlastLogIndex |-> Len((log)[srvId1[self]]), msource |-> srvId1[self], mdest |-> idx0[self]] IN
                                                          /\ ((network)[idx0[self]]).enabled
                                                          /\ (Len(((network)[idx0[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![idx0[self]] = [queue |-> Append(((network)[idx0[self]]).queue, value90), enabled |-> ((network)[idx0[self]]).enabled]]
                                                          /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                  \/ /\ LET yielded_fd20 == (fd)[idx0[self]] IN
                                                          /\ yielded_fd20
                                                          /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                     /\ UNCHANGED network
                                          ELSE /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                               /\ UNCHANGED network
                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverRequestVoteLoop"]
                                    /\ UNCHANGED << network, idx0 >>
                         /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                         nextIndex, matchIndex, log, plog, 
                                         votedFor, votesResponded, 
                                         votesGranted, leader, sm, smDomain, 
                                         leaderTimeout, appendEntriesCh, 
                                         becomeLeaderCh, handlerCh, allReqs, 
                                         reqCh, respCh, requestVoteSrvId, 
                                         appendEntriesSrvId, 
                                         advanceCommitIndexSrvId, 
                                         becomeLeaderSrvId, handlerSrvId, 
                                         crasherSrvId, m, srvId, idx, m0, 
                                         srvId0, srvId1, idx1, srvId2, 
                                         newCommitIndex, srvId3, srvId4, 
                                         leader0, req, resp, reqIdx, timeout, 
                                         srvId5 >>

s1(self) == serverRequestVoteLoop(self) \/ requestVoteLoop(self)

serverAppendEntriesLoop(self) == /\ pc[self] = "serverAppendEntriesLoop"
                                 /\ IF appendEntriesCh
                                       THEN /\ ((state)[srvId2[self]]) = (Leader)
                                            /\ idx1' = [idx1 EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                            /\ idx1' = idx1
                                 /\ UNCHANGED << network, fd, state, 
                                                 currentTerm, commitIndex, 
                                                 nextIndex, matchIndex, log, 
                                                 plog, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, sm, smDomain, 
                                                 leaderTimeout, 
                                                 appendEntriesCh, 
                                                 becomeLeaderCh, handlerCh, 
                                                 allReqs, reqCh, respCh, 
                                                 requestVoteSrvId, 
                                                 appendEntriesSrvId, 
                                                 advanceCommitIndexSrvId, 
                                                 becomeLeaderSrvId, 
                                                 handlerSrvId, crasherSrvId, m, 
                                                 srvId, idx, m0, srvId0, idx0, 
                                                 srvId1, srvId2, 
                                                 newCommitIndex, srvId3, 
                                                 srvId4, leader0, req, resp, 
                                                 reqIdx, timeout, srvId5 >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ IF (((state)[srvId2[self]]) = (Leader)) /\ ((idx1[self]) <= (NumServers))
                                 THEN /\ IF (idx1[self]) # (srvId2[self])
                                            THEN /\ LET prevLogIndex1 == (((nextIndex)[srvId2[self]])[idx1[self]]) - (1) IN
                                                      LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN (((log)[srvId2[self]])[prevLogIndex1]).term ELSE 0 IN
                                                        LET entries1 == SubSeq((log)[srvId2[self]], ((nextIndex)[srvId2[self]])[idx1[self]], Len((log)[srvId2[self]])) IN
                                                          \/ /\ LET value100 == [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId2[self]], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> (commitIndex)[srvId2[self]], msource |-> srvId2[self], mdest |-> idx1[self]] IN
                                                                  /\ ((network)[idx1[self]]).enabled
                                                                  /\ (Len(((network)[idx1[self]]).queue)) < (BufferSize)
                                                                  /\ network' = [network EXCEPT ![idx1[self]] = [queue |-> Append(((network)[idx1[self]]).queue, value100), enabled |-> ((network)[idx1[self]]).enabled]]
                                                                  /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                                                  /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                          \/ /\ LET yielded_fd30 == (fd)[idx1[self]] IN
                                                                  /\ yielded_fd30
                                                                  /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                                                  /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                             /\ UNCHANGED network
                                            ELSE /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                                 /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                 /\ UNCHANGED network
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverAppendEntriesLoop"]
                                      /\ UNCHANGED << network, idx1 >>
                           /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                           nextIndex, matchIndex, log, plog, 
                                           votedFor, votesResponded, 
                                           votesGranted, leader, sm, smDomain, 
                                           leaderTimeout, appendEntriesCh, 
                                           becomeLeaderCh, handlerCh, allReqs, 
                                           reqCh, respCh, requestVoteSrvId, 
                                           appendEntriesSrvId, 
                                           advanceCommitIndexSrvId, 
                                           becomeLeaderSrvId, handlerSrvId, 
                                           crasherSrvId, m, srvId, idx, m0, 
                                           srvId0, idx0, srvId1, srvId2, 
                                           newCommitIndex, srvId3, srvId4, 
                                           leader0, req, resp, reqIdx, timeout, 
                                           srvId5 >>

s2(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)

serverAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverAdvanceCommitIndexLoop"
                                      /\ IF TRUE
                                            THEN /\ ((state)[srvId3[self]]) = (Leader)
                                                 /\ LET i == srvId3[self] IN
                                                      LET maxAgreeIndex == FindMaxAgreeIndex((log)[i], i, (matchIndex)[i]) IN
                                                        LET nCommitIndex == IF ((maxAgreeIndex) # (Nil)) /\ (((((log)[i])[maxAgreeIndex]).term) = ((currentTerm)[i])) THEN maxAgreeIndex ELSE (commitIndex)[i] IN
                                                          /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                                          /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                                    "Failure of assertion at line 3637, column 11.")
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                 /\ UNCHANGED newCommitIndex
                                      /\ UNCHANGED << network, fd, state, 
                                                      currentTerm, commitIndex, 
                                                      nextIndex, matchIndex, 
                                                      log, plog, votedFor, 
                                                      votesResponded, 
                                                      votesGranted, leader, sm, 
                                                      smDomain, leaderTimeout, 
                                                      appendEntriesCh, 
                                                      becomeLeaderCh, 
                                                      handlerCh, allReqs, 
                                                      reqCh, respCh, 
                                                      requestVoteSrvId, 
                                                      appendEntriesSrvId, 
                                                      advanceCommitIndexSrvId, 
                                                      becomeLeaderSrvId, 
                                                      handlerSrvId, 
                                                      crasherSrvId, m, srvId, 
                                                      idx, m0, srvId0, idx0, 
                                                      srvId1, idx1, srvId2, 
                                                      srvId3, srvId4, leader0, 
                                                      req, resp, reqIdx, 
                                                      timeout, srvId5 >>

applyLoop(self) == /\ pc[self] = "applyLoop"
                   /\ IF ((commitIndex)[srvId3[self]]) < (newCommitIndex[self])
                         THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId3[self]] = ((commitIndex)[srvId3[self]]) + (1)]
                              /\ LET i == srvId3[self] IN
                                   LET k == (commitIndex')[i] IN
                                     LET entry == ((log)[i])[k] IN
                                       LET cmd == (entry).cmd IN
                                         LET respType == IF ((cmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                           IF ((cmd).type) = (Put)
                                              THEN /\ sm' = [sm EXCEPT ![i] = ((sm)[i]) @@ (((cmd).key) :> ((cmd).value))]
                                                   /\ smDomain' = [smDomain EXCEPT ![i] = ((smDomain)[i]) \union ({(cmd).key})]
                                                   /\ LET reqOk == ((cmd).key) \in ((smDomain')[i]) IN
                                                        LET value110 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm')[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value110), enabled |-> ((network)[(entry).client]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                              ELSE /\ LET reqOk == ((cmd).key) \in ((smDomain)[i]) IN
                                                        LET value111 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value111), enabled |-> ((network)[(entry).client]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                                   /\ UNCHANGED << sm, 
                                                                   smDomain >>
                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverAdvanceCommitIndexLoop"]
                              /\ UNCHANGED << network, commitIndex, sm, 
                                              smDomain >>
                   /\ UNCHANGED << fd, state, currentTerm, nextIndex, 
                                   matchIndex, log, plog, votedFor, 
                                   votesResponded, votesGranted, leader, 
                                   leaderTimeout, appendEntriesCh, 
                                   becomeLeaderCh, handlerCh, allReqs, reqCh, 
                                   respCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, handlerSrvId, 
                                   crasherSrvId, m, srvId, idx, m0, srvId0, 
                                   idx0, srvId1, idx1, srvId2, newCommitIndex, 
                                   srvId3, srvId4, leader0, req, resp, reqIdx, 
                                   timeout, srvId5 >>

s3(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)

serverBecomeLeaderLoop(self) == /\ pc[self] = "serverBecomeLeaderLoop"
                                /\ (Len((becomeLeaderCh)[srvId4[self]])) > (0)
                                /\ LET res1 == Head((becomeLeaderCh)[srvId4[self]]) IN
                                     /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![srvId4[self]] = Tail((becomeLeaderCh)[srvId4[self]])]
                                     /\ LET yielded_becomeLeaderCh == res1 IN
                                          IF yielded_becomeLeaderCh
                                             THEN /\ ((state)[srvId4[self]]) = (Candidate)
                                                  /\ isQuorum((votesGranted)[srvId4[self]])
                                                  /\ LET i == srvId4[self] IN
                                                       /\ state' = [state EXCEPT ![i] = Leader]
                                                       /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]]
                                                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
                                                       /\ leader' = [leader EXCEPT ![i] = i]
                                                       /\ appendEntriesCh' = TRUE
                                                       /\ IF Debug
                                                             THEN /\ PrintT(<<"BecomeLeader", i, (currentTerm)[i], (state')[i], (leader')[i]>>)
                                                                  /\ pc' = [pc EXCEPT ![self] = "serverBecomeLeaderLoop"]
                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverBecomeLeaderLoop"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  /\ UNCHANGED << state, 
                                                                  nextIndex, 
                                                                  matchIndex, 
                                                                  leader, 
                                                                  appendEntriesCh >>
                                /\ UNCHANGED << network, fd, currentTerm, 
                                                commitIndex, log, plog, 
                                                votedFor, votesResponded, 
                                                votesGranted, sm, smDomain, 
                                                leaderTimeout, handlerCh, 
                                                allReqs, reqCh, respCh, 
                                                requestVoteSrvId, 
                                                appendEntriesSrvId, 
                                                advanceCommitIndexSrvId, 
                                                becomeLeaderSrvId, 
                                                handlerSrvId, crasherSrvId, m, 
                                                srvId, idx, m0, srvId0, idx0, 
                                                srvId1, idx1, srvId2, 
                                                newCommitIndex, srvId3, srvId4, 
                                                leader0, req, resp, reqIdx, 
                                                timeout, srvId5 >>

s4(self) == serverBecomeLeaderLoop(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ (Len(reqCh)) > (0)
                               /\ LET res20 == Head(reqCh) IN
                                    /\ reqCh' = Tail(reqCh)
                                    /\ LET yielded_reqCh0 == res20 IN
                                         /\ req' = [req EXCEPT ![self] = yielded_reqCh0]
                                         /\ reqIdx' = [reqIdx EXCEPT ![self] = (reqIdx[self]) + (1)]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << reqCh, req, reqIdx >>
                    /\ UNCHANGED << network, fd, state, currentTerm, 
                                    commitIndex, nextIndex, matchIndex, log, 
                                    plog, votedFor, votesResponded, 
                                    votesGranted, leader, sm, smDomain, 
                                    leaderTimeout, appendEntriesCh, 
                                    becomeLeaderCh, handlerCh, allReqs, respCh, 
                                    requestVoteSrvId, appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    handlerSrvId, crasherSrvId, m, srvId, idx, 
                                    m0, srvId0, idx0, srvId1, idx1, srvId2, 
                                    newCommitIndex, srvId3, srvId4, leader0, 
                                    resp, timeout, srvId5 >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (leader0[self]) = (Nil)
                      THEN /\ \E srv1 \in ServerSet:
                                /\ leader0' = [leader0 EXCEPT ![self] = srv1]
                                /\ IF Debug
                                      THEN /\ PrintT(<<"ClientSndReq", self, leader0'[self], reqIdx[self], req[self]>>)
                                           /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value120 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value120), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd40 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd40
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value130 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value130), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                    \/ /\ LET yielded_fd50 == (fd)[leader0'[self]] IN
                                                                            /\ yielded_fd50
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                 /\ UNCHANGED network
                                      ELSE /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value121 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value121), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd41 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd41
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value131 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value131), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                    \/ /\ LET yielded_fd51 == (fd)[leader0'[self]] IN
                                                                            /\ yielded_fd51
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                 /\ UNCHANGED network
                      ELSE /\ IF Debug
                                 THEN /\ PrintT(<<"ClientSndReq", self, leader0[self], reqIdx[self], req[self]>>)
                                      /\ IF ((req[self]).type) = (Put)
                                            THEN /\ \/ /\ LET value122 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value122), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd42 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd42
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value132 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value132), enabled |-> ((network)[leader0[self]]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                               \/ /\ LET yielded_fd52 == (fd)[leader0[self]] IN
                                                                       /\ yielded_fd52
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED network
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                 ELSE /\ IF ((req[self]).type) = (Put)
                                            THEN /\ \/ /\ LET value123 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value123), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd43 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd43
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value133 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value133), enabled |-> ((network)[leader0[self]]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                               \/ /\ LET yielded_fd53 == (fd)[leader0[self]] IN
                                                                       /\ yielded_fd53
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED network
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                           /\ UNCHANGED leader0
                /\ UNCHANGED << fd, state, currentTerm, commitIndex, nextIndex, 
                                matchIndex, log, plog, votedFor, 
                                votesResponded, votesGranted, leader, sm, 
                                smDomain, leaderTimeout, appendEntriesCh, 
                                becomeLeaderCh, handlerCh, allReqs, reqCh, 
                                respCh, requestVoteSrvId, appendEntriesSrvId, 
                                advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                handlerSrvId, crasherSrvId, m, srvId, idx, m0, 
                                srvId0, idx0, srvId1, idx1, srvId2, 
                                newCommitIndex, srvId3, srvId4, req, resp, 
                                reqIdx, timeout, srvId5 >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 3879, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg10 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network10 == readMsg10 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network10]
                                 /\ IF Debug
                                       THEN /\ PrintT(<<"ClientRcvResp", self, leader0[self], reqIdx[self], resp'[self]>>)
                                            /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3887, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3892, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3896, column 19.")
                                                                  /\ respCh' = resp'[self]
                                                                  /\ IF Debug
                                                                        THEN /\ PrintT(<<"ClientRcvChDone", self, leader0'[self], reqIdx[self], resp'[self]>>)
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                       ELSE /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3907, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3912, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3916, column 19.")
                                                                  /\ respCh' = resp'[self]
                                                                  /\ IF Debug
                                                                        THEN /\ PrintT(<<"ClientRcvChDone", self, leader0'[self], reqIdx[self], resp'[self]>>)
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                    \/ /\ LET yielded_fd60 == (fd)[leader0[self]] IN
                            LET yielded_network20 == Len(((network)[self]).queue) IN
                              /\ ((yielded_fd60) /\ ((yielded_network20) = (0))) \/ (timeout[self])
                              /\ IF Debug
                                    THEN /\ PrintT(<<"ClientTimeout", self, leader0[self], reqIdx[self]>>)
                                         /\ leader0' = [leader0 EXCEPT ![self] = Nil]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                    ELSE /\ leader0' = [leader0 EXCEPT ![self] = Nil]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                       /\ UNCHANGED <<network, respCh, resp>>
                 /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                 nextIndex, matchIndex, log, plog, votedFor, 
                                 votesResponded, votesGranted, leader, sm, 
                                 smDomain, leaderTimeout, appendEntriesCh, 
                                 becomeLeaderCh, handlerCh, allReqs, reqCh, 
                                 requestVoteSrvId, appendEntriesSrvId, 
                                 advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                 handlerSrvId, crasherSrvId, m, srvId, idx, m0, 
                                 srvId0, idx0, srvId1, idx1, srvId2, 
                                 newCommitIndex, srvId3, srvId4, req, reqIdx, 
                                 timeout, srvId5 >>

client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

serverCrash(self) == /\ pc[self] = "serverCrash"
                     /\ LET value140 == FALSE IN
                          /\ network' = [network EXCEPT ![srvId5[self]] = [queue |-> ((network)[srvId5[self]]).queue, enabled |-> value140]]
                          /\ pc' = [pc EXCEPT ![self] = "fdUpdate"]
                     /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                     nextIndex, matchIndex, log, plog, 
                                     votedFor, votesResponded, votesGranted, 
                                     leader, sm, smDomain, leaderTimeout, 
                                     appendEntriesCh, becomeLeaderCh, 
                                     handlerCh, allReqs, reqCh, respCh, 
                                     requestVoteSrvId, appendEntriesSrvId, 
                                     advanceCommitIndexSrvId, 
                                     becomeLeaderSrvId, handlerSrvId, 
                                     crasherSrvId, m, srvId, idx, m0, srvId0, 
                                     idx0, srvId1, idx1, srvId2, 
                                     newCommitIndex, srvId3, srvId4, leader0, 
                                     req, resp, reqIdx, timeout, srvId5 >>

fdUpdate(self) == /\ pc[self] = "fdUpdate"
                  /\ LET value150 == TRUE IN
                       /\ fd' = [fd EXCEPT ![srvId5[self]] = value150]
                       /\ pc' = [pc EXCEPT ![self] = "block"]
                  /\ UNCHANGED << network, state, currentTerm, commitIndex, 
                                  nextIndex, matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, sm, 
                                  smDomain, leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, handlerCh, allReqs, reqCh, 
                                  respCh, requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  handlerSrvId, crasherSrvId, m, srvId, idx, 
                                  m0, srvId0, idx0, srvId1, idx1, srvId2, 
                                  newCommitIndex, srvId3, srvId4, leader0, req, 
                                  resp, reqIdx, timeout, srvId5 >>

block(self) == /\ pc[self] = "block"
               /\ FALSE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                               nextIndex, matchIndex, log, plog, votedFor, 
                               votesResponded, votesGranted, leader, sm, 
                               smDomain, leaderTimeout, appendEntriesCh, 
                               becomeLeaderCh, handlerCh, allReqs, reqCh, 
                               respCh, requestVoteSrvId, appendEntriesSrvId, 
                               advanceCommitIndexSrvId, becomeLeaderSrvId, 
                               handlerSrvId, crasherSrvId, m, srvId, idx, m0, 
                               srvId0, idx0, srvId1, idx1, srvId2, 
                               newCommitIndex, srvId3, srvId4, leader0, req, 
                               resp, reqIdx, timeout, srvId5 >>

crasher(self) == serverCrash(self) \/ fdUpdate(self) \/ block(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: s00(self))
           \/ (\E self \in ServerHandlerSet: s01(self))
           \/ (\E self \in ServerRequestVoteSet: s1(self))
           \/ (\E self \in ServerAppendEntriesSet: s2(self))
           \/ (\E self \in ServerAdvanceCommitIndexSet: s3(self))
           \/ (\E self \in ServerBecomeLeaderSet: s4(self))
           \/ (\E self \in ClientSet: client(self))
           \/ (\E self \in ServerCrasherSet: crasher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(s00(self))
        /\ \A self \in ServerHandlerSet : WF_vars(s01(self))
        /\ \A self \in ServerRequestVoteSet : WF_vars(s1(self))
        /\ \A self \in ServerAppendEntriesSet : WF_vars(s2(self))
        /\ \A self \in ServerAdvanceCommitIndexSet : WF_vars(s3(self))
        /\ \A self \in ServerBecomeLeaderSet : WF_vars(s4(self))
        /\ \A self \in ClientSet : WF_vars(client(self))
        /\ \A self \in ServerCrasherSet : WF_vars(crasher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION  TLA-f157040c4fee3bde8856de68970be59d

\* Constraints

LimitTerm == \A i \in ServerSet: currentTerm[i] < MaxTerm
LimitCommitIndex == \A i \in ServerSet: commitIndex[i] < MaxCommitIndex

LimitNodeFailure == Cardinality({i \in ServerSet: \lnot network[i].enabled}) < MaxNodeFail

MCConstraint ==
    /\ LimitTerm
    /\ LimitCommitIndex
    /\ LimitNodeFailure

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
                        /\ sm[i] = sm[j]
                        /\ smDomain[i] = smDomain[j]

plogOK == \A i \in ServerSet: log[i] = plog[i]

TermOK == \A i \in ServerSet: currentTerm[i] <= MaxTerm
CommitIndexOK == \A i \in ServerSet: commitIndex[i] <= MaxCommitIndex

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

ClientRcvResp(i) == pc[i] = "rcvResp" ~> pc[i] = "clientLoop"
ClientsOK == \A i \in ClientSet: ClientRcvResp(i)

\* Expected this to be violated if NumServers > 1,
\* but TLC doesn't report violation in case of NumServers = 2 because 
\* of using temporal properties and state constraints at the same time. 
\* TLC reports violation when NumServers = 3.
ElectionLiveness == []<>(\E i \in ServerSet: state[i] = Leader)

=============================================================================
