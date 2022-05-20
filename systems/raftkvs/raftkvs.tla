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

        ServerCrasherSet == IF ExploreFail 
                            THEN (5*NumServers+1)..(5*NumServers+MaxNodeFail)
                            ELSE {}

        ClientSet == (6*NumServers+1)..(6*NumServers+NumClients)

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
                yield SubSeq($variable, 1, Len($variable) - 1);
            };
        }
    }

    archetype AServer(
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
    variables
        idx = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            \* checkFail(self, netEnabled);

            m := net[self];
            assert m.mdest = self;

        handleMsg:
            \* checkFail(self, netEnabled);

            if (m.mtype = RequestVoteRequest) {
                UpdateTerm(self, m, currentTerm, state, votedFor, leader);

                \* HandleRequestVoteRequest
                with (
                    i = self, j = m.msource,
                    logOK = \/ m.mlastLogTerm > LastTerm(log[i])
                            \/ /\ m.mlastLogTerm = LastTerm(log[i])
                                /\ m.mlastLogIndex >= Len(log[i]),
                    grant = /\ m.mterm = currentTerm[i]
                            /\ logOK
                            /\ votedFor[self] \in {Nil, j}
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
                UpdateTerm(self, m, currentTerm, state, votedFor, leader);

                \* DropStaleResponse
                if (m.mterm < currentTerm[self]) {
                    \* goto serverLoop;
                    skip;
                } else {
                    \* HandleRequestVoteResponse
                    with (i = self, j = m.msource) {
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
                UpdateTerm(self, m, currentTerm, state, votedFor, leader);

                leader[self] := m.msource;
                leaderTimeout := LeaderTimeoutReset;

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
                };
            } else if (m.mtype = AppendEntriesResponse) {
                UpdateTerm(self, m, currentTerm, state, votedFor, leader);

                \* DropStaleResponse
                if (m.mterm < currentTerm[self]) {
                    \* goto serverLoop;
                    skip;
                } else {
                    \* HandleAppendEntriesResponse
                    with (i = self, j = m.msource) {
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

                debug(<<"HandleClientRequest", self, m.msource, currentTerm[self], state[self]>>);

                if (state[self] = Leader) {
                    with (entry = [term   |-> currentTerm[self],
                                    cmd    |-> m.mcmd,
                                    client |-> m.msource]
                    ) {
                        log[self]  := Append(log[self], entry);
                        plog[self] := [cmd |-> LogConcat, entries |-> <<entry>>];

                        \* commented out for perf optimization
                        \* appendEntriesCh := TRUE;
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
                        lastEntry    = Min({Len(log[srvId]), nextIndex[srvId][idx]}),
                        entries      = SubSeq(log[srvId], nextIndex[srvId][idx], lastEntry)
                    ) {
                        Send(net, idx, fd, [
                            mtype         |-> AppendEntriesRequest,
                            mterm         |-> currentTerm[srvId],
                            mprevLogIndex |-> prevLogIndex,
                            mprevLogTerm  |-> prevLogTerm,
                            mentries      |-> entries,
                            mcommitIndex  |-> Min({commitIndex[srvId], lastEntry}),
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
        crasherSrvId            = [i \in ServerCrasherSet            |-> i - 5*NumServers];

    fair process (s0 \in ServerSet) == instance AServer(
        s0,
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
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; state = [i \in ServerSet |-> Follower]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]; log = [i \in ServerSet |-> <<>>]; plog = [i \in ServerSet |-> <<>>]; votedFor = [i \in ServerSet |-> Nil]; votesResponded = [i \in ServerSet |-> {}]; votesGranted = [i \in ServerSet |-> {}]; leader = [i \in ServerSet |-> Nil]; sm = [i \in ServerSet |-> [k \in KeySet |-> Nil]]; smDomain = [i \in ServerSet |-> KeySet]; leaderTimeout = TRUE; appendEntriesCh = TRUE; becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]; allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>; reqCh = SubSeq(allReqs, 1, NumRequests); respCh; requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]; appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]; advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]; becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]; crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((5) * (NumServers))];
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
    ServerCrasherSet == IF ExploreFail THEN (((5) * (NumServers)) + (1)) .. (((5) * (NumServers)) + (MaxNodeFail)) ELSE {}
    ClientSet == (((6) * (NumServers)) + (1)) .. (((6) * (NumServers)) + (NumClients))
    NodeSet == (ServerSet) \union (ClientSet)
    KeySet == {}
  }
  
  fair process (s0 \in ServerSet)
    variables idx = 1; m; srvId = self;
  {
    serverLoop:
      if (TRUE) {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg00 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network3 = readMsg00) {
            m := yielded_network3;
            assert ((m).mdest) = (self);
            leaderTimeout := LeaderTimeoutReset;
            goto handleMsg;
          };
        };
      } else {
        goto Done;
      };
    handleMsg:
      if (((m).mtype) = (RequestVoteRequest)) {
        if (((m).mterm) > ((currentTerm)[self])) {
          currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
          state := [state EXCEPT ![self] = Follower];
          with (votedFor1 = [votedFor EXCEPT ![self] = Nil]) {
            leader := [leader EXCEPT ![self] = Nil];
            with (
              i = self, 
              j = (m).msource, 
              logOK = (((m).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m).mlastLogIndex) >= (Len((log)[i])))), 
              grant = ((((m).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor1)[self]) \in ({Nil, j}))
            ) {
              assert ((m).mterm) <= ((currentTerm)[i]);
              if (grant) {
                votedFor := [votedFor1 EXCEPT ![i] = j];
                either {
                  with (value00 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]];
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
                  with (value01 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value01), enabled |-> ((network)[j]).enabled]];
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
            i = self, 
            j = (m).msource, 
            logOK = (((m).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m).mlastLogIndex) >= (Len((log)[i])))), 
            grant = ((((m).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[self]) \in ({Nil, j}))
          ) {
            assert ((m).mterm) <= ((currentTerm)[i]);
            if (grant) {
              votedFor := [votedFor EXCEPT ![i] = j];
              either {
                with (value02 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]];
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
                with (value03 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value03), enabled |-> ((network)[j]).enabled]];
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
        if (((m).mtype) = (RequestVoteResponse)) {
          if (((m).mterm) > ((currentTerm)[self])) {
            currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
            state := [state EXCEPT ![self] = Follower];
            votedFor := [votedFor EXCEPT ![self] = Nil];
            leader := [leader EXCEPT ![self] = Nil];
            if (((m).mterm) < ((currentTerm)[self])) {
              skip;
              goto serverLoop;
            } else {
              with (
                i = self, 
                j = (m).msource
              ) {
                assert ((m).mterm) = ((currentTerm)[i]);
                votesResponded := [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})];
                if ((m).mvoteGranted) {
                  votesGranted := [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})];
                  if ((((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted)[i]))) {
                    with (value15 = TRUE) {
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value15)];
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
            if (((m).mterm) < ((currentTerm)[self])) {
              skip;
              goto serverLoop;
            } else {
              with (
                i = self, 
                j = (m).msource
              ) {
                assert ((m).mterm) = ((currentTerm)[i]);
                votesResponded := [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})];
                if ((m).mvoteGranted) {
                  votesGranted := [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})];
                  if ((((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted)[i]))) {
                    with (value16 = TRUE) {
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value16)];
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
          if (((m).mtype) = (AppendEntriesRequest)) {
            if (((m).mterm) > ((currentTerm)[self])) {
              currentTerm := [currentTerm EXCEPT ![self] = (m).mterm];
              with (state1 = [state EXCEPT ![self] = Follower]) {
                votedFor := [votedFor EXCEPT ![self] = Nil];
                with (leader1 = [leader EXCEPT ![self] = Nil]) {
                  leader := [leader1 EXCEPT ![self] = (m).msource];
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
                          with (yielded_fd00 = (fd)[j]) {
                            await yielded_fd00;
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
                                          with (result16 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result16)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result16)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value50 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]];
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
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value40).cmd) = (LogPop)) {
                                          plog := [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result17 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result17)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result17)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value51 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]];
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
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result18 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result18)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result18)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value52 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]];
                                                  plog := plog4;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd13 = (fd)[j]) {
                                                  await yielded_fd13;
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
                                      with (result19 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result19)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result19)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                          with (yielded_fd14 = (fd)[j]) {
                                            await yielded_fd14;
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
                                            with (result20 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result20)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result20)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value54 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]];
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
                                            goto serverLoop;
                                          };
                                        } else {
                                          if (((value41).cmd) = (LogPop)) {
                                            plog := [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result21 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result21)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result21)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value55 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]];
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd16 = (fd)[j]) {
                                                    await yielded_fd16;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              goto serverLoop;
                                            };
                                          } else {
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result22 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result22)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result22)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value56 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]];
                                                    plog := plog5;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd17 = (fd)[j]) {
                                                    await yielded_fd17;
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
                                        with (result23 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result23)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result23)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                            with (yielded_fd18 = (fd)[j]) {
                                              await yielded_fd18;
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
                                          with (result24 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result24)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result24)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value58 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd19 = (fd)[j]) {
                                                await yielded_fd19;
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
                                            with (result25 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result25)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result25)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value59 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd110 = (fd)[j]) {
                                                  await yielded_fd110;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result26 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result26)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result26)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value510 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd111 = (fd)[j]) {
                                                  await yielded_fd111;
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
                                      with (result27 = ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result27)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result27)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value511 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]];
                                            log := log4;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd112 = (fd)[j]) {
                                            await yielded_fd112;
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
                                    with (result28 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result28)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result28)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                      either {
                                        with (value512 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd113 = (fd)[j]) {
                                          await yielded_fd113;
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
                                      with (result29 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result29)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result29)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value513 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd114 = (fd)[j]) {
                                            await yielded_fd114;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result30 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result30)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result30)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value514 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd115 = (fd)[j]) {
                                            await yielded_fd115;
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
                                with (result31 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result31)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result31)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                  either {
                                    with (value515 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd116 = (fd)[j]) {
                                      await yielded_fd116;
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
                          with (yielded_fd01 = (fd)[j]) {
                            await yielded_fd01;
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
                                          with (result32 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result32)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result32)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value516 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]];
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
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value44).cmd) = (LogPop)) {
                                          plog := [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result33 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result33)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result33)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value517 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]];
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
                                          } else {
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result34 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result34)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result34)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                                with (yielded_fd119 = (fd)[j]) {
                                                  await yielded_fd119;
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
                                      with (result35 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result35)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result35)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                          with (yielded_fd120 = (fd)[j]) {
                                            await yielded_fd120;
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
                                            with (result36 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result36)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result36)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value520 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]];
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd121 = (fd)[j]) {
                                                  await yielded_fd121;
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
                                              with (result37 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result37)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result37)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value521 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]];
                                                    state := state1;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd122 = (fd)[j]) {
                                                    await yielded_fd122;
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
                                              with (result38 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result38)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result38)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                                  with (yielded_fd123 = (fd)[j]) {
                                                    await yielded_fd123;
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
                                        with (result39 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result39)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result39)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                            with (yielded_fd124 = (fd)[j]) {
                                              await yielded_fd124;
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
                                          with (result40 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result40)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result40)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value524 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd125 = (fd)[j]) {
                                                await yielded_fd125;
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
                                            with (result41 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result41)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result41)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value525 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]];
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd126 = (fd)[j]) {
                                                  await yielded_fd126;
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
                                            with (result42 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result42)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result42)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value526 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]];
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd127 = (fd)[j]) {
                                                  await yielded_fd127;
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
                                      with (result43 = ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result43)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result43)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                          with (yielded_fd128 = (fd)[j]) {
                                            await yielded_fd128;
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
                                    with (result44 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result44)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result44)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                      either {
                                        with (value528 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd129 = (fd)[j]) {
                                          await yielded_fd129;
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
                                      with (result45 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result45)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result45)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value529 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]];
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd130 = (fd)[j]) {
                                            await yielded_fd130;
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
                                      with (result46 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result46)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result46)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value530 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]];
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd131 = (fd)[j]) {
                                            await yielded_fd131;
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
                                with (result47 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result47)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result47)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                  either {
                                    with (value531 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]];
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd132 = (fd)[j]) {
                                      await yielded_fd132;
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
              };
            } else {
              leader := [leader EXCEPT ![self] = (m).msource];
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
                      with (yielded_fd02 = (fd)[j]) {
                        await yielded_fd02;
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
                                      with (result48 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result48)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result48)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value532 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd133 = (fd)[j]) {
                                            await yielded_fd133;
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
                                        with (result49 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result49)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result49)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value533 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd134 = (fd)[j]) {
                                              await yielded_fd134;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result50 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result50)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result50)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value534 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]];
                                              plog := plog8;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd135 = (fd)[j]) {
                                              await yielded_fd135;
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
                                  with (result51 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result51)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result51)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                      with (yielded_fd136 = (fd)[j]) {
                                        await yielded_fd136;
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
                                        with (result52 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result52)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result52)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value536 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value49).cmd) = (LogPop)) {
                                        plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result53 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result53)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result53)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value537 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]];
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
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result54 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result54)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result54)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value538 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]];
                                                plog := plog9;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd139 = (fd)[j]) {
                                                await yielded_fd139;
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
                                    with (result55 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result55)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result55)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                        with (yielded_fd140 = (fd)[j]) {
                                          await yielded_fd140;
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
                                      with (result56 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result56)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result56)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value540 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]];
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
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value410).cmd) = (LogPop)) {
                                      plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result57 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result57)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result57)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value541 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd142 = (fd)[j]) {
                                              await yielded_fd142;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result58 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result58)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result58)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value542 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result59 = ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result59)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result59)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value543 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]];
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd144 = (fd)[j]) {
                                        await yielded_fd144;
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
                                with (result60 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result60)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result60)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                  either {
                                    with (value544 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd145 = (fd)[j]) {
                                      await yielded_fd145;
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
                                  with (result61 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result61)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result61)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value545 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]];
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
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result62 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result62)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result62)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value546 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]];
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
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            with (result63 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                              sm := [sm EXCEPT ![i] = (result63)[1]];
                              smDomain := [smDomain EXCEPT ![i] = (result63)[2]];
                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                              either {
                                with (value547 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]];
                                  goto serverLoop;
                                };
                              } or {
                                with (yielded_fd148 = (fd)[j]) {
                                  await yielded_fd148;
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
                      with (yielded_fd03 = (fd)[j]) {
                        await yielded_fd03;
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
                                      with (result64 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result64)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result64)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value548 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]];
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
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value412).cmd) = (LogPop)) {
                                      plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result65 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result65)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result65)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value549 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result66 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result66)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result66)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value550 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]];
                                              plog := plog10;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd151 = (fd)[j]) {
                                              await yielded_fd151;
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
                                  with (result67 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result67)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result67)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                      with (yielded_fd152 = (fd)[j]) {
                                        await yielded_fd152;
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
                                        with (result68 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result68)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result68)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value552 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value413).cmd) = (LogPop)) {
                                        plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result69 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result69)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result69)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value553 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd154 = (fd)[j]) {
                                                await yielded_fd154;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result70 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result70)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result70)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value554 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]];
                                                plog := plog11;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd155 = (fd)[j]) {
                                                await yielded_fd155;
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
                                    with (result71 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result71)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result71)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
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
                                        with (yielded_fd156 = (fd)[j]) {
                                          await yielded_fd156;
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
                                      with (result72 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result72)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result72)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value556 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd157 = (fd)[j]) {
                                            await yielded_fd157;
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
                                        with (result73 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result73)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result73)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value557 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result74 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result74)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result74)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value558 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]];
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
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result75 = ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result75)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result75)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value559 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]];
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd160 = (fd)[j]) {
                                        await yielded_fd160;
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
                                with (result76 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                  sm := [sm EXCEPT ![i] = (result76)[1]];
                                  smDomain := [smDomain EXCEPT ![i] = (result76)[2]];
                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                  either {
                                    with (value560 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]];
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
                                goto serverLoop;
                              };
                            } else {
                              if (((value415).cmd) = (LogPop)) {
                                plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result77 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result77)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result77)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value561 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]];
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
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (result78 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                    sm := [sm EXCEPT ![i] = (result78)[1]];
                                    smDomain := [smDomain EXCEPT ![i] = (result78)[2]];
                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                    either {
                                      with (value562 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd163 = (fd)[j]) {
                                        await yielded_fd163;
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
                            with (result79 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                              sm := [sm EXCEPT ![i] = (result79)[1]];
                              smDomain := [smDomain EXCEPT ![i] = (result79)[2]];
                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                              either {
                                with (value563 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]];
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
                votedFor := [votedFor EXCEPT ![self] = Nil];
                leader := [leader EXCEPT ![self] = Nil];
                if (((m).mterm) < ((currentTerm)[self])) {
                  skip;
                  goto serverLoop;
                } else {
                  with (
                    i = self, 
                    j = (m).msource
                  ) {
                    assert ((m).mterm) = ((currentTerm)[i]);
                    if ((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m).mmatchIndex]];
                      goto serverLoop;
                    } else {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                      goto serverLoop;
                    };
                  };
                };
              } else {
                if (((m).mterm) < ((currentTerm)[self])) {
                  skip;
                  goto serverLoop;
                } else {
                  with (
                    i = self, 
                    j = (m).msource
                  ) {
                    assert ((m).mterm) = ((currentTerm)[i]);
                    if ((m).msuccess) {
                      nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m).mmatchIndex) + (1)]];
                      matchIndex := [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m).mmatchIndex]];
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
                    value70 = [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m).mcmd).idx, key |-> ((m).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j]
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
  }
  
  fair process (s1 \in ServerRequestVoteSet)
    variables idx0 = 1; srvId0 = (requestVoteSrvId)[self];
  {
    serverRequestVoteLoop:
      if (TRUE) {
        await leaderTimeout;
        with (yielded_network00 = Len(((network)[srvId0]).queue)) {
          await (yielded_network00) = (0);
          await ((state)[srvId0]) \in ({Follower, Candidate});
          with (i1 = srvId0) {
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
        if ((idx0) # (srvId0)) {
          either {
            with (value80 = [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId0], mlastLogTerm |-> LastTerm((log)[srvId0]), mlastLogIndex |-> Len((log)[srvId0]), msource |-> srvId0, mdest |-> idx0]) {
              await ((network)[idx0]).enabled;
              await (Len(((network)[idx0]).queue)) < (BufferSize);
              network := [network EXCEPT ![idx0] = [queue |-> Append(((network)[idx0]).queue, value80), enabled |-> ((network)[idx0]).enabled]];
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
    variables idx1; srvId1 = (appendEntriesSrvId)[self];
  {
    serverAppendEntriesLoop:
      if (appendEntriesCh) {
        await ((state)[srvId1]) = (Leader);
        idx1 := 1;
        goto appendEntriesLoop;
      } else {
        goto Done;
      };
    appendEntriesLoop:
      if ((((state)[srvId1]) = (Leader)) /\ ((idx1) <= (NumServers))) {
        if ((idx1) # (srvId1)) {
          with (
            prevLogIndex1 = (((nextIndex)[srvId1])[idx1]) - (1), 
            prevLogTerm1 = IF (prevLogIndex1) > (0) THEN (((log)[srvId1])[prevLogIndex1]).term ELSE 0, 
            lastEntry1 = Min({Len((log)[srvId1]), ((nextIndex)[srvId1])[idx1]}), 
            entries1 = SubSeq((log)[srvId1], ((nextIndex)[srvId1])[idx1], lastEntry1)
          ) {
            either {
              with (value90 = [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId1], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[srvId1], lastEntry1}), msource |-> srvId1, mdest |-> idx1]) {
                await ((network)[idx1]).enabled;
                await (Len(((network)[idx1]).queue)) < (BufferSize);
                network := [network EXCEPT ![idx1] = [queue |-> Append(((network)[idx1]).queue, value90), enabled |-> ((network)[idx1]).enabled]];
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
    variables newCommitIndex = 0; srvId2 = (advanceCommitIndexSrvId)[self];
  {
    serverAdvanceCommitIndexLoop:
      if (TRUE) {
        await ((state)[srvId2]) = (Leader);
        with (
          i = srvId2, 
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
      if (((commitIndex)[srvId2]) < (newCommitIndex)) {
        commitIndex := [commitIndex EXCEPT ![srvId2] = ((commitIndex)[srvId2]) + (1)];
        with (
          i = srvId2, 
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
              value100 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value100), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          } else {
            with (
              reqOk = ((cmd).key) \in ((smDomain)[i]), 
              value101 = [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client]
            ) {
              await ((network)[(entry).client]).enabled;
              await (Len(((network)[(entry).client]).queue)) < (BufferSize);
              network := [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value101), enabled |-> ((network)[(entry).client]).enabled]];
              goto applyLoop;
            };
          };
        };
      } else {
        goto serverAdvanceCommitIndexLoop;
      };
  }
  
  fair process (s4 \in ServerBecomeLeaderSet)
    variables srvId3 = (becomeLeaderSrvId)[self];
  {
    serverBecomeLeaderLoop:
      await (Len((becomeLeaderCh)[srvId3])) > (0);
      with (res0 = Head((becomeLeaderCh)[srvId3])) {
        becomeLeaderCh := [becomeLeaderCh EXCEPT ![srvId3] = Tail((becomeLeaderCh)[srvId3])];
        with (yielded_becomeLeaderCh = res0) {
          if (yielded_becomeLeaderCh) {
            await ((state)[srvId3]) = (Candidate);
            await isQuorum((votesGranted)[srvId3]);
            with (i = srvId3) {
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
        with (res10 = Head(reqCh)) {
          reqCh := Tail(reqCh);
          with (yielded_reqCh0 = res10) {
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
                with (value110 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value110), enabled |-> ((network)[leader0]).enabled]];
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
                  with (value120 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                    await ((network)[leader0]).enabled;
                    await (Len(((network)[leader0]).queue)) < (BufferSize);
                    network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value120), enabled |-> ((network)[leader0]).enabled]];
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
                with (value111 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value111), enabled |-> ((network)[leader0]).enabled]];
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
                  with (value121 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                    await ((network)[leader0]).enabled;
                    await (Len(((network)[leader0]).queue)) < (BufferSize);
                    network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value121), enabled |-> ((network)[leader0]).enabled]];
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
              with (value112 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value112), enabled |-> ((network)[leader0]).enabled]];
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
                with (value122 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value122), enabled |-> ((network)[leader0]).enabled]];
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
              with (value113 = [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx, type |-> Put, key |-> (req).key, value |-> (req).value], msource |-> self, mdest |-> leader0]) {
                await ((network)[leader0]).enabled;
                await (Len(((network)[leader0]).queue)) < (BufferSize);
                network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value113), enabled |-> ((network)[leader0]).enabled]];
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
                with (value123 = [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx, type |-> Get, key |-> (req).key], msource |-> self, mdest |-> leader0]) {
                  await ((network)[leader0]).enabled;
                  await (Len(((network)[leader0]).queue)) < (BufferSize);
                  network := [network EXCEPT ![leader0] = [queue |-> Append(((network)[leader0]).queue, value123), enabled |-> ((network)[leader0]).enabled]];
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
              assert ((resp).msource) = (leader0);
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
              assert ((resp).msource) = (leader0);
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
    variables srvId4 = (crasherSrvId)[self];
  {
    serverCrash:
      with (value130 = FALSE) {
        network := [network EXCEPT ![srvId4] = [queue |-> ((network)[srvId4]).queue, enabled |-> value130]];
        goto fdUpdate;
      };
    fdUpdate:
      with (value140 = TRUE) {
        fd := [fd EXCEPT ![srvId4] = value140];
        goto block;
      };
    block:
      await FALSE;
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "888b62ac" /\ chksum(tla) = "4fd0825b") PCal-18049938ece8066a38eb5044080cf45c
CONSTANT defaultInitValue
VARIABLES network, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, 
          log, plog, votedFor, votesResponded, votesGranted, leader, sm, 
          smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, allReqs, 
          reqCh, respCh, requestVoteSrvId, appendEntriesSrvId, 
          advanceCommitIndexSrvId, becomeLeaderSrvId, crasherSrvId, pc

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
ServerCrasherSet == IF ExploreFail THEN (((5) * (NumServers)) + (1)) .. (((5) * (NumServers)) + (MaxNodeFail)) ELSE {}
ClientSet == (((6) * (NumServers)) + (1)) .. (((6) * (NumServers)) + (NumClients))
NodeSet == (ServerSet) \union (ClientSet)
KeySet == {}

VARIABLES idx, m, srvId, idx0, srvId0, idx1, srvId1, newCommitIndex, srvId2, 
          srvId3, leader0, req, resp, reqIdx, timeout, srvId4

vars == << network, fd, state, currentTerm, commitIndex, nextIndex, 
           matchIndex, log, plog, votedFor, votesResponded, votesGranted, 
           leader, sm, smDomain, leaderTimeout, appendEntriesCh, 
           becomeLeaderCh, allReqs, reqCh, respCh, requestVoteSrvId, 
           appendEntriesSrvId, advanceCommitIndexSrvId, becomeLeaderSrvId, 
           crasherSrvId, pc, idx, m, srvId, idx0, srvId0, idx1, srvId1, 
           newCommitIndex, srvId2, srvId3, leader0, req, resp, reqIdx, 
           timeout, srvId4 >>

ProcSet == (ServerSet) \cup (ServerRequestVoteSet) \cup (ServerAppendEntriesSet) \cup (ServerAdvanceCommitIndexSet) \cup (ServerBecomeLeaderSet) \cup (ClientSet) \cup (ServerCrasherSet)

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
        /\ allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>
        /\ reqCh = SubSeq(allReqs, 1, NumRequests)
        /\ respCh = defaultInitValue
        /\ requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]
        /\ appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]
        /\ advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]
        /\ becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]
        /\ crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((5) * (NumServers))]
        (* Process s0 *)
        /\ idx = [self \in ServerSet |-> 1]
        /\ m = [self \in ServerSet |-> defaultInitValue]
        /\ srvId = [self \in ServerSet |-> self]
        (* Process s1 *)
        /\ idx0 = [self \in ServerRequestVoteSet |-> 1]
        /\ srvId0 = [self \in ServerRequestVoteSet |-> (requestVoteSrvId)[self]]
        (* Process s2 *)
        /\ idx1 = [self \in ServerAppendEntriesSet |-> defaultInitValue]
        /\ srvId1 = [self \in ServerAppendEntriesSet |-> (appendEntriesSrvId)[self]]
        (* Process s3 *)
        /\ newCommitIndex = [self \in ServerAdvanceCommitIndexSet |-> 0]
        /\ srvId2 = [self \in ServerAdvanceCommitIndexSet |-> (advanceCommitIndexSrvId)[self]]
        (* Process s4 *)
        /\ srvId3 = [self \in ServerBecomeLeaderSet |-> (becomeLeaderSrvId)[self]]
        (* Process client *)
        /\ leader0 = [self \in ClientSet |-> Nil]
        /\ req = [self \in ClientSet |-> defaultInitValue]
        /\ resp = [self \in ClientSet |-> defaultInitValue]
        /\ reqIdx = [self \in ClientSet |-> 0]
        /\ timeout = [self \in ClientSet |-> FALSE]
        (* Process crasher *)
        /\ srvId4 = [self \in ServerCrasherSet |-> (crasherSrvId)[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                                        [] self \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                                        [] self \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                                        [] self \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                                        [] self \in ClientSet -> "clientLoop"
                                        [] self \in ServerCrasherSet -> "serverCrash"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ Assert(((network)[self]).enabled, 
                                         "Failure of assertion at line 984, column 9.")
                               /\ (Len(((network)[self]).queue)) > (0)
                               /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                    /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                    /\ LET yielded_network3 == readMsg00 IN
                                         /\ m' = [m EXCEPT ![self] = yielded_network3]
                                         /\ Assert(((m'[self]).mdest) = (self), 
                                                   "Failure of assertion at line 990, column 13.")
                                         /\ leaderTimeout' = LeaderTimeoutReset
                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, leaderTimeout, m >>
                    /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                    nextIndex, matchIndex, log, plog, votedFor, 
                                    votesResponded, votesGranted, leader, sm, 
                                    smDomain, appendEntriesCh, becomeLeaderCh, 
                                    allReqs, reqCh, respCh, requestVoteSrvId, 
                                    appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    crasherSrvId, idx, srvId, idx0, srvId0, 
                                    idx1, srvId1, newCommitIndex, srvId2, 
                                    srvId3, leader0, req, resp, reqIdx, 
                                    timeout, srvId4 >>

handleMsg(self) == /\ pc[self] = "handleMsg"
                   /\ IF ((m[self]).mtype) = (RequestVoteRequest)
                         THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                    THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                         /\ state' = [state EXCEPT ![self] = Follower]
                                         /\ LET votedFor1 == [votedFor EXCEPT ![self] = Nil] IN
                                              /\ leader' = [leader EXCEPT ![self] = Nil]
                                              /\ LET i == self IN
                                                   LET j == (m[self]).msource IN
                                                     LET logOK == (((m[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                       LET grant == ((((m[self]).mterm) = ((currentTerm')[i])) /\ (logOK)) /\ (((votedFor1)[self]) \in ({Nil, j})) IN
                                                         /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                   "Failure of assertion at line 1011, column 15.")
                                                         /\ IF grant
                                                               THEN /\ votedFor' = [votedFor1 EXCEPT ![i] = j]
                                                                    /\ \/ /\ LET value00 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value00), enabled |-> ((network)[j]).enabled]]
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
                                                               ELSE /\ \/ /\ LET value01 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value01), enabled |-> ((network)[j]).enabled]]
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
                                    ELSE /\ LET i == self IN
                                              LET j == (m[self]).msource IN
                                                LET logOK == (((m[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                  LET grant == ((((m[self]).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[self]) \in ({Nil, j})) IN
                                                    /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                              "Failure of assertion at line 1075, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                                               /\ \/ /\ LET value02 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value02), enabled |-> ((network)[j]).enabled]]
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
                                                          ELSE /\ \/ /\ LET value03 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value03), enabled |-> ((network)[j]).enabled]]
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
                                              smDomain, becomeLeaderCh >>
                         ELSE /\ IF ((m[self]).mtype) = (RequestVoteResponse)
                                    THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                    /\ state' = [state EXCEPT ![self] = Follower]
                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                    /\ leader' = [leader EXCEPT ![self] = Nil]
                                                    /\ IF ((m[self]).mterm) < ((currentTerm')[self])
                                                          THEN /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted, 
                                                                               becomeLeaderCh >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                "Failure of assertion at line 1143, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state')[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value15 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value15)]
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            /\ UNCHANGED becomeLeaderCh
                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                 /\ UNCHANGED << votesGranted, 
                                                                                                 becomeLeaderCh >>
                                               ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                          THEN /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                               /\ UNCHANGED << votesResponded, 
                                                                               votesGranted, 
                                                                               becomeLeaderCh >>
                                                          ELSE /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                "Failure of assertion at line 1169, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value16 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value16)]
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
                                                         smDomain >>
                                    ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                               /\ LET state1 == [state EXCEPT ![self] = Follower] IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                    /\ LET leader1 == [leader EXCEPT ![self] = Nil] IN
                                                                         /\ leader' = [leader1 EXCEPT ![self] = (m[self]).msource]
                                                                         /\ LET i == self IN
                                                                              LET j == (m[self]).msource IN
                                                                                LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                                  /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                                            "Failure of assertion at line 1200, column 21.")
                                                                                  /\ IF (((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                        THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                             /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                   THEN /\ \/ /\ LET value20 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]]
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
                                                                                                   ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                  "Failure of assertion at line 1218, column 25.")
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
                                                                                                                                                                    THEN /\ LET result16 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result16)[1]]
                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result16)[2]]
                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                              /\ \/ /\ LET value50 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                                                                                                         /\ yielded_fd11
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                                         commitIndex, 
                                                                                                                                                                                         sm, 
                                                                                                                                                                                         smDomain >>
                                                                                                                                                         ELSE /\ IF ((value40).cmd) = (LogPop)
                                                                                                                                                                    THEN /\ plog' = [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result17 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result17)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result17)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value51 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd12
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result18 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result18)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result18)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value52 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ plog' = plog4
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd13
                                                                                                                                                                                                    /\ plog' = plog4
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ plog' = plog4
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                            ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                       THEN /\ LET result19 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                 /\ sm' = [sm EXCEPT ![i] = (result19)[1]]
                                                                                                                                                                 /\ smDomain' = [smDomain EXCEPT ![i] = (result19)[2]]
                                                                                                                                                                 /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                 /\ \/ /\ LET value53 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog4
                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    \/ /\ LET yielded_fd14 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd14
                                                                                                                                                                            /\ plog' = plog4
                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ plog' = plog4
                                                                                                                                                            /\ log' = log4
                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            /\ UNCHANGED << network, 
                                                                                                                                                                            commitIndex, 
                                                                                                                                                                            sm, 
                                                                                                                                                                            smDomain >>
                                                                                                                               ELSE /\ IF ((value30).cmd) = (LogPop)
                                                                                                                                          THEN /\ LET plog5 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ LET value41 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                                 IF ((value41).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value41).entries)]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result20 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result20)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result20)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value54 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd15 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd15
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF ((value41).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result21 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result21)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result21)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value55 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd16 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd16
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result22 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result22)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result22)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value56 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog5
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd17 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd17
                                                                                                                                                                                                               /\ plog' = plog5
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ plog' = plog5
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET result23 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result23)[1]]
                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result23)[2]]
                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                            /\ \/ /\ LET value57 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog5
                                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd18 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd18
                                                                                                                                                                                       /\ plog' = plog5
                                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ plog' = plog5
                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED << network, 
                                                                                                                                                                                       commitIndex, 
                                                                                                                                                                                       sm, 
                                                                                                                                                                                       smDomain >>
                                                                                                                                          ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                     THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ LET value42 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                               IF ((value42).cmd) = (LogConcat)
                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value42).entries)]
                                                                                                                                                                       /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET result24 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result24)[1]]
                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result24)[2]]
                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                       /\ \/ /\ LET value58 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd19 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd19
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                                  commitIndex, 
                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                  ELSE /\ IF ((value42).cmd) = (LogPop)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result25 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result25)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result25)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value59 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd110 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd110
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result26 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result26)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result26)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value510 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd111 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd111
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                                  /\ plog' = plog
                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                THEN /\ LET result27 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result27)[1]]
                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result27)[2]]
                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                          /\ \/ /\ LET value511 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ log' = log4
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             \/ /\ LET yielded_fd112 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd112
                                                                                                                                                                                     /\ log' = log4
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = log4
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                     sm, 
                                                                                                                                                                                     smDomain >>
                                                                                                                                                          /\ plog' = plog
                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                           THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                                /\ LET value43 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                     IF ((value43).cmd) = (LogConcat)
                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value43).entries)]
                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                   THEN /\ LET result28 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result28)[1]]
                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result28)[2]]
                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                             /\ \/ /\ LET value512 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                \/ /\ LET yielded_fd113 == (fd)[j] IN
                                                                                                                                                                        /\ yielded_fd113
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                        commitIndex, 
                                                                                                                                                                        sm, 
                                                                                                                                                                        smDomain >>
                                                                                                                                        ELSE /\ IF ((value43).cmd) = (LogPop)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result29 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result29)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result29)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value513 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd114 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd114
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result30 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result30)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result30)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value514 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd115 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd115
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                        /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                      THEN /\ LET result31 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result31)[1]]
                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result31)[2]]
                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                /\ \/ /\ LET value515 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                   \/ /\ LET yielded_fd116 == (fd)[j] IN
                                                                                                                                                           /\ yielded_fd116
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                           commitIndex, 
                                                                                                                                                           sm, 
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
                                                                                                   ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                  "Failure of assertion at line 1687, column 25.")
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
                                                                                                                                                                    THEN /\ LET result32 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result32)[1]]
                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result32)[2]]
                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                              /\ \/ /\ LET value516 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 \/ /\ LET yielded_fd117 == (fd)[j] IN
                                                                                                                                                                                         /\ yielded_fd117
                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                                    ELSE /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                                         commitIndex, 
                                                                                                                                                                                         sm, 
                                                                                                                                                                                         smDomain >>
                                                                                                                                                         ELSE /\ IF ((value44).cmd) = (LogPop)
                                                                                                                                                                    THEN /\ plog' = [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result33 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result33)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result33)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value517 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd118 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd118
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result34 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result34)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result34)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value518 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ plog' = plog6
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd119 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd119
                                                                                                                                                                                                    /\ plog' = plog6
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ plog' = plog6
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                            ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                       THEN /\ LET result35 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                 /\ sm' = [sm EXCEPT ![i] = (result35)[1]]
                                                                                                                                                                 /\ smDomain' = [smDomain EXCEPT ![i] = (result35)[2]]
                                                                                                                                                                 /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                 /\ \/ /\ LET value519 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog6
                                                                                                                                                                            /\ log' = log5
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    \/ /\ LET yielded_fd120 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd120
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
                                                                                                                                                                            sm, 
                                                                                                                                                                            smDomain >>
                                                                                                                               ELSE /\ IF ((value31).cmd) = (LogPop)
                                                                                                                                          THEN /\ LET plog7 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ LET value45 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                                 IF ((value45).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value45).entries)]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result36 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result36)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result36)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value520 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd121 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd121
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF ((value45).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result37 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result37)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result37)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value521 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd122 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd122
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result38 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result38)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result38)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value522 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog7
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd123 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd123
                                                                                                                                                                                                               /\ plog' = plog7
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ plog' = plog7
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET result39 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result39)[1]]
                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result39)[2]]
                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                            /\ \/ /\ LET value523 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog7
                                                                                                                                                                                       /\ log' = log5
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd124 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd124
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
                                                                                                                                                                                       sm, 
                                                                                                                                                                                       smDomain >>
                                                                                                                                          ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                     THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ LET value46 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                               IF ((value46).cmd) = (LogConcat)
                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value46).entries)]
                                                                                                                                                                       /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET result40 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result40)[1]]
                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result40)[2]]
                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                       /\ \/ /\ LET value524 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd125 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd125
                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                                             ELSE /\ state' = state1
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                                  commitIndex, 
                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                  ELSE /\ IF ((value46).cmd) = (LogPop)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result41 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result41)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result41)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value525 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd126 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd126
                                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ state' = state1
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result42 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result42)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result42)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value526 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd127 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd127
                                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ state' = state1
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                                  /\ plog' = plog
                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                THEN /\ LET result43 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result43)[1]]
                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result43)[2]]
                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                          /\ \/ /\ LET value527 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ log' = log5
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             \/ /\ LET yielded_fd128 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd128
                                                                                                                                                                                     /\ log' = log5
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = log5
                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                     sm, 
                                                                                                                                                                                     smDomain >>
                                                                                                                                                          /\ plog' = plog
                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                           THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                                /\ LET value47 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                     IF ((value47).cmd) = (LogConcat)
                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value47).entries)]
                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                   THEN /\ LET result44 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result44)[1]]
                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result44)[2]]
                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                             /\ \/ /\ LET value528 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                \/ /\ LET yielded_fd129 == (fd)[j] IN
                                                                                                                                                                        /\ yielded_fd129
                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                        commitIndex, 
                                                                                                                                                                        sm, 
                                                                                                                                                                        smDomain >>
                                                                                                                                        ELSE /\ IF ((value47).cmd) = (LogPop)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result45 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result45)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result45)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value529 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd130 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd130
                                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ state' = state1
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result46 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result46)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result46)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value530 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd131 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd131
                                                                                                                                                                                   /\ state' = state1
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ state' = state1
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                        /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                      THEN /\ LET result47 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result47)[1]]
                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result47)[2]]
                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                /\ \/ /\ LET value531 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                           /\ state' = state1
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                   \/ /\ LET yielded_fd132 == (fd)[j] IN
                                                                                                                                                           /\ yielded_fd132
                                                                                                                                                           /\ state' = state1
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                      ELSE /\ state' = state1
                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                           commitIndex, 
                                                                                                                                                           sm, 
                                                                                                                                                           smDomain >>
                                                                                                                                /\ UNCHANGED << log, 
                                                                                                                                                plog >>
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                                                  "Failure of assertion at line 2197, column 17.")
                                                                        /\ IF (((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value22 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value22), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                                                         /\ yielded_fd02
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                              log, 
                                                                                                              plog, 
                                                                                                              sm, 
                                                                                                              smDomain >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2215, column 21.")
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
                                                                                                                                                          THEN /\ LET result48 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result48)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result48)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value532 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd133 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd133
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               commitIndex, 
                                                                                                                                                                               sm, 
                                                                                                                                                                               smDomain >>
                                                                                                                                               ELSE /\ IF ((value48).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result49 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result49)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result49)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value533 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd134 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd134
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result50 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result50)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result50)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value534 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd135 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd135
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog8
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET result51 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result51)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result51)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value535 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd136 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd136
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog8
                                                                                                                                                  /\ log' = log6
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  commitIndex, 
                                                                                                                                                                  sm, 
                                                                                                                                                                  smDomain >>
                                                                                                                     ELSE /\ IF ((value32).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value49 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value49).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value49).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result52 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result52)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result52)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value536 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd137 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd137
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF ((value49).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result53 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result53)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result53)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                          /\ \/ /\ LET value537 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd138 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd138
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result54 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result54)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result54)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                          /\ \/ /\ LET value538 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd139 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd139
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog9
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET result55 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result55)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result55)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value539 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd140 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd140
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog9
                                                                                                                                                             /\ log' = log6
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             commitIndex, 
                                                                                                                                                                             sm, 
                                                                                                                                                                             smDomain >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value410 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value410).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value410).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET result56 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result56)[1]]
                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result56)[2]]
                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                             /\ \/ /\ LET value540 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd141 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd141
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                        sm, 
                                                                                                                                                                                        smDomain >>
                                                                                                                                                        ELSE /\ IF ((value410).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result57 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result57)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result57)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                        /\ \/ /\ LET value541 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd142 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd142
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result58 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result58)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result58)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                        /\ \/ /\ LET value542 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd143 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd143
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET result59 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result59)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result59)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value543 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd144 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd144
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log6
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           commitIndex, 
                                                                                                                                                                           sm, 
                                                                                                                                                                           smDomain >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value411 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value411).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value411).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET result60 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result60)[1]]
                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result60)[2]]
                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                   /\ \/ /\ LET value544 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd145 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd145
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              commitIndex, 
                                                                                                                                                              sm, 
                                                                                                                                                              smDomain >>
                                                                                                                              ELSE /\ IF ((value411).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result61 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result61)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result61)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value545 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd146 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd146
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm, 
                                                                                                                                                                         smDomain >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result62 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result62)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result62)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value546 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd147 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd147
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm, 
                                                                                                                                                                         smDomain >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET result63 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                      /\ sm' = [sm EXCEPT ![i] = (result63)[1]]
                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![i] = (result63)[2]]
                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                      /\ \/ /\ LET value547 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd148 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd148
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex, 
                                                                                                                                                 sm, 
                                                                                                                                                 smDomain >>
                                                                                                                      /\ UNCHANGED << log, 
                                                                                                                                      plog >>
                                                                              ELSE /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value23 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value23), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                                                         /\ yielded_fd03
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                              log, 
                                                                                                              plog, 
                                                                                                              sm, 
                                                                                                              smDomain >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2682, column 21.")
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
                                                                                                                                                          THEN /\ LET result64 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result64)[1]]
                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result64)[2]]
                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                    /\ \/ /\ LET value548 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd149 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd149
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               commitIndex, 
                                                                                                                                                                               sm, 
                                                                                                                                                                               smDomain >>
                                                                                                                                               ELSE /\ IF ((value412).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result65 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result65)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result65)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value549 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd150 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd150
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result66 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result66)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result66)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value550 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd151 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd151
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog10
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET result67 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result67)[1]]
                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result67)[2]]
                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                       /\ \/ /\ LET value551 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd152 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd152
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog10
                                                                                                                                                  /\ log' = log7
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  commitIndex, 
                                                                                                                                                                  sm, 
                                                                                                                                                                  smDomain >>
                                                                                                                     ELSE /\ IF ((value33).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value413 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value413).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value413).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET result68 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result68)[1]]
                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result68)[2]]
                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                               /\ \/ /\ LET value552 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd153 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd153
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          commitIndex, 
                                                                                                                                                                                          sm, 
                                                                                                                                                                                          smDomain >>
                                                                                                                                                          ELSE /\ IF ((value413).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result69 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result69)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result69)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                          /\ \/ /\ LET value553 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd154 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd154
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET result70 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                          /\ sm' = [sm EXCEPT ![i] = (result70)[1]]
                                                                                                                                                                                          /\ smDomain' = [smDomain EXCEPT ![i] = (result70)[2]]
                                                                                                                                                                                          /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                          /\ \/ /\ LET value554 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd155 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd155
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog11
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     commitIndex, 
                                                                                                                                                                                                     sm, 
                                                                                                                                                                                                     smDomain >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET result71 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result71)[1]]
                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result71)[2]]
                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                  /\ \/ /\ LET value555 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd156 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd156
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog11
                                                                                                                                                             /\ log' = log7
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             commitIndex, 
                                                                                                                                                                             sm, 
                                                                                                                                                                             smDomain >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value414 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value414).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value414).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET result72 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result72)[1]]
                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result72)[2]]
                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                             /\ \/ /\ LET value556 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd157 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd157
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        commitIndex, 
                                                                                                                                                                                        sm, 
                                                                                                                                                                                        smDomain >>
                                                                                                                                                        ELSE /\ IF ((value414).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result73 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result73)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result73)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                        /\ \/ /\ LET value557 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd158 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd158
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET result74 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result74)[1]]
                                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result74)[2]]
                                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                                        /\ \/ /\ LET value558 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd159 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd159
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   commitIndex, 
                                                                                                                                                                                                   sm, 
                                                                                                                                                                                                   smDomain >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET result75 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                /\ sm' = [sm EXCEPT ![i] = (result75)[1]]
                                                                                                                                                                /\ smDomain' = [smDomain EXCEPT ![i] = (result75)[2]]
                                                                                                                                                                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                                /\ \/ /\ LET value559 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd160 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd160
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log7
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           commitIndex, 
                                                                                                                                                                           sm, 
                                                                                                                                                                           smDomain >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value415 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value415).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value415).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET result76 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result76)[1]]
                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result76)[2]]
                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                   /\ \/ /\ LET value560 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd161 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd161
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              commitIndex, 
                                                                                                                                                              sm, 
                                                                                                                                                              smDomain >>
                                                                                                                              ELSE /\ IF ((value415).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result77 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result77)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result77)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value561 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd162 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd162
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm, 
                                                                                                                                                                         smDomain >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET result78 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result78)[1]]
                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result78)[2]]
                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                                              /\ \/ /\ LET value562 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd163 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd163
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         commitIndex, 
                                                                                                                                                                         sm, 
                                                                                                                                                                         smDomain >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET result79 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                      /\ sm' = [sm EXCEPT ![i] = (result79)[1]]
                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![i] = (result79)[2]]
                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m[self]).mcommitIndex})]
                                                                                                                                      /\ \/ /\ LET value563 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd164 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd164
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 commitIndex, 
                                                                                                                                                 sm, 
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
                                                                          /\ leader' = [leader EXCEPT ![self] = Nil]
                                                                          /\ IF ((m[self]).mterm) < ((currentTerm')[self])
                                                                                THEN /\ TRUE
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                                      "Failure of assertion at line 3151, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                       /\ UNCHANGED matchIndex
                                                                     ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                                                THEN /\ TRUE
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     /\ UNCHANGED << nextIndex, 
                                                                                                     matchIndex >>
                                                                                ELSE /\ LET i == self IN
                                                                                          LET j == (m[self]).msource IN
                                                                                            /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                                      "Failure of assertion at line 3171, column 21.")
                                                                                            /\ IF (m[self]).msuccess
                                                                                                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m[self]).mmatchIndex]]
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
                                                                                              LET value70 == [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> ((m[self]).mcmd).idx, key |-> ((m[self]).mcmd).key], mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j] IN
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
                                                                               currentTerm, 
                                                                               nextIndex, 
                                                                               matchIndex, 
                                                                               votedFor, 
                                                                               leader >>
                                                    /\ UNCHANGED << commitIndex, 
                                                                    sm, 
                                                                    smDomain >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted, 
                                                         becomeLeaderCh >>
                   /\ UNCHANGED << fd, leaderTimeout, appendEntriesCh, allReqs, 
                                   reqCh, respCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, crasherSrvId, idx, m, 
                                   srvId, idx0, srvId0, idx1, srvId1, 
                                   newCommitIndex, srvId2, srvId3, leader0, 
                                   req, resp, reqIdx, timeout, srvId4 >>

s0(self) == serverLoop(self) \/ handleMsg(self)

serverRequestVoteLoop(self) == /\ pc[self] = "serverRequestVoteLoop"
                               /\ IF TRUE
                                     THEN /\ leaderTimeout
                                          /\ LET yielded_network00 == Len(((network)[srvId0[self]]).queue) IN
                                               /\ (yielded_network00) = (0)
                                               /\ ((state)[srvId0[self]]) \in ({Follower, Candidate})
                                               /\ LET i1 == srvId0[self] IN
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
                                               becomeLeaderCh, allReqs, reqCh, 
                                               respCh, requestVoteSrvId, 
                                               appendEntriesSrvId, 
                                               advanceCommitIndexSrvId, 
                                               becomeLeaderSrvId, crasherSrvId, 
                                               idx, m, srvId, srvId0, idx1, 
                                               srvId1, newCommitIndex, srvId2, 
                                               srvId3, leader0, req, resp, 
                                               reqIdx, timeout, srvId4 >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx0[self]) <= (NumServers)
                               THEN /\ IF (idx0[self]) # (srvId0[self])
                                          THEN /\ \/ /\ LET value80 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId0[self]], mlastLogTerm |-> LastTerm((log)[srvId0[self]]), mlastLogIndex |-> Len((log)[srvId0[self]]), msource |-> srvId0[self], mdest |-> idx0[self]] IN
                                                          /\ ((network)[idx0[self]]).enabled
                                                          /\ (Len(((network)[idx0[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![idx0[self]] = [queue |-> Append(((network)[idx0[self]]).queue, value80), enabled |-> ((network)[idx0[self]]).enabled]]
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
                                         becomeLeaderCh, allReqs, reqCh, 
                                         respCh, requestVoteSrvId, 
                                         appendEntriesSrvId, 
                                         advanceCommitIndexSrvId, 
                                         becomeLeaderSrvId, crasherSrvId, idx, 
                                         m, srvId, srvId0, idx1, srvId1, 
                                         newCommitIndex, srvId2, srvId3, 
                                         leader0, req, resp, reqIdx, timeout, 
                                         srvId4 >>

s1(self) == serverRequestVoteLoop(self) \/ requestVoteLoop(self)

serverAppendEntriesLoop(self) == /\ pc[self] = "serverAppendEntriesLoop"
                                 /\ IF appendEntriesCh
                                       THEN /\ ((state)[srvId1[self]]) = (Leader)
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
                                                 becomeLeaderCh, allReqs, 
                                                 reqCh, respCh, 
                                                 requestVoteSrvId, 
                                                 appendEntriesSrvId, 
                                                 advanceCommitIndexSrvId, 
                                                 becomeLeaderSrvId, 
                                                 crasherSrvId, idx, m, srvId, 
                                                 idx0, srvId0, srvId1, 
                                                 newCommitIndex, srvId2, 
                                                 srvId3, leader0, req, resp, 
                                                 reqIdx, timeout, srvId4 >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ IF (((state)[srvId1[self]]) = (Leader)) /\ ((idx1[self]) <= (NumServers))
                                 THEN /\ IF (idx1[self]) # (srvId1[self])
                                            THEN /\ LET prevLogIndex1 == (((nextIndex)[srvId1[self]])[idx1[self]]) - (1) IN
                                                      LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN (((log)[srvId1[self]])[prevLogIndex1]).term ELSE 0 IN
                                                        LET lastEntry1 == Min({Len((log)[srvId1[self]]), ((nextIndex)[srvId1[self]])[idx1[self]]}) IN
                                                          LET entries1 == SubSeq((log)[srvId1[self]], ((nextIndex)[srvId1[self]])[idx1[self]], lastEntry1) IN
                                                            \/ /\ LET value90 == [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId1[self]], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> Min({(commitIndex)[srvId1[self]], lastEntry1}), msource |-> srvId1[self], mdest |-> idx1[self]] IN
                                                                    /\ ((network)[idx1[self]]).enabled
                                                                    /\ (Len(((network)[idx1[self]]).queue)) < (BufferSize)
                                                                    /\ network' = [network EXCEPT ![idx1[self]] = [queue |-> Append(((network)[idx1[self]]).queue, value90), enabled |-> ((network)[idx1[self]]).enabled]]
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
                                           becomeLeaderCh, allReqs, reqCh, 
                                           respCh, requestVoteSrvId, 
                                           appendEntriesSrvId, 
                                           advanceCommitIndexSrvId, 
                                           becomeLeaderSrvId, crasherSrvId, 
                                           idx, m, srvId, idx0, srvId0, srvId1, 
                                           newCommitIndex, srvId2, srvId3, 
                                           leader0, req, resp, reqIdx, timeout, 
                                           srvId4 >>

s2(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)

serverAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverAdvanceCommitIndexLoop"
                                      /\ IF TRUE
                                            THEN /\ ((state)[srvId2[self]]) = (Leader)
                                                 /\ LET i == srvId2[self] IN
                                                      LET maxAgreeIndex == FindMaxAgreeIndex((log)[i], i, (matchIndex)[i]) IN
                                                        LET nCommitIndex == IF ((maxAgreeIndex) # (Nil)) /\ (((((log)[i])[maxAgreeIndex]).term) = ((currentTerm)[i])) THEN maxAgreeIndex ELSE (commitIndex)[i] IN
                                                          /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                                          /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                                    "Failure of assertion at line 3337, column 11.")
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
                                                      becomeLeaderCh, allReqs, 
                                                      reqCh, respCh, 
                                                      requestVoteSrvId, 
                                                      appendEntriesSrvId, 
                                                      advanceCommitIndexSrvId, 
                                                      becomeLeaderSrvId, 
                                                      crasherSrvId, idx, m, 
                                                      srvId, idx0, srvId0, 
                                                      idx1, srvId1, srvId2, 
                                                      srvId3, leader0, req, 
                                                      resp, reqIdx, timeout, 
                                                      srvId4 >>

applyLoop(self) == /\ pc[self] = "applyLoop"
                   /\ IF ((commitIndex)[srvId2[self]]) < (newCommitIndex[self])
                         THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId2[self]] = ((commitIndex)[srvId2[self]]) + (1)]
                              /\ LET i == srvId2[self] IN
                                   LET k == (commitIndex')[i] IN
                                     LET entry == ((log)[i])[k] IN
                                       LET cmd == (entry).cmd IN
                                         LET respType == IF ((cmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                           IF ((cmd).type) = (Put)
                                              THEN /\ sm' = [sm EXCEPT ![i] = ((sm)[i]) @@ (((cmd).key) :> ((cmd).value))]
                                                   /\ smDomain' = [smDomain EXCEPT ![i] = ((smDomain)[i]) \union ({(cmd).key})]
                                                   /\ LET reqOk == ((cmd).key) \in ((smDomain')[i]) IN
                                                        LET value100 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm')[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value100), enabled |-> ((network)[(entry).client]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                              ELSE /\ LET reqOk == ((cmd).key) \in ((smDomain)[i]) IN
                                                        LET value101 == [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> (cmd).idx, key |-> (cmd).key, value |-> IF reqOk THEN ((sm)[i])[(cmd).key] ELSE Nil, ok |-> reqOk], mleaderHint |-> i, msource |-> i, mdest |-> (entry).client] IN
                                                          /\ ((network)[(entry).client]).enabled
                                                          /\ (Len(((network)[(entry).client]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![(entry).client] = [queue |-> Append(((network)[(entry).client]).queue, value101), enabled |-> ((network)[(entry).client]).enabled]]
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
                                   becomeLeaderCh, allReqs, reqCh, respCh, 
                                   requestVoteSrvId, appendEntriesSrvId, 
                                   advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                   crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                   idx1, srvId1, newCommitIndex, srvId2, 
                                   srvId3, leader0, req, resp, reqIdx, timeout, 
                                   srvId4 >>

s3(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)

serverBecomeLeaderLoop(self) == /\ pc[self] = "serverBecomeLeaderLoop"
                                /\ (Len((becomeLeaderCh)[srvId3[self]])) > (0)
                                /\ LET res0 == Head((becomeLeaderCh)[srvId3[self]]) IN
                                     /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![srvId3[self]] = Tail((becomeLeaderCh)[srvId3[self]])]
                                     /\ LET yielded_becomeLeaderCh == res0 IN
                                          IF yielded_becomeLeaderCh
                                             THEN /\ ((state)[srvId3[self]]) = (Candidate)
                                                  /\ isQuorum((votesGranted)[srvId3[self]])
                                                  /\ LET i == srvId3[self] IN
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
                                                leaderTimeout, allReqs, reqCh, 
                                                respCh, requestVoteSrvId, 
                                                appendEntriesSrvId, 
                                                advanceCommitIndexSrvId, 
                                                becomeLeaderSrvId, 
                                                crasherSrvId, idx, m, srvId, 
                                                idx0, srvId0, idx1, srvId1, 
                                                newCommitIndex, srvId2, srvId3, 
                                                leader0, req, resp, reqIdx, 
                                                timeout, srvId4 >>

s4(self) == serverBecomeLeaderLoop(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ (Len(reqCh)) > (0)
                               /\ LET res10 == Head(reqCh) IN
                                    /\ reqCh' = Tail(reqCh)
                                    /\ LET yielded_reqCh0 == res10 IN
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
                                    becomeLeaderCh, allReqs, respCh, 
                                    requestVoteSrvId, appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                    idx1, srvId1, newCommitIndex, srvId2, 
                                    srvId3, leader0, resp, timeout, srvId4 >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (leader0[self]) = (Nil)
                      THEN /\ \E srv1 \in ServerSet:
                                /\ leader0' = [leader0 EXCEPT ![self] = srv1]
                                /\ IF Debug
                                      THEN /\ PrintT(<<"ClientSndReq", self, leader0'[self], reqIdx[self], req[self]>>)
                                           /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value110 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value110), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd40 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd40
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value120 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value120), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                    \/ /\ LET yielded_fd50 == (fd)[leader0'[self]] IN
                                                                            /\ yielded_fd50
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                       /\ UNCHANGED network
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                 /\ UNCHANGED network
                                      ELSE /\ IF ((req[self]).type) = (Put)
                                                 THEN /\ \/ /\ LET value111 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0'[self]] IN
                                                                 /\ ((network)[leader0'[self]]).enabled
                                                                 /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                 /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value111), enabled |-> ((network)[leader0'[self]]).enabled]]
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                         \/ /\ LET yielded_fd41 == (fd)[leader0'[self]] IN
                                                                 /\ yielded_fd41
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                                 ELSE /\ IF ((req[self]).type) = (Get)
                                                            THEN /\ \/ /\ LET value121 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0'[self]] IN
                                                                            /\ ((network)[leader0'[self]]).enabled
                                                                            /\ (Len(((network)[leader0'[self]]).queue)) < (BufferSize)
                                                                            /\ network' = [network EXCEPT ![leader0'[self]] = [queue |-> Append(((network)[leader0'[self]]).queue, value121), enabled |-> ((network)[leader0'[self]]).enabled]]
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
                                            THEN /\ \/ /\ LET value112 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value112), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd42 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd42
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value122 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value122), enabled |-> ((network)[leader0[self]]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                               \/ /\ LET yielded_fd52 == (fd)[leader0[self]] IN
                                                                       /\ yielded_fd52
                                                                       /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED network
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            /\ UNCHANGED network
                                 ELSE /\ IF ((req[self]).type) = (Put)
                                            THEN /\ \/ /\ LET value113 == [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Put, key |-> (req[self]).key, value |-> (req[self]).value], msource |-> self, mdest |-> leader0[self]] IN
                                                            /\ ((network)[leader0[self]]).enabled
                                                            /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                            /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value113), enabled |-> ((network)[leader0[self]]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                    \/ /\ LET yielded_fd43 == (fd)[leader0[self]] IN
                                                            /\ yielded_fd43
                                                            /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED network
                                            ELSE /\ IF ((req[self]).type) = (Get)
                                                       THEN /\ \/ /\ LET value123 == [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[self], type |-> Get, key |-> (req[self]).key], msource |-> self, mdest |-> leader0[self]] IN
                                                                       /\ ((network)[leader0[self]]).enabled
                                                                       /\ (Len(((network)[leader0[self]]).queue)) < (BufferSize)
                                                                       /\ network' = [network EXCEPT ![leader0[self]] = [queue |-> Append(((network)[leader0[self]]).queue, value123), enabled |-> ((network)[leader0[self]]).enabled]]
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
                                becomeLeaderCh, allReqs, reqCh, respCh, 
                                requestVoteSrvId, appendEntriesSrvId, 
                                advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                idx1, srvId1, newCommitIndex, srvId2, srvId3, 
                                req, resp, reqIdx, timeout, srvId4 >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 3579, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg10 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network10 == readMsg10 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network10]
                                 /\ IF Debug
                                       THEN /\ PrintT(<<"ClientRcvResp", self, leader0[self], reqIdx[self], resp'[self]>>)
                                            /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3587, column 15.")
                                            /\ Assert(((resp'[self]).msource) = (leader0[self]), 
                                                      "Failure of assertion at line 3588, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3593, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3597, column 19.")
                                                                  /\ respCh' = resp'[self]
                                                                  /\ IF Debug
                                                                        THEN /\ PrintT(<<"ClientRcvChDone", self, leader0'[self], reqIdx[self], resp'[self]>>)
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                       ELSE /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3608, column 15.")
                                            /\ Assert(((resp'[self]).msource) = (leader0[self]), 
                                                      "Failure of assertion at line 3609, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3614, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3618, column 19.")
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
                                 becomeLeaderCh, allReqs, reqCh, 
                                 requestVoteSrvId, appendEntriesSrvId, 
                                 advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                 crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                 idx1, srvId1, newCommitIndex, srvId2, srvId3, 
                                 req, reqIdx, timeout, srvId4 >>

client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

serverCrash(self) == /\ pc[self] = "serverCrash"
                     /\ LET value130 == FALSE IN
                          /\ network' = [network EXCEPT ![srvId4[self]] = [queue |-> ((network)[srvId4[self]]).queue, enabled |-> value130]]
                          /\ pc' = [pc EXCEPT ![self] = "fdUpdate"]
                     /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                     nextIndex, matchIndex, log, plog, 
                                     votedFor, votesResponded, votesGranted, 
                                     leader, sm, smDomain, leaderTimeout, 
                                     appendEntriesCh, becomeLeaderCh, allReqs, 
                                     reqCh, respCh, requestVoteSrvId, 
                                     appendEntriesSrvId, 
                                     advanceCommitIndexSrvId, 
                                     becomeLeaderSrvId, crasherSrvId, idx, m, 
                                     srvId, idx0, srvId0, idx1, srvId1, 
                                     newCommitIndex, srvId2, srvId3, leader0, 
                                     req, resp, reqIdx, timeout, srvId4 >>

fdUpdate(self) == /\ pc[self] = "fdUpdate"
                  /\ LET value140 == TRUE IN
                       /\ fd' = [fd EXCEPT ![srvId4[self]] = value140]
                       /\ pc' = [pc EXCEPT ![self] = "block"]
                  /\ UNCHANGED << network, state, currentTerm, commitIndex, 
                                  nextIndex, matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, sm, 
                                  smDomain, leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, allReqs, reqCh, respCh, 
                                  requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                  idx1, srvId1, newCommitIndex, srvId2, srvId3, 
                                  leader0, req, resp, reqIdx, timeout, srvId4 >>

block(self) == /\ pc[self] = "block"
               /\ FALSE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                               nextIndex, matchIndex, log, plog, votedFor, 
                               votesResponded, votesGranted, leader, sm, 
                               smDomain, leaderTimeout, appendEntriesCh, 
                               becomeLeaderCh, allReqs, reqCh, respCh, 
                               requestVoteSrvId, appendEntriesSrvId, 
                               advanceCommitIndexSrvId, becomeLeaderSrvId, 
                               crasherSrvId, idx, m, srvId, idx0, srvId0, idx1, 
                               srvId1, newCommitIndex, srvId2, srvId3, leader0, 
                               req, resp, reqIdx, timeout, srvId4 >>

crasher(self) == serverCrash(self) \/ fdUpdate(self) \/ block(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: s0(self))
           \/ (\E self \in ServerRequestVoteSet: s1(self))
           \/ (\E self \in ServerAppendEntriesSet: s2(self))
           \/ (\E self \in ServerAdvanceCommitIndexSet: s3(self))
           \/ (\E self \in ServerBecomeLeaderSet: s4(self))
           \/ (\E self \in ClientSet: client(self))
           \/ (\E self \in ServerCrasherSet: crasher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(s0(self))
        /\ \A self \in ServerRequestVoteSet : WF_vars(s1(self))
        /\ \A self \in ServerAppendEntriesSet : WF_vars(s2(self))
        /\ \A self \in ServerAdvanceCommitIndexSet : WF_vars(s3(self))
        /\ \A self \in ServerBecomeLeaderSet : WF_vars(s4(self))
        /\ \A self \in ClientSet : WF_vars(client(self))
        /\ \A self \in ServerCrasherSet : WF_vars(crasher(self))

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
                        /\ sm[i] = sm[j]
                        /\ smDomain[i] = smDomain[j]

plogOK == \A i \in ServerSet: log[i] = plog[i]

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
