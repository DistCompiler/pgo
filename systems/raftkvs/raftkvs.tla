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

        Nil == 0

        ServerRequestVoteSet        == (1*NumServers+1)..(2*NumServers)
        ServerAppendEntriesSet      == (2*NumServers+1)..(3*NumServers)
        ServerAdvanceCommitIndexSet == (3*NumServers+1)..(4*NumServers)
        ServerBecomeLeaderSet       == (4*NumServers+1)..(5*NumServers)

        ClientSet == (5*NumServers+1)..(2*NumServers+NumClients)
        NodeSet   == ServerSet \cup ServerAppendEntriesSet \cup ClientSet

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
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout, ref appendEntriesCh
    )
    variables
        idx = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            m := net[self];
            assert m.mdest = self;

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
                    goto serverLoop;
                } else {
                    \* HandleRequestVoteResponse
                    with (i = self, j = m.msource) {
                        assert m.mterm = currentTerm[i];
                        votesResponded[i] := votesResponded[i] \cup {j};
                        if (m.mvoteGranted) {
                            votesGranted[i] := votesGranted[i] \cup {j};
                        }; 
                    };
                };
            } else if (m.mtype = AppendEntriesRequest) {
                UpdateTerm(self, m, currentTerm, state, votedFor, leader);

                leader[self] := m.msource;

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
                                with (result = ApplyLog(log[i], commitIndex[i]+1, m.mcommitIndex,
                                      sm[i], smDomain[i])) {
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
                    goto serverLoop;
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
                \* ClientRequest
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
                            mresponse   |-> Nil,
                            mleaderHint |-> leader[i],
                            msource     |-> i,
                            mdest       |-> j
                        ];
                    };
                };
            };
        };

    failLabel:
        fd[self] := TRUE;
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
        ref leaderTimeout, ref appendEntriesCh
    )
    variable idx = 1;
    {
    serverRequestVoteLoop:
        while (TRUE) {

            \* Server times out and starts a new election.
            await state[srvId] \in {Follower, Candidate};
            await (
                /\ netLen[srvId] = 0
                /\ leaderTimeout
            );

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
        ref leaderTimeout, ref appendEntriesCh
    )
    variable idx;
    {
    serverAppendEntriesLoop:
        while (appendEntriesCh) {
            await state[srvId] = Leader;
            idx := 1;

        appendEntriesLoop:
            \* AppendEntries
            while (
                /\ netEnabled[srvId]
                /\ state[srvId] = Leader
                /\ idx <= NumServers
            ) {
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
        ref leaderTimeout, ref appendEntriesCh
    )
    variable newCommitIndex = 0,
    {
    serverAdvanceCommitIndexLoop:
        while (TRUE) {
            await state[srvId] = Leader;

            \* AdvanceCommitIndex
            with (
                i = srvId,

                \* gives a much smaller set than above, proportional to disagreement not log size
                agreeIndexes = FindAgreeIndices(log[i], i, matchIndex[i]),

                nCommitIndex =
                    IF /\ agreeIndexes /= {}
                        /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
                    THEN Max(agreeIndexes)
                    ELSE commitIndex[i]
            ) {
                newCommitIndex := nCommitIndex;
                assert newCommitIndex >= commitIndex[i];
            };

        applyLoop:
            while (commitIndex[srvId] < newCommitIndex) {
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
        ref leaderTimeout, ref appendEntriesCh
    )
    {
    serverBecomeLeaderLoop:
        while (TRUE) {
            \* BecomeLeader
            await (
                /\ state[srvId] = Candidate
                /\ isQuorum(votesGranted[srvId])
            );
            with (i = srvId) {
                state[i]      := Leader;
                nextIndex[i]  := [j \in ServerSet |-> Len(log[i]) + 1];
                matchIndex[i] := [j \in ServerSet |-> 0];
                leader[i]     := i;

                appendEntriesCh := TRUE;
                debug(<<"BecomeLeader", i, currentTerm[i]>>);
            };
        };
    }

    archetype AClient(ref net[_], ref netLen[_], ref fd[_], ref reqCh, ref respCh, ref timeout)
    variables leader = Nil, req, resp, reqIdx = 0;
    {
    clientLoop:
        while (TRUE) {
            either {
                req := reqCh;
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
            debug(<<"ClientSndReq", self, leader, req>>);
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
                debug(<<"ClientRcvResp", resp>>);
                assert resp.mdest = self;

                \* it should be /very likely/ that indexed requests will help us
                \* throw out duplicate server responses.
                \* one edge case I can think of: start, do one req, immediately
                \* stop + restart, immediately get stale response to last req.
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
                        respCh := resp;
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

        state       = [i \in ServerSet |-> Follower];
        currentTerm = [i \in ServerSet |-> 1];

        commitIndex = [i \in ServerSet |-> 0];
        nextIndex   = [i \in ServerSet |-> [j \in ServerSet |-> 1]];
        matchIndex  = [i \in ServerSet |-> [j \in ServerSet |-> 0]];

        log         = [i \in ServerSet |-> <<>>];
        plog        = [i \in ServerSet |-> <<>>];

        votedFor = [i \in ServerSet |-> Nil];
        votesResponded = [i \in ServerSet |-> {}];
        votesGranted   = [i \in ServerSet |-> {}];

        leader = [i \in ServerSet |-> Nil];

        sm       = [i \in ServerSet |-> [k \in KeySet |-> Nil]];
        smDomain = [i \in ServerSet |-> KeySet];

        leaderTimeout   = TRUE;
        appendEntriesCh = TRUE;

        reqCh  = <<
            [type |-> Put, key |-> Key1, value |-> Value1]
            \* [type |-> Get, key |-> Key2]
            \* [type |-> Get, key |-> Key1]
        >>;
        respCh;

        requestVoteSrvId        = [i \in ServerRequestVoteSet        |-> i - 1*NumServers];
        appendEntriesSrvId      = [i \in ServerAppendEntriesSet      |-> i - 2*NumServers];
        advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> i - 3*NumServers];
        becomeLeaderSrvId       = [i \in ServerBecomeLeaderSet       |-> i - 4*NumServers];

    fair process (s0 \in ServerSet) == instance AServer(
        s0,
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout, ref appendEntriesCh
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog;

    fair process (s1 \in ServerRequestVoteSet) == instance AServerRequestVote(
        requestVoteSrvId[s1],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref sm[_], ref smDomain[_],
        ref leaderTimeout, ref appendEntriesCh
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
        ref leaderTimeout, ref appendEntriesCh
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
        ref leaderTimeout, ref appendEntriesCh
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
        ref leaderTimeout, ref appendEntriesCh
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via NetworkBufferLength
        mapping @4[_] via NetworkToggle
        mapping @5[_] via PerfectFD
        mapping @9[_] via PersistentLog;

    fair process (client \in ClientSet) == instance AClient(
        ref network[_], ref network[_], ref fd[_],
        ref reqCh, ref respCh, FALSE
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via NetworkBufferLength
        mapping @3[_] via PerfectFD
        mapping @4    via InputChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raftkvs {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; state = [i \in ServerSet |-> Follower]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]; log = [i \in ServerSet |-> <<>>]; plog = [i \in ServerSet |-> <<>>]; votedFor = [i \in ServerSet |-> Nil]; votesResponded = [i \in ServerSet |-> {}]; votesGranted = [i \in ServerSet |-> {}]; leader = [i \in ServerSet |-> Nil]; sm = [i \in ServerSet |-> [k \in KeySet |-> Nil]]; smDomain = [i \in ServerSet |-> KeySet]; leaderTimeout = TRUE; appendEntriesCh = TRUE; reqCh = <<[type |-> Put, key |-> Key1, value |-> Value1]>>; respCh; requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]; appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]; advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]; becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))];
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
    ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
    ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
    ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
    ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
    ClientSet == (((5) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
    NodeSet == ((ServerSet) \union (ServerAppendEntriesSet)) \union (ClientSet)
    KeySet == {}
  }
  
  fair process (s0 \in ServerSet)
    variables idx = 1; m; srvId = self;
  {
    serverLoop:
      if (TRUE) {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (
          readMsg00 = Head(((network)[self]).queue), 
          network0 = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]], 
          yielded_network5 = readMsg00
        ) {
          m := yielded_network5;
          assert ((m).mdest) = (self);
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
                        await ((network0)[j]).enabled;
                        await (Len(((network0)[j]).queue)) < (BufferSize);
                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value00), enabled |-> ((network0)[j]).enabled]];
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
                          network := network0;
                          goto serverLoop;
                        } else {
                          network := network0;
                          goto serverLoop;
                        };
                      };
                    };
                  } else {
                    either {
                      with (value01 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                        await ((network0)[j]).enabled;
                        await (Len(((network0)[j]).queue)) < (BufferSize);
                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value01), enabled |-> ((network0)[j]).enabled]];
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
                          network := network0;
                          goto serverLoop;
                        } else {
                          votedFor := votedFor1;
                          network := network0;
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
                      await ((network0)[j]).enabled;
                      await (Len(((network0)[j]).queue)) < (BufferSize);
                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value02), enabled |-> ((network0)[j]).enabled]];
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
                        network := network0;
                        goto serverLoop;
                      } else {
                        network := network0;
                        goto serverLoop;
                      };
                    };
                  };
                } else {
                  either {
                    with (value03 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                      await ((network0)[j]).enabled;
                      await (Len(((network0)[j]).queue)) < (BufferSize);
                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value03), enabled |-> ((network0)[j]).enabled]];
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
                        network := network0;
                        goto serverLoop;
                      } else {
                        network := network0;
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
                  network := network0;
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
                      network := network0;
                      goto serverLoop;
                    } else {
                      network := network0;
                      goto serverLoop;
                    };
                  };
                };
              } else {
                if (((m).mterm) < ((currentTerm)[self])) {
                  network := network0;
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
                      network := network0;
                      goto serverLoop;
                    } else {
                      network := network0;
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
                              with (value13 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                                await ((network0)[j]).enabled;
                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value13), enabled |-> ((network0)[j]).enabled]];
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd00 = (fd)[j]) {
                                await yielded_fd00;
                                network := network0;
                                goto serverLoop;
                              };
                            };
                          } else {
                            assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                            with (index = ((m).mprevLogIndex) + (1)) {
                              if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                                with (
                                  log4 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                                  value20 = [cmd |-> LogPop]
                                ) {
                                  if (((value20).cmd) = (LogConcat)) {
                                    with (plog4 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value20).entries)]) {
                                      if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                        log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                        with (value30 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                          if (((value30).cmd) = (LogConcat)) {
                                            plog := [plog4 EXCEPT ![i] = ((plog4)[i]) \o ((value30).entries)];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result16 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result16)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result16)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value40 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value40), enabled |-> ((network0)[j]).enabled]];
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd11 = (fd)[j]) {
                                                    await yielded_fd11;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if (((value30).cmd) = (LogPop)) {
                                              plog := [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result17 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result17)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result17)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value41 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value41), enabled |-> ((network0)[j]).enabled]];
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd12 = (fd)[j]) {
                                                      await yielded_fd12;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result18 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result18)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result18)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value42 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value42), enabled |-> ((network0)[j]).enabled]];
                                                      plog := plog4;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd13 = (fd)[j]) {
                                                      await yielded_fd13;
                                                      plog := plog4;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                plog := plog4;
                                                network := network0;
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
                                              with (value43 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value43), enabled |-> ((network0)[j]).enabled]];
                                                plog := plog4;
                                                log := log4;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd14 = (fd)[j]) {
                                                await yielded_fd14;
                                                plog := plog4;
                                                log := log4;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog4;
                                          log := log4;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    if (((value20).cmd) = (LogPop)) {
                                      with (plog5 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                        if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                          log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                          with (value31 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                            if (((value31).cmd) = (LogConcat)) {
                                              plog := [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value31).entries)];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result20 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result20)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result20)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value44 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value44), enabled |-> ((network0)[j]).enabled]];
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd15 = (fd)[j]) {
                                                      await yielded_fd15;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if (((value31).cmd) = (LogPop)) {
                                                plog := [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))];
                                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                  with (result21 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                    sm := [sm EXCEPT ![i] = (result21)[1]];
                                                    smDomain := [smDomain EXCEPT ![i] = (result21)[2]];
                                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                    either {
                                                      with (value45 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                        await ((network0)[j]).enabled;
                                                        await (Len(((network0)[j]).queue)) < (BufferSize);
                                                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value45), enabled |-> ((network0)[j]).enabled]];
                                                        goto serverLoop;
                                                      };
                                                    } or {
                                                      with (yielded_fd16 = (fd)[j]) {
                                                        await yielded_fd16;
                                                        network := network0;
                                                        goto serverLoop;
                                                      };
                                                    };
                                                  };
                                                } else {
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              } else {
                                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                  with (result22 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                    sm := [sm EXCEPT ![i] = (result22)[1]];
                                                    smDomain := [smDomain EXCEPT ![i] = (result22)[2]];
                                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                    either {
                                                      with (value46 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                        await ((network0)[j]).enabled;
                                                        await (Len(((network0)[j]).queue)) < (BufferSize);
                                                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value46), enabled |-> ((network0)[j]).enabled]];
                                                        plog := plog5;
                                                        goto serverLoop;
                                                      };
                                                    } or {
                                                      with (yielded_fd17 = (fd)[j]) {
                                                        await yielded_fd17;
                                                        plog := plog5;
                                                        network := network0;
                                                        goto serverLoop;
                                                      };
                                                    };
                                                  };
                                                } else {
                                                  plog := plog5;
                                                  network := network0;
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
                                                with (value47 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value47), enabled |-> ((network0)[j]).enabled]];
                                                  plog := plog5;
                                                  log := log4;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd18 = (fd)[j]) {
                                                  await yielded_fd18;
                                                  plog := plog5;
                                                  log := log4;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog5;
                                            log := log4;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                        log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                        with (value32 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                          if (((value32).cmd) = (LogConcat)) {
                                            plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result24 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result24)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result24)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value48 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value48), enabled |-> ((network0)[j]).enabled]];
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd19 = (fd)[j]) {
                                                    await yielded_fd19;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if (((value32).cmd) = (LogPop)) {
                                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result25 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result25)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result25)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value49 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value49), enabled |-> ((network0)[j]).enabled]];
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd110 = (fd)[j]) {
                                                      await yielded_fd110;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result26 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result26)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result26)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value410 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value410), enabled |-> ((network0)[j]).enabled]];
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd111 = (fd)[j]) {
                                                      await yielded_fd111;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                network := network0;
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
                                              with (value411 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value411), enabled |-> ((network0)[j]).enabled]];
                                                log := log4;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd112 = (fd)[j]) {
                                                await yielded_fd112;
                                                log := log4;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          log := log4;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                                  log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                                  with (value33 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value33).cmd) = (LogConcat)) {
                                      plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result28 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result28)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result28)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value412 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network0)[j]).enabled;
                                              await (Len(((network0)[j]).queue)) < (BufferSize);
                                              network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value412), enabled |-> ((network0)[j]).enabled]];
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd113 = (fd)[j]) {
                                              await yielded_fd113;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        network := network0;
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value33).cmd) = (LogPop)) {
                                        plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result29 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result29)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result29)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value413 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value413), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd114 = (fd)[j]) {
                                                await yielded_fd114;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result30 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result30)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result30)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value414 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value414), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd115 = (fd)[j]) {
                                                await yielded_fd115;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
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
                                        with (value415 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network0)[j]).enabled;
                                          await (Len(((network0)[j]).queue)) < (BufferSize);
                                          network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value415), enabled |-> ((network0)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd116 = (fd)[j]) {
                                          await yielded_fd116;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    network := network0;
                                    goto serverLoop;
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                            either {
                              with (value14 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                                await ((network0)[j]).enabled;
                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value14), enabled |-> ((network0)[j]).enabled]];
                                state := state1;
                                goto serverLoop;
                              };
                            } or {
                              with (yielded_fd01 = (fd)[j]) {
                                await yielded_fd01;
                                state := state1;
                                network := network0;
                                goto serverLoop;
                              };
                            };
                          } else {
                            assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK);
                            with (index = ((m).mprevLogIndex) + (1)) {
                              if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                                with (
                                  log5 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                                  value21 = [cmd |-> LogPop]
                                ) {
                                  if (((value21).cmd) = (LogConcat)) {
                                    with (plog6 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value21).entries)]) {
                                      if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                        log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                        with (value34 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                          if (((value34).cmd) = (LogConcat)) {
                                            plog := [plog6 EXCEPT ![i] = ((plog6)[i]) \o ((value34).entries)];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result32 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result32)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result32)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value416 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value416), enabled |-> ((network0)[j]).enabled]];
                                                    state := state1;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd117 = (fd)[j]) {
                                                    await yielded_fd117;
                                                    state := state1;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              state := state1;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if (((value34).cmd) = (LogPop)) {
                                              plog := [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result33 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result33)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result33)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value417 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value417), enabled |-> ((network0)[j]).enabled]];
                                                      state := state1;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd118 = (fd)[j]) {
                                                      await yielded_fd118;
                                                      state := state1;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result34 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result34)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result34)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value418 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value418), enabled |-> ((network0)[j]).enabled]];
                                                      plog := plog6;
                                                      state := state1;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd119 = (fd)[j]) {
                                                      await yielded_fd119;
                                                      plog := plog6;
                                                      state := state1;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                plog := plog6;
                                                state := state1;
                                                network := network0;
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
                                              with (value419 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value419), enabled |-> ((network0)[j]).enabled]];
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
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          plog := plog6;
                                          log := log5;
                                          state := state1;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    if (((value21).cmd) = (LogPop)) {
                                      with (plog7 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                        if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                          log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                          with (value35 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                            if (((value35).cmd) = (LogConcat)) {
                                              plog := [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value35).entries)];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result36 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result36)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result36)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value420 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value420), enabled |-> ((network0)[j]).enabled]];
                                                      state := state1;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd121 = (fd)[j]) {
                                                      await yielded_fd121;
                                                      state := state1;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if (((value35).cmd) = (LogPop)) {
                                                plog := [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))];
                                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                  with (result37 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                    sm := [sm EXCEPT ![i] = (result37)[1]];
                                                    smDomain := [smDomain EXCEPT ![i] = (result37)[2]];
                                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                    either {
                                                      with (value421 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                        await ((network0)[j]).enabled;
                                                        await (Len(((network0)[j]).queue)) < (BufferSize);
                                                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value421), enabled |-> ((network0)[j]).enabled]];
                                                        state := state1;
                                                        goto serverLoop;
                                                      };
                                                    } or {
                                                      with (yielded_fd122 = (fd)[j]) {
                                                        await yielded_fd122;
                                                        state := state1;
                                                        network := network0;
                                                        goto serverLoop;
                                                      };
                                                    };
                                                  };
                                                } else {
                                                  state := state1;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              } else {
                                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                  with (result38 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                    sm := [sm EXCEPT ![i] = (result38)[1]];
                                                    smDomain := [smDomain EXCEPT ![i] = (result38)[2]];
                                                    commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                    either {
                                                      with (value422 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                        await ((network0)[j]).enabled;
                                                        await (Len(((network0)[j]).queue)) < (BufferSize);
                                                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value422), enabled |-> ((network0)[j]).enabled]];
                                                        plog := plog7;
                                                        state := state1;
                                                        goto serverLoop;
                                                      };
                                                    } or {
                                                      with (yielded_fd123 = (fd)[j]) {
                                                        await yielded_fd123;
                                                        plog := plog7;
                                                        state := state1;
                                                        network := network0;
                                                        goto serverLoop;
                                                      };
                                                    };
                                                  };
                                                } else {
                                                  plog := plog7;
                                                  state := state1;
                                                  network := network0;
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
                                                with (value423 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value423), enabled |-> ((network0)[j]).enabled]];
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
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog7;
                                            log := log5;
                                            state := state1;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                        log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                        with (value36 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                          if (((value36).cmd) = (LogConcat)) {
                                            plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value36).entries)];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result40 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result40)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result40)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value424 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value424), enabled |-> ((network0)[j]).enabled]];
                                                    state := state1;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd125 = (fd)[j]) {
                                                    await yielded_fd125;
                                                    state := state1;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              state := state1;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if (((value36).cmd) = (LogPop)) {
                                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result41 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result41)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result41)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value425 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value425), enabled |-> ((network0)[j]).enabled]];
                                                      state := state1;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd126 = (fd)[j]) {
                                                      await yielded_fd126;
                                                      state := state1;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            } else {
                                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                                with (result42 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                  sm := [sm EXCEPT ![i] = (result42)[1]];
                                                  smDomain := [smDomain EXCEPT ![i] = (result42)[2]];
                                                  commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                  either {
                                                    with (value426 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                      await ((network0)[j]).enabled;
                                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value426), enabled |-> ((network0)[j]).enabled]];
                                                      state := state1;
                                                      goto serverLoop;
                                                    };
                                                  } or {
                                                    with (yielded_fd127 = (fd)[j]) {
                                                      await yielded_fd127;
                                                      state := state1;
                                                      network := network0;
                                                      goto serverLoop;
                                                    };
                                                  };
                                                };
                                              } else {
                                                state := state1;
                                                network := network0;
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
                                              with (value427 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value427), enabled |-> ((network0)[j]).enabled]];
                                                log := log5;
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd128 = (fd)[j]) {
                                                await yielded_fd128;
                                                log := log5;
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          log := log5;
                                          state := state1;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                                  log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                                  with (value37 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value37).cmd) = (LogConcat)) {
                                      plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value37).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (result44 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                          sm := [sm EXCEPT ![i] = (result44)[1]];
                                          smDomain := [smDomain EXCEPT ![i] = (result44)[2]];
                                          commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                          either {
                                            with (value428 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network0)[j]).enabled;
                                              await (Len(((network0)[j]).queue)) < (BufferSize);
                                              network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value428), enabled |-> ((network0)[j]).enabled]];
                                              state := state1;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd129 = (fd)[j]) {
                                              await yielded_fd129;
                                              state := state1;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        state := state1;
                                        network := network0;
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value37).cmd) = (LogPop)) {
                                        plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result45 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result45)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result45)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value429 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value429), enabled |-> ((network0)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd130 = (fd)[j]) {
                                                await yielded_fd130;
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result46 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result46)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result46)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value430 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value430), enabled |-> ((network0)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd131 = (fd)[j]) {
                                                await yielded_fd131;
                                                state := state1;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          state := state1;
                                          network := network0;
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
                                        with (value431 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network0)[j]).enabled;
                                          await (Len(((network0)[j]).queue)) < (BufferSize);
                                          network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value431), enabled |-> ((network0)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd132 = (fd)[j]) {
                                          await yielded_fd132;
                                          state := state1;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    state := state1;
                                    network := network0;
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
                          with (value15 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network0)[j]).enabled;
                            await (Len(((network0)[j]).queue)) < (BufferSize);
                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value15), enabled |-> ((network0)[j]).enabled]];
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd02 = (fd)[j]) {
                            await yielded_fd02;
                            network := network0;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                        with (index = ((m).mprevLogIndex) + (1)) {
                          if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                            with (
                              log6 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                              value22 = [cmd |-> LogPop]
                            ) {
                              if (((value22).cmd) = (LogConcat)) {
                                with (plog8 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value22).entries)]) {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                    log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                    with (value38 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value38).cmd) = (LogConcat)) {
                                        plog := [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value38).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result48 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result48)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result48)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value432 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value432), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd133 = (fd)[j]) {
                                                await yielded_fd133;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value38).cmd) = (LogPop)) {
                                          plog := [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result49 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result49)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result49)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value433 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value433), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd134 = (fd)[j]) {
                                                  await yielded_fd134;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result50 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result50)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result50)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value434 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value434), enabled |-> ((network0)[j]).enabled]];
                                                  plog := plog8;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd135 = (fd)[j]) {
                                                  await yielded_fd135;
                                                  plog := plog8;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog8;
                                            network := network0;
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
                                          with (value435 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value435), enabled |-> ((network0)[j]).enabled]];
                                            plog := plog8;
                                            log := log6;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd136 = (fd)[j]) {
                                            await yielded_fd136;
                                            plog := plog8;
                                            log := log6;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      plog := plog8;
                                      log := log6;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value22).cmd) = (LogPop)) {
                                  with (plog9 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                    if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                      log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                      with (value39 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                        if (((value39).cmd) = (LogConcat)) {
                                          plog := [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value39).entries)];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result52 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result52)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result52)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value436 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value436), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd137 = (fd)[j]) {
                                                  await yielded_fd137;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if (((value39).cmd) = (LogPop)) {
                                            plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result53 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result53)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result53)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value437 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value437), enabled |-> ((network0)[j]).enabled]];
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd138 = (fd)[j]) {
                                                    await yielded_fd138;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result54 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result54)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result54)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value438 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value438), enabled |-> ((network0)[j]).enabled]];
                                                    plog := plog9;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd139 = (fd)[j]) {
                                                    await yielded_fd139;
                                                    plog := plog9;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              plog := plog9;
                                              network := network0;
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
                                            with (value439 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network0)[j]).enabled;
                                              await (Len(((network0)[j]).queue)) < (BufferSize);
                                              network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value439), enabled |-> ((network0)[j]).enabled]];
                                              plog := plog9;
                                              log := log6;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd140 = (fd)[j]) {
                                              await yielded_fd140;
                                              plog := plog9;
                                              log := log6;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        plog := plog9;
                                        log := log6;
                                        network := network0;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                    log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                    with (value310 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value310).cmd) = (LogConcat)) {
                                        plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value310).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result56 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result56)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result56)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value440 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value440), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd141 = (fd)[j]) {
                                                await yielded_fd141;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value310).cmd) = (LogPop)) {
                                          plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result57 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result57)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result57)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value441 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value441), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd142 = (fd)[j]) {
                                                  await yielded_fd142;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result58 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result58)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result58)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value442 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value442), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd143 = (fd)[j]) {
                                                  await yielded_fd143;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
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
                                          with (value443 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value443), enabled |-> ((network0)[j]).enabled]];
                                            log := log6;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd144 = (fd)[j]) {
                                            await yielded_fd144;
                                            log := log6;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      log := log6;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                              log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                              with (value311 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                if (((value311).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result60 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result60)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result60)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                      either {
                                        with (value444 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network0)[j]).enabled;
                                          await (Len(((network0)[j]).queue)) < (BufferSize);
                                          network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value444), enabled |-> ((network0)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd145 = (fd)[j]) {
                                          await yielded_fd145;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    network := network0;
                                    goto serverLoop;
                                  };
                                } else {
                                  if (((value311).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result61 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result61)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result61)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value445 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value445), enabled |-> ((network0)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd146 = (fd)[j]) {
                                            await yielded_fd146;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result62 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result62)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result62)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value446 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value446), enabled |-> ((network0)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd147 = (fd)[j]) {
                                            await yielded_fd147;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      network := network0;
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
                                    with (value447 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network0)[j]).enabled;
                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value447), enabled |-> ((network0)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd148 = (fd)[j]) {
                                      await yielded_fd148;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                network := network0;
                                goto serverLoop;
                              };
                            };
                          };
                        };
                      };
                    } else {
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value16 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network0)[j]).enabled;
                            await (Len(((network0)[j]).queue)) < (BufferSize);
                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value16), enabled |-> ((network0)[j]).enabled]];
                            goto serverLoop;
                          };
                        } or {
                          with (yielded_fd03 = (fd)[j]) {
                            await yielded_fd03;
                            network := network0;
                            goto serverLoop;
                          };
                        };
                      } else {
                        assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                        with (index = ((m).mprevLogIndex) + (1)) {
                          if (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m).mentries)[1]).term))) {
                            with (
                              log7 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))], 
                              value23 = [cmd |-> LogPop]
                            ) {
                              if (((value23).cmd) = (LogConcat)) {
                                with (plog10 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value23).entries)]) {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                    log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                    with (value312 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value312).cmd) = (LogConcat)) {
                                        plog := [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value312).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result64 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result64)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result64)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value448 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value448), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd149 = (fd)[j]) {
                                                await yielded_fd149;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value312).cmd) = (LogPop)) {
                                          plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result65 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result65)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result65)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value449 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value449), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd150 = (fd)[j]) {
                                                  await yielded_fd150;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result66 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result66)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result66)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value450 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value450), enabled |-> ((network0)[j]).enabled]];
                                                  plog := plog10;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd151 = (fd)[j]) {
                                                  await yielded_fd151;
                                                  plog := plog10;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            plog := plog10;
                                            network := network0;
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
                                          with (value451 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value451), enabled |-> ((network0)[j]).enabled]];
                                            plog := plog10;
                                            log := log7;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd152 = (fd)[j]) {
                                            await yielded_fd152;
                                            plog := plog10;
                                            log := log7;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      plog := plog10;
                                      log := log7;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value23).cmd) = (LogPop)) {
                                  with (plog11 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                    if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                      log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                      with (value313 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                        if (((value313).cmd) = (LogConcat)) {
                                          plog := [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value313).entries)];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result68 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result68)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result68)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value452 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value452), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd153 = (fd)[j]) {
                                                  await yielded_fd153;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if (((value313).cmd) = (LogPop)) {
                                            plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result69 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result69)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result69)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value453 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value453), enabled |-> ((network0)[j]).enabled]];
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd154 = (fd)[j]) {
                                                    await yielded_fd154;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          } else {
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (result70 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                                sm := [sm EXCEPT ![i] = (result70)[1]];
                                                smDomain := [smDomain EXCEPT ![i] = (result70)[2]];
                                                commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                                either {
                                                  with (value454 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network0)[j]).enabled;
                                                    await (Len(((network0)[j]).queue)) < (BufferSize);
                                                    network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value454), enabled |-> ((network0)[j]).enabled]];
                                                    plog := plog11;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd155 = (fd)[j]) {
                                                    await yielded_fd155;
                                                    plog := plog11;
                                                    network := network0;
                                                    goto serverLoop;
                                                  };
                                                };
                                              };
                                            } else {
                                              plog := plog11;
                                              network := network0;
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
                                            with (value455 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network0)[j]).enabled;
                                              await (Len(((network0)[j]).queue)) < (BufferSize);
                                              network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value455), enabled |-> ((network0)[j]).enabled]];
                                              plog := plog11;
                                              log := log7;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd156 = (fd)[j]) {
                                              await yielded_fd156;
                                              plog := plog11;
                                              log := log7;
                                              network := network0;
                                              goto serverLoop;
                                            };
                                          };
                                        };
                                      } else {
                                        plog := plog11;
                                        log := log7;
                                        network := network0;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                    log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                    with (value314 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value314).cmd) = (LogConcat)) {
                                        plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (result72 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                            sm := [sm EXCEPT ![i] = (result72)[1]];
                                            smDomain := [smDomain EXCEPT ![i] = (result72)[2]];
                                            commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                            either {
                                              with (value456 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network0)[j]).enabled;
                                                await (Len(((network0)[j]).queue)) < (BufferSize);
                                                network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value456), enabled |-> ((network0)[j]).enabled]];
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd157 = (fd)[j]) {
                                                await yielded_fd157;
                                                network := network0;
                                                goto serverLoop;
                                              };
                                            };
                                          };
                                        } else {
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value314).cmd) = (LogPop)) {
                                          plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result73 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result73)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result73)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value457 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value457), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd158 = (fd)[j]) {
                                                  await yielded_fd158;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (result74 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                              sm := [sm EXCEPT ![i] = (result74)[1]];
                                              smDomain := [smDomain EXCEPT ![i] = (result74)[2]];
                                              commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                              either {
                                                with (value458 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network0)[j]).enabled;
                                                  await (Len(((network0)[j]).queue)) < (BufferSize);
                                                  network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value458), enabled |-> ((network0)[j]).enabled]];
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd159 = (fd)[j]) {
                                                  await yielded_fd159;
                                                  network := network0;
                                                  goto serverLoop;
                                                };
                                              };
                                            };
                                          } else {
                                            network := network0;
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
                                          with (value459 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value459), enabled |-> ((network0)[j]).enabled]];
                                            log := log7;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd160 = (fd)[j]) {
                                            await yielded_fd160;
                                            log := log7;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      log := log7;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if ((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m).mprevLogIndex))) {
                              log := [log EXCEPT ![i] = ((log)[i]) \o ((m).mentries)];
                              with (value315 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                if (((value315).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value315).entries)];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (result76 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                      sm := [sm EXCEPT ![i] = (result76)[1]];
                                      smDomain := [smDomain EXCEPT ![i] = (result76)[2]];
                                      commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                      either {
                                        with (value460 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network0)[j]).enabled;
                                          await (Len(((network0)[j]).queue)) < (BufferSize);
                                          network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value460), enabled |-> ((network0)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd161 = (fd)[j]) {
                                          await yielded_fd161;
                                          network := network0;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    network := network0;
                                    goto serverLoop;
                                  };
                                } else {
                                  if (((value315).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result77 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result77)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result77)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value461 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value461), enabled |-> ((network0)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd162 = (fd)[j]) {
                                            await yielded_fd162;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (result78 = ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m).mcommitIndex, (sm)[i], (smDomain)[i])) {
                                        sm := [sm EXCEPT ![i] = (result78)[1]];
                                        smDomain := [smDomain EXCEPT ![i] = (result78)[2]];
                                        commitIndex := [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m).mcommitIndex})];
                                        either {
                                          with (value462 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network0)[j]).enabled;
                                            await (Len(((network0)[j]).queue)) < (BufferSize);
                                            network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value462), enabled |-> ((network0)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd163 = (fd)[j]) {
                                            await yielded_fd163;
                                            network := network0;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      network := network0;
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
                                    with (value463 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network0)[j]).enabled;
                                      await (Len(((network0)[j]).queue)) < (BufferSize);
                                      network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value463), enabled |-> ((network0)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd164 = (fd)[j]) {
                                      await yielded_fd164;
                                      network := network0;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                network := network0;
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
                      network := network0;
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
                          network := network0;
                          goto serverLoop;
                        } else {
                          nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                          network := network0;
                          goto serverLoop;
                        };
                      };
                    };
                  } else {
                    if (((m).mterm) < ((currentTerm)[self])) {
                      network := network0;
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
                          network := network0;
                          goto serverLoop;
                        } else {
                          nextIndex := [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]];
                          network := network0;
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
                        with (value50 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                          if (((value50).cmd) = (LogConcat)) {
                            plog := [plog EXCEPT ![self] = ((plog)[self]) \o ((value50).entries)];
                            network := network0;
                            goto serverLoop;
                          } else {
                            if (((value50).cmd) = (LogPop)) {
                              plog := [plog EXCEPT ![self] = SubSeq((plog)[self], 1, (Len((plog)[self])) - (1))];
                              network := network0;
                              goto serverLoop;
                            } else {
                              network := network0;
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
                        value60 = [mtype |-> respType, msuccess |-> FALSE, mresponse |-> Nil, mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j]
                      ) {
                        await ((network0)[j]).enabled;
                        await (Len(((network0)[j]).queue)) < (BufferSize);
                        network := [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value60), enabled |-> ((network0)[j]).enabled]];
                        goto serverLoop;
                      };
                    };
                  } else {
                    network := network0;
                    goto serverLoop;
                  };
                };
              };
            };
          };
        };
      } else {
        goto failLabel;
      };
    failLabel:
      with (value70 = TRUE) {
        fd := [fd EXCEPT ![self] = value70];
        goto Done;
      };
  }
  
  fair process (s1 \in ServerRequestVoteSet)
    variables idx0 = 1; srvId0 = (requestVoteSrvId)[self];
  {
    serverRequestVoteLoop:
      if (TRUE) {
        await ((state)[srvId0]) \in ({Follower, Candidate});
        with (yielded_network00 = Len(((network)[srvId0]).queue)) {
          await ((yielded_network00) = (0)) /\ (leaderTimeout);
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
      with (yielded_network1 = ((network)[srvId1]).enabled) {
        if (((yielded_network1) /\ (((state)[srvId1]) = (Leader))) /\ ((idx1) <= (NumServers))) {
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
          agreeIndexes = FindAgreeIndices((log)[i], i, (matchIndex)[i]), 
          nCommitIndex = IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i]
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
      if (TRUE) {
        await (((state)[srvId3]) = (Candidate)) /\ (isQuorum((votesGranted)[srvId3]));
        with (i = srvId3) {
          state := [state EXCEPT ![i] = Leader];
          nextIndex := [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]];
          matchIndex := [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]];
          leader := [leader EXCEPT ![i] = i];
          appendEntriesCh := TRUE;
          if (Debug) {
            print <<"BecomeLeader", i, (currentTerm)[i]>>;
            goto serverBecomeLeaderLoop;
          } else {
            goto serverBecomeLeaderLoop;
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (client \in ClientSet)
    variables leader0 = Nil; req; resp; reqIdx = 0; timeout = FALSE;
  {
    clientLoop:
      if (TRUE) {
        either {
          await (Len(reqCh)) > (0);
          with (res00 = Head(reqCh)) {
            reqCh := Tail(reqCh);
            with (yielded_reqCh0 = res00) {
              req := yielded_reqCh0;
              reqIdx := (reqIdx) + (1);
              goto sndReq;
            };
          };
        } or {
          assert ((network)[self]).enabled;
          await (Len(((network)[self]).queue)) > (0);
          with (readMsg10 = Head(((network)[self]).queue)) {
            network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
            with (yielded_network20 = readMsg10) {
              resp := yielded_network20;
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
            print <<"ClientSndReq", self, leader0, req>>;
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
          print <<"ClientSndReq", self, leader0, req>>;
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
        with (readMsg20 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network30 = readMsg20) {
            resp := yielded_network30;
            if (Debug) {
              print <<"ClientRcvResp", resp>>;
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
                  respCh := resp;
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
                  respCh := resp;
                  goto clientLoop;
                };
              };
            };
          };
        };
      } or {
        with (
          yielded_fd60 = (fd)[leader0], 
          yielded_network40 = Len(((network)[self]).queue)
        ) {
          await ((yielded_fd60) /\ ((yielded_network40) = (0))) \/ (timeout);
          leader0 := Nil;
          goto sndReq;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "76e7aefa" /\ chksum(tla) = "8a4ce2d1") PCal-18049938ece8066a38eb5044080cf45c
CONSTANT defaultInitValue
VARIABLES network, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, 
          log, plog, votedFor, votesResponded, votesGranted, leader, sm, 
          smDomain, leaderTimeout, appendEntriesCh, reqCh, respCh, 
          requestVoteSrvId, appendEntriesSrvId, advanceCommitIndexSrvId, 
          becomeLeaderSrvId, pc

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
ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
ClientSet == (((5) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
NodeSet == ((ServerSet) \union (ServerAppendEntriesSet)) \union (ClientSet)
KeySet == {}

VARIABLES idx, m, srvId, idx0, srvId0, idx1, srvId1, newCommitIndex, srvId2, 
          srvId3, leader0, req, resp, reqIdx, timeout

vars == << network, fd, state, currentTerm, commitIndex, nextIndex, 
           matchIndex, log, plog, votedFor, votesResponded, votesGranted, 
           leader, sm, smDomain, leaderTimeout, appendEntriesCh, reqCh, 
           respCh, requestVoteSrvId, appendEntriesSrvId, 
           advanceCommitIndexSrvId, becomeLeaderSrvId, pc, idx, m, srvId, 
           idx0, srvId0, idx1, srvId1, newCommitIndex, srvId2, srvId3, 
           leader0, req, resp, reqIdx, timeout >>

ProcSet == (ServerSet) \cup (ServerRequestVoteSet) \cup (ServerAppendEntriesSet) \cup (ServerAdvanceCommitIndexSet) \cup (ServerBecomeLeaderSet) \cup (ClientSet)

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
        /\ reqCh = <<[type |-> Put, key |-> Key1, value |-> Value1]>>
        /\ respCh = defaultInitValue
        /\ requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]
        /\ appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]
        /\ advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]
        /\ becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]
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
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                                        [] self \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                                        [] self \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                                        [] self \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                                        [] self \in ClientSet -> "clientLoop"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ Assert(((network)[self]).enabled, 
                                         "Failure of assertion at line 922, column 9.")
                               /\ (Len(((network)[self]).queue)) > (0)
                               /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                    LET network0 == [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]] IN
                                      LET yielded_network5 == readMsg00 IN
                                        /\ m' = [m EXCEPT ![self] = yielded_network5]
                                        /\ Assert(((m'[self]).mdest) = (self), 
                                                  "Failure of assertion at line 930, column 11.")
                                        /\ IF ((m'[self]).mtype) = (RequestVoteRequest)
                                              THEN /\ IF ((m'[self]).mterm) > ((currentTerm)[self])
                                                         THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m'[self]).mterm]
                                                              /\ state' = [state EXCEPT ![self] = Follower]
                                                              /\ LET votedFor1 == [votedFor EXCEPT ![self] = Nil] IN
                                                                   /\ leader' = [leader EXCEPT ![self] = Nil]
                                                                   /\ LET i == self IN
                                                                        LET j == (m'[self]).msource IN
                                                                          LET logOK == (((m'[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m'[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m'[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                                            LET grant == ((((m'[self]).mterm) = ((currentTerm')[i])) /\ (logOK)) /\ (((votedFor1)[self]) \in ({Nil, j})) IN
                                                                              /\ Assert(((m'[self]).mterm) <= ((currentTerm')[i]), 
                                                                                        "Failure of assertion at line 943, column 19.")
                                                                              /\ IF grant
                                                                                    THEN /\ votedFor' = [votedFor1 EXCEPT ![i] = j]
                                                                                         /\ \/ /\ LET value00 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                                    /\ ((network0)[j]).enabled
                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value00), enabled |-> ((network0)[j]).enabled]]
                                                                                                    /\ IF Debug
                                                                                                          THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                            \/ /\ LET yielded_fd7 == (fd)[j] IN
                                                                                                    /\ yielded_fd7
                                                                                                    /\ IF Debug
                                                                                                          THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                                               /\ network' = network0
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          ELSE /\ network' = network0
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                    ELSE /\ \/ /\ LET value01 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                                    /\ ((network0)[j]).enabled
                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value01), enabled |-> ((network0)[j]).enabled]]
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
                                                                                                               /\ network' = network0
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          ELSE /\ votedFor' = votedFor1
                                                                                                               /\ network' = network0
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                         ELSE /\ LET i == self IN
                                                                   LET j == (m'[self]).msource IN
                                                                     LET logOK == (((m'[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m'[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m'[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                                       LET grant == ((((m'[self]).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[self]) \in ({Nil, j})) IN
                                                                         /\ Assert(((m'[self]).mterm) <= ((currentTerm)[i]), 
                                                                                   "Failure of assertion at line 1011, column 17.")
                                                                         /\ IF grant
                                                                               THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                                                                    /\ \/ /\ LET value02 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                               /\ ((network0)[j]).enabled
                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value02), enabled |-> ((network0)[j]).enabled]]
                                                                                               /\ IF Debug
                                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       \/ /\ LET yielded_fd9 == (fd)[j] IN
                                                                                               /\ yielded_fd9
                                                                                               /\ IF Debug
                                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                                          /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                     ELSE /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                               ELSE /\ \/ /\ LET value03 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                               /\ ((network0)[j]).enabled
                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value03), enabled |-> ((network0)[j]).enabled]]
                                                                                               /\ IF Debug
                                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                       \/ /\ LET yielded_fd10 == (fd)[j] IN
                                                                                               /\ yielded_fd10
                                                                                               /\ IF Debug
                                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                                          /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                     ELSE /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                    /\ UNCHANGED votedFor
                                                              /\ UNCHANGED << state, 
                                                                              currentTerm, 
                                                                              leader >>
                                                   /\ UNCHANGED << commitIndex, 
                                                                   nextIndex, 
                                                                   matchIndex, 
                                                                   log, plog, 
                                                                   votesResponded, 
                                                                   votesGranted, 
                                                                   sm, 
                                                                   smDomain >>
                                              ELSE /\ IF ((m'[self]).mtype) = (RequestVoteResponse)
                                                         THEN /\ IF ((m'[self]).mterm) > ((currentTerm)[self])
                                                                    THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m'[self]).mterm]
                                                                         /\ state' = [state EXCEPT ![self] = Follower]
                                                                         /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                         /\ leader' = [leader EXCEPT ![self] = Nil]
                                                                         /\ IF ((m'[self]).mterm) < ((currentTerm')[self])
                                                                               THEN /\ network' = network0
                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                    /\ UNCHANGED << votesResponded, 
                                                                                                    votesGranted >>
                                                                               ELSE /\ LET i == self IN
                                                                                         LET j == (m'[self]).msource IN
                                                                                           /\ Assert(((m'[self]).mterm) = ((currentTerm')[i]), 
                                                                                                     "Failure of assertion at line 1083, column 21.")
                                                                                           /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                                           /\ IF (m'[self]).mvoteGranted
                                                                                                 THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                                      /\ network' = network0
                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 ELSE /\ network' = network0
                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                      /\ UNCHANGED votesGranted
                                                                    ELSE /\ IF ((m'[self]).mterm) < ((currentTerm)[self])
                                                                               THEN /\ network' = network0
                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                    /\ UNCHANGED << votesResponded, 
                                                                                                    votesGranted >>
                                                                               ELSE /\ LET i == self IN
                                                                                         LET j == (m'[self]).msource IN
                                                                                           /\ Assert(((m'[self]).mterm) = ((currentTerm)[i]), 
                                                                                                     "Failure of assertion at line 1104, column 21.")
                                                                                           /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                                           /\ IF (m'[self]).mvoteGranted
                                                                                                 THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                                      /\ network' = network0
                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 ELSE /\ network' = network0
                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                      /\ UNCHANGED votesGranted
                                                                         /\ UNCHANGED << state, 
                                                                                         currentTerm, 
                                                                                         votedFor, 
                                                                                         leader >>
                                                              /\ UNCHANGED << commitIndex, 
                                                                              nextIndex, 
                                                                              matchIndex, 
                                                                              log, 
                                                                              plog, 
                                                                              sm, 
                                                                              smDomain >>
                                                         ELSE /\ IF ((m'[self]).mtype) = (AppendEntriesRequest)
                                                                    THEN /\ IF ((m'[self]).mterm) > ((currentTerm)[self])
                                                                               THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m'[self]).mterm]
                                                                                    /\ LET state1 == [state EXCEPT ![self] = Follower] IN
                                                                                         /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                                         /\ LET leader1 == [leader EXCEPT ![self] = Nil] IN
                                                                                              /\ leader' = [leader1 EXCEPT ![self] = (m'[self]).msource]
                                                                                              /\ LET i == self IN
                                                                                                   LET j == (m'[self]).msource IN
                                                                                                     LET logOK == (((m'[self]).mprevLogIndex) = (0)) \/ (((((m'[self]).mprevLogIndex) > (0)) /\ (((m'[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m'[self]).mprevLogTerm) = ((((log)[i])[(m'[self]).mprevLogIndex]).term))) IN
                                                                                                       /\ Assert(((m'[self]).mterm) <= ((currentTerm')[i]), 
                                                                                                                 "Failure of assertion at line 1130, column 25.")
                                                                                                       /\ IF (((m'[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                                             THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                                                  /\ IF (((m'[self]).mterm) < ((currentTerm')[i])) \/ (((((m'[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                                        THEN /\ \/ /\ LET value13 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value13), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                                                                                        /\ yielded_fd00
                                                                                                                                        /\ network' = network0
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                             log, 
                                                                                                                                             plog, 
                                                                                                                                             sm, 
                                                                                                                                             smDomain >>
                                                                                                                        ELSE /\ Assert(((((m'[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                                       "Failure of assertion at line 1149, column 29.")
                                                                                                                             /\ LET index == ((m'[self]).mprevLogIndex) + (1) IN
                                                                                                                                  IF ((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m'[self]).mentries)[1]).term))
                                                                                                                                     THEN /\ LET log4 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                                               LET value20 == [cmd |-> LogPop] IN
                                                                                                                                                 IF ((value20).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ LET plog4 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value20).entries)] IN
                                                                                                                                                              IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                 THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                      /\ LET value30 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                           IF ((value30).cmd) = (LogConcat)
                                                                                                                                                                              THEN /\ plog' = [plog4 EXCEPT ![i] = ((plog4)[i]) \o ((value30).entries)]
                                                                                                                                                                                   /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                         THEN /\ LET result16 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result16)[1]]
                                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result16)[2]]
                                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                   /\ \/ /\ LET value40 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value40), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                      \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                                                                                                                              /\ yielded_fd11
                                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                         ELSE /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                              sm, 
                                                                                                                                                                                                              smDomain >>
                                                                                                                                                                              ELSE /\ IF ((value30).cmd) = (LogPop)
                                                                                                                                                                                         THEN /\ plog' = [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))]
                                                                                                                                                                                              /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result17 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result17)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result17)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value41 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value41), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd12
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                                         ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result18 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result18)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result18)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value42 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value42), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ plog' = plog4
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd13
                                                                                                                                                                                                                         /\ plog' = plog4
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ plog' = plog4
                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                 ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                            THEN /\ LET result19 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                      /\ sm' = [sm EXCEPT ![i] = (result19)[1]]
                                                                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![i] = (result19)[2]]
                                                                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                      /\ \/ /\ LET value43 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                 /\ ((network0)[j]).enabled
                                                                                                                                                                                                 /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                 /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value43), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                 /\ plog' = plog4
                                                                                                                                                                                                 /\ log' = log4
                                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                         \/ /\ LET yielded_fd14 == (fd)[j] IN
                                                                                                                                                                                                 /\ yielded_fd14
                                                                                                                                                                                                 /\ plog' = plog4
                                                                                                                                                                                                 /\ log' = log4
                                                                                                                                                                                                 /\ network' = network0
                                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            ELSE /\ plog' = plog4
                                                                                                                                                                                 /\ log' = log4
                                                                                                                                                                                 /\ network' = network0
                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                 sm, 
                                                                                                                                                                                                 smDomain >>
                                                                                                                                                    ELSE /\ IF ((value20).cmd) = (LogPop)
                                                                                                                                                               THEN /\ LET plog5 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                                         IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                            THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                                 /\ LET value31 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                                      IF ((value31).cmd) = (LogConcat)
                                                                                                                                                                                         THEN /\ plog' = [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value31).entries)]
                                                                                                                                                                                              /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result20 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result20)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result20)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value44 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value44), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd15 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd15
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                                         ELSE /\ IF ((value31).cmd) = (LogPop)
                                                                                                                                                                                                    THEN /\ plog' = [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))]
                                                                                                                                                                                                         /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                               THEN /\ LET result21 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result21)[1]]
                                                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result21)[2]]
                                                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                         /\ \/ /\ LET value45 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value45), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                            \/ /\ LET yielded_fd16 == (fd)[j] IN
                                                                                                                                                                                                                                    /\ yielded_fd16
                                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               ELSE /\ network' = network0
                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                                                    ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                               THEN /\ LET result22 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result22)[1]]
                                                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result22)[2]]
                                                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                         /\ \/ /\ LET value46 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value46), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                    /\ plog' = plog5
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                            \/ /\ LET yielded_fd17 == (fd)[j] IN
                                                                                                                                                                                                                                    /\ yielded_fd17
                                                                                                                                                                                                                                    /\ plog' = plog5
                                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               ELSE /\ plog' = plog5
                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                            ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                       THEN /\ LET result23 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                 /\ sm' = [sm EXCEPT ![i] = (result23)[1]]
                                                                                                                                                                                                 /\ smDomain' = [smDomain EXCEPT ![i] = (result23)[2]]
                                                                                                                                                                                                 /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                 /\ \/ /\ LET value47 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                            /\ ((network0)[j]).enabled
                                                                                                                                                                                                            /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                            /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value47), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                            /\ plog' = plog5
                                                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    \/ /\ LET yielded_fd18 == (fd)[j] IN
                                                                                                                                                                                                            /\ yielded_fd18
                                                                                                                                                                                                            /\ plog' = plog5
                                                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                                                            /\ network' = network0
                                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       ELSE /\ plog' = plog5
                                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                                            /\ network' = network0
                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                            sm, 
                                                                                                                                                                                                            smDomain >>
                                                                                                                                                               ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                          THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                               /\ LET value32 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                                    IF ((value32).cmd) = (LogConcat)
                                                                                                                                                                                       THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)]
                                                                                                                                                                                            /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                  THEN /\ LET result24 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result24)[1]]
                                                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result24)[2]]
                                                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                            /\ \/ /\ LET value48 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                       /\ ((network0)[j]).enabled
                                                                                                                                                                                                                       /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                       /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value48), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               \/ /\ LET yielded_fd19 == (fd)[j] IN
                                                                                                                                                                                                                       /\ yielded_fd19
                                                                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  ELSE /\ network' = network0
                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                       sm, 
                                                                                                                                                                                                                       smDomain >>
                                                                                                                                                                                       ELSE /\ IF ((value32).cmd) = (LogPop)
                                                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                                       /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                             THEN /\ LET result25 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result25)[1]]
                                                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result25)[2]]
                                                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                       /\ \/ /\ LET value49 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value49), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                          \/ /\ LET yielded_fd110 == (fd)[j] IN
                                                                                                                                                                                                                                  /\ yielded_fd110
                                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                             ELSE /\ network' = network0
                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                                                  ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                             THEN /\ LET result26 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result26)[1]]
                                                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result26)[2]]
                                                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                       /\ \/ /\ LET value410 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value410), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                          \/ /\ LET yielded_fd111 == (fd)[j] IN
                                                                                                                                                                                                                                  /\ yielded_fd111
                                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                             ELSE /\ network' = network0
                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                                                       /\ plog' = plog
                                                                                                                                                                          ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result27 == ApplyLog((log4)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result27)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result27)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                               /\ \/ /\ LET value411 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value411), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                          /\ log' = log4
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd112 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd112
                                                                                                                                                                                                          /\ log' = log4
                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     ELSE /\ log' = log4
                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                               /\ plog' = plog
                                                                                                                                     ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                     /\ LET value33 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                          IF ((value33).cmd) = (LogConcat)
                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)]
                                                                                                                                                                  /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                        THEN /\ LET result28 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result28)[1]]
                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result28)[2]]
                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                  /\ \/ /\ LET value412 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                             /\ ((network0)[j]).enabled
                                                                                                                                                                                             /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                             /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value412), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     \/ /\ LET yielded_fd113 == (fd)[j] IN
                                                                                                                                                                                             /\ yielded_fd113
                                                                                                                                                                                             /\ network' = network0
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        ELSE /\ network' = network0
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                             sm, 
                                                                                                                                                                                             smDomain >>
                                                                                                                                                             ELSE /\ IF ((value33).cmd) = (LogPop)
                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                             /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result29 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result29)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result29)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                             /\ \/ /\ LET value413 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value413), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd114 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd114
                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                        ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result30 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result30)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result30)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                             /\ \/ /\ LET value414 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value414), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd115 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd115
                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                           THEN /\ LET result31 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result31)[1]]
                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result31)[2]]
                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                     /\ \/ /\ LET value415 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network0)[j]).enabled
                                                                                                                                                                                /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value415), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        \/ /\ LET yielded_fd116 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd116
                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           ELSE /\ network' = network0
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                sm, 
                                                                                                                                                                                smDomain >>
                                                                                                                                                     /\ UNCHANGED << log, 
                                                                                                                                                                     plog >>
                                                                                                             ELSE /\ IF (((m'[self]).mterm) < ((currentTerm')[i])) \/ (((((m'[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                                        THEN /\ \/ /\ LET value14 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value14), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                        /\ state' = state1
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                \/ /\ LET yielded_fd01 == (fd)[j] IN
                                                                                                                                        /\ yielded_fd01
                                                                                                                                        /\ state' = state1
                                                                                                                                        /\ network' = network0
                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                             log, 
                                                                                                                                             plog, 
                                                                                                                                             sm, 
                                                                                                                                             smDomain >>
                                                                                                                        ELSE /\ Assert(((((m'[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                                       "Failure of assertion at line 1651, column 29.")
                                                                                                                             /\ LET index == ((m'[self]).mprevLogIndex) + (1) IN
                                                                                                                                  IF ((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m'[self]).mentries)[1]).term))
                                                                                                                                     THEN /\ LET log5 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                                               LET value21 == [cmd |-> LogPop] IN
                                                                                                                                                 IF ((value21).cmd) = (LogConcat)
                                                                                                                                                    THEN /\ LET plog6 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value21).entries)] IN
                                                                                                                                                              IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                 THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                      /\ LET value34 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                           IF ((value34).cmd) = (LogConcat)
                                                                                                                                                                              THEN /\ plog' = [plog6 EXCEPT ![i] = ((plog6)[i]) \o ((value34).entries)]
                                                                                                                                                                                   /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                         THEN /\ LET result32 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result32)[1]]
                                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result32)[2]]
                                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                   /\ \/ /\ LET value416 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value416), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                      \/ /\ LET yielded_fd117 == (fd)[j] IN
                                                                                                                                                                                                              /\ yielded_fd117
                                                                                                                                                                                                              /\ state' = state1
                                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                         ELSE /\ state' = state1
                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                              sm, 
                                                                                                                                                                                                              smDomain >>
                                                                                                                                                                              ELSE /\ IF ((value34).cmd) = (LogPop)
                                                                                                                                                                                         THEN /\ plog' = [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))]
                                                                                                                                                                                              /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result33 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result33)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result33)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value417 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value417), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd118 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd118
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ state' = state1
                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                                         ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result34 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result34)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result34)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value418 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value418), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ plog' = plog6
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd119 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd119
                                                                                                                                                                                                                         /\ plog' = plog6
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ plog' = plog6
                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                 ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                            THEN /\ LET result35 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                      /\ sm' = [sm EXCEPT ![i] = (result35)[1]]
                                                                                                                                                                                      /\ smDomain' = [smDomain EXCEPT ![i] = (result35)[2]]
                                                                                                                                                                                      /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                      /\ \/ /\ LET value419 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                 /\ ((network0)[j]).enabled
                                                                                                                                                                                                 /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                 /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value419), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                 /\ plog' = plog6
                                                                                                                                                                                                 /\ log' = log5
                                                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                         \/ /\ LET yielded_fd120 == (fd)[j] IN
                                                                                                                                                                                                 /\ yielded_fd120
                                                                                                                                                                                                 /\ plog' = plog6
                                                                                                                                                                                                 /\ log' = log5
                                                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                                                 /\ network' = network0
                                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                            ELSE /\ plog' = plog6
                                                                                                                                                                                 /\ log' = log5
                                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                                 /\ network' = network0
                                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                 sm, 
                                                                                                                                                                                                 smDomain >>
                                                                                                                                                    ELSE /\ IF ((value21).cmd) = (LogPop)
                                                                                                                                                               THEN /\ LET plog7 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                                         IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                            THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                                 /\ LET value35 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                                      IF ((value35).cmd) = (LogConcat)
                                                                                                                                                                                         THEN /\ plog' = [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value35).entries)]
                                                                                                                                                                                              /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                    THEN /\ LET result36 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                              /\ sm' = [sm EXCEPT ![i] = (result36)[1]]
                                                                                                                                                                                                              /\ smDomain' = [smDomain EXCEPT ![i] = (result36)[2]]
                                                                                                                                                                                                              /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                              /\ \/ /\ LET value420 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                         /\ ((network0)[j]).enabled
                                                                                                                                                                                                                         /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                         /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value420), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                 \/ /\ LET yielded_fd121 == (fd)[j] IN
                                                                                                                                                                                                                         /\ yielded_fd121
                                                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    ELSE /\ state' = state1
                                                                                                                                                                                                         /\ network' = network0
                                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                         /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                         sm, 
                                                                                                                                                                                                                         smDomain >>
                                                                                                                                                                                         ELSE /\ IF ((value35).cmd) = (LogPop)
                                                                                                                                                                                                    THEN /\ plog' = [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))]
                                                                                                                                                                                                         /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                               THEN /\ LET result37 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result37)[1]]
                                                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result37)[2]]
                                                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                         /\ \/ /\ LET value421 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value421), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                            \/ /\ LET yielded_fd122 == (fd)[j] IN
                                                                                                                                                                                                                                    /\ yielded_fd122
                                                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               ELSE /\ state' = state1
                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                                                    ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                               THEN /\ LET result38 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result38)[1]]
                                                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result38)[2]]
                                                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                         /\ \/ /\ LET value422 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value422), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                    /\ plog' = plog7
                                                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                            \/ /\ LET yielded_fd123 == (fd)[j] IN
                                                                                                                                                                                                                                    /\ yielded_fd123
                                                                                                                                                                                                                                    /\ plog' = plog7
                                                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               ELSE /\ plog' = plog7
                                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                            ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                       THEN /\ LET result39 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                 /\ sm' = [sm EXCEPT ![i] = (result39)[1]]
                                                                                                                                                                                                 /\ smDomain' = [smDomain EXCEPT ![i] = (result39)[2]]
                                                                                                                                                                                                 /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                 /\ \/ /\ LET value423 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                            /\ ((network0)[j]).enabled
                                                                                                                                                                                                            /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                            /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value423), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                            /\ plog' = plog7
                                                                                                                                                                                                            /\ log' = log5
                                                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                    \/ /\ LET yielded_fd124 == (fd)[j] IN
                                                                                                                                                                                                            /\ yielded_fd124
                                                                                                                                                                                                            /\ plog' = plog7
                                                                                                                                                                                                            /\ log' = log5
                                                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                                                            /\ network' = network0
                                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                       ELSE /\ plog' = plog7
                                                                                                                                                                                            /\ log' = log5
                                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                                            /\ network' = network0
                                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                            sm, 
                                                                                                                                                                                                            smDomain >>
                                                                                                                                                               ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                          THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                               /\ LET value36 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                                    IF ((value36).cmd) = (LogConcat)
                                                                                                                                                                                       THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value36).entries)]
                                                                                                                                                                                            /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                  THEN /\ LET result40 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result40)[1]]
                                                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result40)[2]]
                                                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                            /\ \/ /\ LET value424 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                       /\ ((network0)[j]).enabled
                                                                                                                                                                                                                       /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                       /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value424), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                               \/ /\ LET yielded_fd125 == (fd)[j] IN
                                                                                                                                                                                                                       /\ yielded_fd125
                                                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  ELSE /\ state' = state1
                                                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                       sm, 
                                                                                                                                                                                                                       smDomain >>
                                                                                                                                                                                       ELSE /\ IF ((value36).cmd) = (LogPop)
                                                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                                       /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                             THEN /\ LET result41 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result41)[1]]
                                                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result41)[2]]
                                                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                       /\ \/ /\ LET value425 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value425), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                          \/ /\ LET yielded_fd126 == (fd)[j] IN
                                                                                                                                                                                                                                  /\ yielded_fd126
                                                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                             ELSE /\ state' = state1
                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                                                  ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                             THEN /\ LET result42 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result42)[1]]
                                                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result42)[2]]
                                                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                                       /\ \/ /\ LET value426 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value426), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                          \/ /\ LET yielded_fd127 == (fd)[j] IN
                                                                                                                                                                                                                                  /\ yielded_fd127
                                                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                             ELSE /\ state' = state1
                                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                                                  smDomain >>
                                                                                                                                                                                                       /\ plog' = plog
                                                                                                                                                                          ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                     THEN /\ LET result43 == ApplyLog((log5)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result43)[1]]
                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result43)[2]]
                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                               /\ \/ /\ LET value427 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value427), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                          /\ log' = log5
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                  \/ /\ LET yielded_fd128 == (fd)[j] IN
                                                                                                                                                                                                          /\ yielded_fd128
                                                                                                                                                                                                          /\ log' = log5
                                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     ELSE /\ log' = log5
                                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                               /\ plog' = plog
                                                                                                                                     ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                     /\ LET value37 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                          IF ((value37).cmd) = (LogConcat)
                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value37).entries)]
                                                                                                                                                                  /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                        THEN /\ LET result44 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result44)[1]]
                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result44)[2]]
                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                  /\ \/ /\ LET value428 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                             /\ ((network0)[j]).enabled
                                                                                                                                                                                             /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                             /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value428), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     \/ /\ LET yielded_fd129 == (fd)[j] IN
                                                                                                                                                                                             /\ yielded_fd129
                                                                                                                                                                                             /\ state' = state1
                                                                                                                                                                                             /\ network' = network0
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        ELSE /\ state' = state1
                                                                                                                                                                             /\ network' = network0
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                             sm, 
                                                                                                                                                                                             smDomain >>
                                                                                                                                                             ELSE /\ IF ((value37).cmd) = (LogPop)
                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                             /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result45 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result45)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result45)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                             /\ \/ /\ LET value429 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value429), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd130 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd130
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                        ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                   THEN /\ LET result46 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result46)[1]]
                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result46)[2]]
                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                             /\ \/ /\ LET value430 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value430), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                \/ /\ LET yielded_fd131 == (fd)[j] IN
                                                                                                                                                                                                        /\ yielded_fd131
                                                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                           THEN /\ LET result47 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result47)[1]]
                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result47)[2]]
                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                     /\ \/ /\ LET value431 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network0)[j]).enabled
                                                                                                                                                                                /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value431), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                /\ state' = state1
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        \/ /\ LET yielded_fd132 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd132
                                                                                                                                                                                /\ state' = state1
                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           ELSE /\ state' = state1
                                                                                                                                                                /\ network' = network0
                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                sm, 
                                                                                                                                                                                smDomain >>
                                                                                                                                                     /\ UNCHANGED << log, 
                                                                                                                                                                     plog >>
                                                                               ELSE /\ leader' = [leader EXCEPT ![self] = (m'[self]).msource]
                                                                                    /\ LET i == self IN
                                                                                         LET j == (m'[self]).msource IN
                                                                                           LET logOK == (((m'[self]).mprevLogIndex) = (0)) \/ (((((m'[self]).mprevLogIndex) > (0)) /\ (((m'[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m'[self]).mprevLogTerm) = ((((log)[i])[(m'[self]).mprevLogIndex]).term))) IN
                                                                                             /\ Assert(((m'[self]).mterm) <= ((currentTerm)[i]), 
                                                                                                       "Failure of assertion at line 2193, column 21.")
                                                                                             /\ IF (((m'[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                                                   THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                                        /\ IF (((m'[self]).mterm) < ((currentTerm)[i])) \/ (((((m'[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                              THEN /\ \/ /\ LET value15 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value15), enabled |-> ((network0)[j]).enabled]]
                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                                                                              /\ yielded_fd02
                                                                                                                              /\ network' = network0
                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   /\ UNCHANGED << commitIndex, 
                                                                                                                                   log, 
                                                                                                                                   plog, 
                                                                                                                                   sm, 
                                                                                                                                   smDomain >>
                                                                                                              ELSE /\ Assert(((((m'[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                             "Failure of assertion at line 2212, column 25.")
                                                                                                                   /\ LET index == ((m'[self]).mprevLogIndex) + (1) IN
                                                                                                                        IF ((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m'[self]).mentries)[1]).term))
                                                                                                                           THEN /\ LET log6 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                                     LET value22 == [cmd |-> LogPop] IN
                                                                                                                                       IF ((value22).cmd) = (LogConcat)
                                                                                                                                          THEN /\ LET plog8 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value22).entries)] IN
                                                                                                                                                    IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                            /\ LET value38 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                 IF ((value38).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value38).entries)]
                                                                                                                                                                         /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result48 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result48)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result48)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value432 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value432), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd133 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd133
                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               ELSE /\ network' = network0
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF ((value38).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result49 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result49)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result49)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value433 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value433), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd134 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd134
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result50 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result50)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result50)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value434 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value434), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog8
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd135 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd135
                                                                                                                                                                                                               /\ plog' = plog8
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ plog' = plog8
                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                       ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET result51 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result51)[1]]
                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result51)[2]]
                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                            /\ \/ /\ LET value435 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network0)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value435), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog8
                                                                                                                                                                                       /\ log' = log6
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd136 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd136
                                                                                                                                                                                       /\ plog' = plog8
                                                                                                                                                                                       /\ log' = log6
                                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  ELSE /\ plog' = plog8
                                                                                                                                                                       /\ log' = log6
                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                       sm, 
                                                                                                                                                                                       smDomain >>
                                                                                                                                          ELSE /\ IF ((value22).cmd) = (LogPop)
                                                                                                                                                     THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                               IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                  THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                       /\ LET value39 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                            IF ((value39).cmd) = (LogConcat)
                                                                                                                                                                               THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value39).entries)]
                                                                                                                                                                                    /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result52 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result52)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result52)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value436 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value436), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd137 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd137
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF ((value39).cmd) = (LogPop)
                                                                                                                                                                                          THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))]
                                                                                                                                                                                               /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                     THEN /\ LET result53 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result53)[1]]
                                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result53)[2]]
                                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                               /\ \/ /\ LET value437 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value437), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  \/ /\ LET yielded_fd138 == (fd)[j] IN
                                                                                                                                                                                                                          /\ yielded_fd138
                                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     ELSE /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                                          ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                     THEN /\ LET result54 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result54)[1]]
                                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result54)[2]]
                                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                               /\ \/ /\ LET value438 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value438), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                          /\ plog' = plog9
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  \/ /\ LET yielded_fd139 == (fd)[j] IN
                                                                                                                                                                                                                          /\ yielded_fd139
                                                                                                                                                                                                                          /\ plog' = plog9
                                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     ELSE /\ plog' = plog9
                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                  ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET result55 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result55)[1]]
                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result55)[2]]
                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                       /\ \/ /\ LET value439 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value439), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                  /\ plog' = plog9
                                                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd140 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd140
                                                                                                                                                                                                  /\ plog' = plog9
                                                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             ELSE /\ plog' = plog9
                                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                  smDomain >>
                                                                                                                                                     ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                     /\ LET value310 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                          IF ((value310).cmd) = (LogConcat)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value310).entries)]
                                                                                                                                                                                  /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result56 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result56)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result56)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value440 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network0)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value440), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd141 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd141
                                                                                                                                                                                                             /\ network' = network0
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        ELSE /\ network' = network0
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                             ELSE /\ IF ((value310).cmd) = (LogPop)
                                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                             /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                   THEN /\ LET result57 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result57)[1]]
                                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result57)[2]]
                                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                             /\ \/ /\ LET value441 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value441), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                \/ /\ LET yielded_fd142 == (fd)[j] IN
                                                                                                                                                                                                                        /\ yielded_fd142
                                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                                        ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                   THEN /\ LET result58 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result58)[1]]
                                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result58)[2]]
                                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                             /\ \/ /\ LET value442 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value442), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                \/ /\ LET yielded_fd143 == (fd)[j] IN
                                                                                                                                                                                                                        /\ yielded_fd143
                                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                                ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                           THEN /\ LET result59 == ApplyLog((log6)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result59)[1]]
                                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result59)[2]]
                                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                     /\ \/ /\ LET value443 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                /\ ((network0)[j]).enabled
                                                                                                                                                                                                /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value443), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                /\ log' = log6
                                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        \/ /\ LET yielded_fd144 == (fd)[j] IN
                                                                                                                                                                                                /\ yielded_fd144
                                                                                                                                                                                                /\ log' = log6
                                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           ELSE /\ log' = log6
                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                sm, 
                                                                                                                                                                                                smDomain >>
                                                                                                                                                                     /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m'[self]).mentries)]
                                                                                                                                           /\ LET value311 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                IF ((value311).cmd) = (LogConcat)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)]
                                                                                                                                                        /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result60 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result60)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result60)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value444 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network0)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value444), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd145 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd145
                                                                                                                                                                                   /\ network' = network0
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              ELSE /\ network' = network0
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                   ELSE /\ IF ((value311).cmd) = (LogPop)
                                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                   /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                         THEN /\ LET result61 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result61)[1]]
                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result61)[2]]
                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                   /\ \/ /\ LET value445 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value445), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                      \/ /\ LET yielded_fd146 == (fd)[j] IN
                                                                                                                                                                                              /\ yielded_fd146
                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         ELSE /\ network' = network0
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                              sm, 
                                                                                                                                                                                              smDomain >>
                                                                                                                                                              ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                         THEN /\ LET result62 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result62)[1]]
                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result62)[2]]
                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                   /\ \/ /\ LET value446 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value446), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                      \/ /\ LET yielded_fd147 == (fd)[j] IN
                                                                                                                                                                                              /\ yielded_fd147
                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         ELSE /\ network' = network0
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                              sm, 
                                                                                                                                                                                              smDomain >>
                                                                                                                                                                   /\ plog' = plog
                                                                                                                                      ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                 THEN /\ LET result63 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result63)[1]]
                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result63)[2]]
                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                           /\ \/ /\ LET value447 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                      /\ ((network0)[j]).enabled
                                                                                                                                                                      /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                      /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value447), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              \/ /\ LET yielded_fd148 == (fd)[j] IN
                                                                                                                                                                      /\ yielded_fd148
                                                                                                                                                                      /\ network' = network0
                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 ELSE /\ network' = network0
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      /\ UNCHANGED << commitIndex, 
                                                                                                                                                                      sm, 
                                                                                                                                                                      smDomain >>
                                                                                                                                           /\ UNCHANGED << log, 
                                                                                                                                                           plog >>
                                                                                                   ELSE /\ IF (((m'[self]).mterm) < ((currentTerm)[i])) \/ (((((m'[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                              THEN /\ \/ /\ LET value16 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value16), enabled |-> ((network0)[j]).enabled]]
                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                      \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                                                                              /\ yielded_fd03
                                                                                                                              /\ network' = network0
                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                   /\ UNCHANGED << commitIndex, 
                                                                                                                                   log, 
                                                                                                                                   plog, 
                                                                                                                                   sm, 
                                                                                                                                   smDomain >>
                                                                                                              ELSE /\ Assert(((((m'[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                                             "Failure of assertion at line 2712, column 25.")
                                                                                                                   /\ LET index == ((m'[self]).mprevLogIndex) + (1) IN
                                                                                                                        IF ((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m'[self]).mentries)[1]).term))
                                                                                                                           THEN /\ LET log7 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                                     LET value23 == [cmd |-> LogPop] IN
                                                                                                                                       IF ((value23).cmd) = (LogConcat)
                                                                                                                                          THEN /\ LET plog10 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value23).entries)] IN
                                                                                                                                                    IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                            /\ LET value312 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                 IF ((value312).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value312).entries)]
                                                                                                                                                                         /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET result64 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                         /\ sm' = [sm EXCEPT ![i] = (result64)[1]]
                                                                                                                                                                                         /\ smDomain' = [smDomain EXCEPT ![i] = (result64)[2]]
                                                                                                                                                                                         /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                         /\ \/ /\ LET value448 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network0)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value448), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd149 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd149
                                                                                                                                                                                                    /\ network' = network0
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               ELSE /\ network' = network0
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                    sm, 
                                                                                                                                                                                                    smDomain >>
                                                                                                                                                                    ELSE /\ IF ((value312).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result65 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result65)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result65)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value449 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value449), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd150 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd150
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result66 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result66)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result66)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value450 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value450), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog10
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd151 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd151
                                                                                                                                                                                                               /\ plog' = plog10
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ plog' = plog10
                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                       ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET result67 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                            /\ sm' = [sm EXCEPT ![i] = (result67)[1]]
                                                                                                                                                                            /\ smDomain' = [smDomain EXCEPT ![i] = (result67)[2]]
                                                                                                                                                                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                            /\ \/ /\ LET value451 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network0)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value451), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog10
                                                                                                                                                                                       /\ log' = log7
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd152 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd152
                                                                                                                                                                                       /\ plog' = plog10
                                                                                                                                                                                       /\ log' = log7
                                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                  ELSE /\ plog' = plog10
                                                                                                                                                                       /\ log' = log7
                                                                                                                                                                       /\ network' = network0
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                       sm, 
                                                                                                                                                                                       smDomain >>
                                                                                                                                          ELSE /\ IF ((value23).cmd) = (LogPop)
                                                                                                                                                     THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                               IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                  THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                       /\ LET value313 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                            IF ((value313).cmd) = (LogConcat)
                                                                                                                                                                               THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value313).entries)]
                                                                                                                                                                                    /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET result68 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                    /\ sm' = [sm EXCEPT ![i] = (result68)[1]]
                                                                                                                                                                                                    /\ smDomain' = [smDomain EXCEPT ![i] = (result68)[2]]
                                                                                                                                                                                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                    /\ \/ /\ LET value452 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network0)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value452), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd153 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd153
                                                                                                                                                                                                               /\ network' = network0
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          ELSE /\ network' = network0
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                               sm, 
                                                                                                                                                                                                               smDomain >>
                                                                                                                                                                               ELSE /\ IF ((value313).cmd) = (LogPop)
                                                                                                                                                                                          THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))]
                                                                                                                                                                                               /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                     THEN /\ LET result69 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result69)[1]]
                                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result69)[2]]
                                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                               /\ \/ /\ LET value453 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value453), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  \/ /\ LET yielded_fd154 == (fd)[j] IN
                                                                                                                                                                                                                          /\ yielded_fd154
                                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     ELSE /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                                          ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                     THEN /\ LET result70 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                               /\ sm' = [sm EXCEPT ![i] = (result70)[1]]
                                                                                                                                                                                                               /\ smDomain' = [smDomain EXCEPT ![i] = (result70)[2]]
                                                                                                                                                                                                               /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                               /\ \/ /\ LET value454 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                          /\ ((network0)[j]).enabled
                                                                                                                                                                                                                          /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                          /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value454), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                          /\ plog' = plog11
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                  \/ /\ LET yielded_fd155 == (fd)[j] IN
                                                                                                                                                                                                                          /\ yielded_fd155
                                                                                                                                                                                                                          /\ plog' = plog11
                                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     ELSE /\ plog' = plog11
                                                                                                                                                                                                          /\ network' = network0
                                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                          sm, 
                                                                                                                                                                                                                          smDomain >>
                                                                                                                                                                  ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET result71 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                       /\ sm' = [sm EXCEPT ![i] = (result71)[1]]
                                                                                                                                                                                       /\ smDomain' = [smDomain EXCEPT ![i] = (result71)[2]]
                                                                                                                                                                                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                       /\ \/ /\ LET value455 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network0)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value455), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                  /\ plog' = plog11
                                                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd156 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd156
                                                                                                                                                                                                  /\ plog' = plog11
                                                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             ELSE /\ plog' = plog11
                                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                                  /\ network' = network0
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                  sm, 
                                                                                                                                                                                                  smDomain >>
                                                                                                                                                     ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                                                THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m'[self]).mentries)]
                                                                                                                                                                     /\ LET value314 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                                          IF ((value314).cmd) = (LogConcat)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)]
                                                                                                                                                                                  /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET result72 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                  /\ sm' = [sm EXCEPT ![i] = (result72)[1]]
                                                                                                                                                                                                  /\ smDomain' = [smDomain EXCEPT ![i] = (result72)[2]]
                                                                                                                                                                                                  /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                  /\ \/ /\ LET value456 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network0)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value456), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd157 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd157
                                                                                                                                                                                                             /\ network' = network0
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        ELSE /\ network' = network0
                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                             sm, 
                                                                                                                                                                                                             smDomain >>
                                                                                                                                                                             ELSE /\ IF ((value314).cmd) = (LogPop)
                                                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                             /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                   THEN /\ LET result73 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result73)[1]]
                                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result73)[2]]
                                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                             /\ \/ /\ LET value457 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value457), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                \/ /\ LET yielded_fd158 == (fd)[j] IN
                                                                                                                                                                                                                        /\ yielded_fd158
                                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                                        ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                                                   THEN /\ LET result74 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                                             /\ sm' = [sm EXCEPT ![i] = (result74)[1]]
                                                                                                                                                                                                             /\ smDomain' = [smDomain EXCEPT ![i] = (result74)[2]]
                                                                                                                                                                                                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                                             /\ \/ /\ LET value458 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                                        /\ ((network0)[j]).enabled
                                                                                                                                                                                                                        /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                                        /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value458), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                                \/ /\ LET yielded_fd159 == (fd)[j] IN
                                                                                                                                                                                                                        /\ yielded_fd159
                                                                                                                                                                                                                        /\ network' = network0
                                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                   ELSE /\ network' = network0
                                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                                        sm, 
                                                                                                                                                                                                                        smDomain >>
                                                                                                                                                                                             /\ plog' = plog
                                                                                                                                                                ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                           THEN /\ LET result75 == ApplyLog((log7)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                     /\ sm' = [sm EXCEPT ![i] = (result75)[1]]
                                                                                                                                                                                     /\ smDomain' = [smDomain EXCEPT ![i] = (result75)[2]]
                                                                                                                                                                                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                     /\ \/ /\ LET value459 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                /\ ((network0)[j]).enabled
                                                                                                                                                                                                /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value459), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                                /\ log' = log7
                                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                        \/ /\ LET yielded_fd160 == (fd)[j] IN
                                                                                                                                                                                                /\ yielded_fd160
                                                                                                                                                                                                /\ log' = log7
                                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           ELSE /\ log' = log7
                                                                                                                                                                                /\ network' = network0
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                                sm, 
                                                                                                                                                                                                smDomain >>
                                                                                                                                                                     /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m'[self]).mprevLogIndex))
                                                                                                                                      THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m'[self]).mentries)]
                                                                                                                                           /\ LET value315 == [cmd |-> LogConcat, entries |-> (m'[self]).mentries] IN
                                                                                                                                                IF ((value315).cmd) = (LogConcat)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value315).entries)]
                                                                                                                                                        /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET result76 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                        /\ sm' = [sm EXCEPT ![i] = (result76)[1]]
                                                                                                                                                                        /\ smDomain' = [smDomain EXCEPT ![i] = (result76)[2]]
                                                                                                                                                                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                        /\ \/ /\ LET value460 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network0)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value460), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd161 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd161
                                                                                                                                                                                   /\ network' = network0
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              ELSE /\ network' = network0
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                   sm, 
                                                                                                                                                                                   smDomain >>
                                                                                                                                                   ELSE /\ IF ((value315).cmd) = (LogPop)
                                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                   /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                         THEN /\ LET result77 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result77)[1]]
                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result77)[2]]
                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                   /\ \/ /\ LET value461 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value461), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                      \/ /\ LET yielded_fd162 == (fd)[j] IN
                                                                                                                                                                                              /\ yielded_fd162
                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         ELSE /\ network' = network0
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                              sm, 
                                                                                                                                                                                              smDomain >>
                                                                                                                                                              ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                                         THEN /\ LET result78 == ApplyLog((log')[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                                                   /\ sm' = [sm EXCEPT ![i] = (result78)[1]]
                                                                                                                                                                                   /\ smDomain' = [smDomain EXCEPT ![i] = (result78)[2]]
                                                                                                                                                                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                                                   /\ \/ /\ LET value462 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                              /\ ((network0)[j]).enabled
                                                                                                                                                                                              /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                                              /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value462), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                      \/ /\ LET yielded_fd163 == (fd)[j] IN
                                                                                                                                                                                              /\ yielded_fd163
                                                                                                                                                                                              /\ network' = network0
                                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         ELSE /\ network' = network0
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED << commitIndex, 
                                                                                                                                                                                              sm, 
                                                                                                                                                                                              smDomain >>
                                                                                                                                                                   /\ plog' = plog
                                                                                                                                      ELSE /\ IF (((m'[self]).mentries) = (<<>>)) \/ (((((m'[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m'[self]).mentries)[1]).term)))
                                                                                                                                                 THEN /\ LET result79 == ApplyLog((log)[i], ((commitIndex)[i]) + (1), (m'[self]).mcommitIndex, (sm)[i], (smDomain)[i]) IN
                                                                                                                                                           /\ sm' = [sm EXCEPT ![i] = (result79)[1]]
                                                                                                                                                           /\ smDomain' = [smDomain EXCEPT ![i] = (result79)[2]]
                                                                                                                                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({(commitIndex)[i], (m'[self]).mcommitIndex})]
                                                                                                                                                           /\ \/ /\ LET value463 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m'[self]).mprevLogIndex) + (Len((m'[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                      /\ ((network0)[j]).enabled
                                                                                                                                                                      /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                                                                      /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value463), enabled |-> ((network0)[j]).enabled]]
                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                              \/ /\ LET yielded_fd164 == (fd)[j] IN
                                                                                                                                                                      /\ yielded_fd164
                                                                                                                                                                      /\ network' = network0
                                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                 ELSE /\ network' = network0
                                                                                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      /\ UNCHANGED << commitIndex, 
                                                                                                                                                                      sm, 
                                                                                                                                                                      smDomain >>
                                                                                                                                           /\ UNCHANGED << log, 
                                                                                                                                                           plog >>
                                                                                                        /\ state' = state
                                                                                    /\ UNCHANGED << currentTerm, 
                                                                                                    votedFor >>
                                                                         /\ UNCHANGED << nextIndex, 
                                                                                         matchIndex >>
                                                                    ELSE /\ IF ((m'[self]).mtype) = (AppendEntriesResponse)
                                                                               THEN /\ IF ((m'[self]).mterm) > ((currentTerm)[self])
                                                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m'[self]).mterm]
                                                                                               /\ state' = [state EXCEPT ![self] = Follower]
                                                                                               /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                                               /\ leader' = [leader EXCEPT ![self] = Nil]
                                                                                               /\ IF ((m'[self]).mterm) < ((currentTerm')[self])
                                                                                                     THEN /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          /\ UNCHANGED << nextIndex, 
                                                                                                                          matchIndex >>
                                                                                                     ELSE /\ LET i == self IN
                                                                                                               LET j == (m'[self]).msource IN
                                                                                                                 /\ Assert(((m'[self]).mterm) = ((currentTerm')[i]), 
                                                                                                                           "Failure of assertion at line 3213, column 25.")
                                                                                                                 /\ IF (m'[self]).msuccess
                                                                                                                       THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m'[self]).mmatchIndex) + (1)]]
                                                                                                                            /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m'[self]).mmatchIndex]]
                                                                                                                            /\ network' = network0
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                                            /\ network' = network0
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            /\ UNCHANGED matchIndex
                                                                                          ELSE /\ IF ((m'[self]).mterm) < ((currentTerm)[self])
                                                                                                     THEN /\ network' = network0
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          /\ UNCHANGED << nextIndex, 
                                                                                                                          matchIndex >>
                                                                                                     ELSE /\ LET i == self IN
                                                                                                               LET j == (m'[self]).msource IN
                                                                                                                 /\ Assert(((m'[self]).mterm) = ((currentTerm)[i]), 
                                                                                                                           "Failure of assertion at line 3235, column 25.")
                                                                                                                 /\ IF (m'[self]).msuccess
                                                                                                                       THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m'[self]).mmatchIndex) + (1)]]
                                                                                                                            /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m'[self]).mmatchIndex]]
                                                                                                                            /\ network' = network0
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                                            /\ network' = network0
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                            /\ UNCHANGED matchIndex
                                                                                               /\ UNCHANGED << state, 
                                                                                                               currentTerm, 
                                                                                                               votedFor, 
                                                                                                               leader >>
                                                                                    /\ UNCHANGED << log, 
                                                                                                    plog >>
                                                                               ELSE /\ IF (((m'[self]).mtype) = (ClientPutRequest)) \/ (((m'[self]).mtype) = (ClientGetRequest))
                                                                                          THEN /\ IF ((state)[self]) = (Leader)
                                                                                                     THEN /\ LET entry == [term |-> (currentTerm)[self], cmd |-> (m'[self]).mcmd, client |-> (m'[self]).msource] IN
                                                                                                               /\ log' = [log EXCEPT ![self] = Append((log)[self], entry)]
                                                                                                               /\ LET value50 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                                    IF ((value50).cmd) = (LogConcat)
                                                                                                                       THEN /\ plog' = [plog EXCEPT ![self] = ((plog)[self]) \o ((value50).entries)]
                                                                                                                            /\ network' = network0
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                       ELSE /\ IF ((value50).cmd) = (LogPop)
                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![self] = SubSeq((plog)[self], 1, (Len((plog)[self])) - (1))]
                                                                                                                                       /\ network' = network0
                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                  ELSE /\ network' = network0
                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                       /\ plog' = plog
                                                                                                     ELSE /\ LET i == self IN
                                                                                                               LET j == (m'[self]).msource IN
                                                                                                                 LET respType == IF (((m'[self]).mcmd).type) = (Put) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                                                   LET value60 == [mtype |-> respType, msuccess |-> FALSE, mresponse |-> Nil, mleaderHint |-> (leader)[i], msource |-> i, mdest |-> j] IN
                                                                                                                     /\ ((network0)[j]).enabled
                                                                                                                     /\ (Len(((network0)[j]).queue)) < (BufferSize)
                                                                                                                     /\ network' = [network0 EXCEPT ![j] = [queue |-> Append(((network0)[j]).queue, value60), enabled |-> ((network0)[j]).enabled]]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                          /\ UNCHANGED << log, 
                                                                                                                          plog >>
                                                                                          ELSE /\ network' = network0
                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                               /\ UNCHANGED << log, 
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
                                                                              votesGranted >>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                               /\ UNCHANGED << network, state, currentTerm, 
                                               commitIndex, nextIndex, 
                                               matchIndex, log, plog, votedFor, 
                                               votesResponded, votesGranted, 
                                               leader, sm, smDomain, m >>
                    /\ UNCHANGED << fd, leaderTimeout, appendEntriesCh, reqCh, 
                                    respCh, requestVoteSrvId, 
                                    appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    idx, srvId, idx0, srvId0, idx1, srvId1, 
                                    newCommitIndex, srvId2, srvId3, leader0, 
                                    req, resp, reqIdx, timeout >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value70 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value70]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, state, currentTerm, commitIndex, 
                                   nextIndex, matchIndex, log, plog, votedFor, 
                                   votesResponded, votesGranted, leader, sm, 
                                   smDomain, leaderTimeout, appendEntriesCh, 
                                   reqCh, respCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, idx, m, srvId, idx0, 
                                   srvId0, idx1, srvId1, newCommitIndex, 
                                   srvId2, srvId3, leader0, req, resp, reqIdx, 
                                   timeout >>

s0(self) == serverLoop(self) \/ failLabel(self)

serverRequestVoteLoop(self) == /\ pc[self] = "serverRequestVoteLoop"
                               /\ IF TRUE
                                     THEN /\ ((state)[srvId0[self]]) \in ({Follower, Candidate})
                                          /\ LET yielded_network00 == Len(((network)[srvId0[self]]).queue) IN
                                               /\ ((yielded_network00) = (0)) /\ (leaderTimeout)
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
                                               reqCh, respCh, requestVoteSrvId, 
                                               appendEntriesSrvId, 
                                               advanceCommitIndexSrvId, 
                                               becomeLeaderSrvId, idx, m, 
                                               srvId, srvId0, idx1, srvId1, 
                                               newCommitIndex, srvId2, srvId3, 
                                               leader0, req, resp, reqIdx, 
                                               timeout >>

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
                                         leaderTimeout, appendEntriesCh, reqCh, 
                                         respCh, requestVoteSrvId, 
                                         appendEntriesSrvId, 
                                         advanceCommitIndexSrvId, 
                                         becomeLeaderSrvId, idx, m, srvId, 
                                         srvId0, idx1, srvId1, newCommitIndex, 
                                         srvId2, srvId3, leader0, req, resp, 
                                         reqIdx, timeout >>

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
                                                 appendEntriesCh, reqCh, 
                                                 respCh, requestVoteSrvId, 
                                                 appendEntriesSrvId, 
                                                 advanceCommitIndexSrvId, 
                                                 becomeLeaderSrvId, idx, m, 
                                                 srvId, idx0, srvId0, srvId1, 
                                                 newCommitIndex, srvId2, 
                                                 srvId3, leader0, req, resp, 
                                                 reqIdx, timeout >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ LET yielded_network1 == ((network)[srvId1[self]]).enabled IN
                                IF ((yielded_network1) /\ (((state)[srvId1[self]]) = (Leader))) /\ ((idx1[self]) <= (NumServers))
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
                                           reqCh, respCh, requestVoteSrvId, 
                                           appendEntriesSrvId, 
                                           advanceCommitIndexSrvId, 
                                           becomeLeaderSrvId, idx, m, srvId, 
                                           idx0, srvId0, srvId1, 
                                           newCommitIndex, srvId2, srvId3, 
                                           leader0, req, resp, reqIdx, timeout >>

s2(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)

serverAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverAdvanceCommitIndexLoop"
                                      /\ IF TRUE
                                            THEN /\ ((state)[srvId2[self]]) = (Leader)
                                                 /\ LET i == srvId2[self] IN
                                                      LET agreeIndexes == FindAgreeIndices((log)[i], i, (matchIndex)[i]) IN
                                                        LET nCommitIndex == IF ((agreeIndexes) # ({})) /\ (((((log)[i])[Max(agreeIndexes)]).term) = ((currentTerm)[i])) THEN Max(agreeIndexes) ELSE (commitIndex)[i] IN
                                                          /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                                          /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                                    "Failure of assertion at line 3417, column 11.")
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
                                                      appendEntriesCh, reqCh, 
                                                      respCh, requestVoteSrvId, 
                                                      appendEntriesSrvId, 
                                                      advanceCommitIndexSrvId, 
                                                      becomeLeaderSrvId, idx, 
                                                      m, srvId, idx0, srvId0, 
                                                      idx1, srvId1, srvId2, 
                                                      srvId3, leader0, req, 
                                                      resp, reqIdx, timeout >>

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
                                   leaderTimeout, appendEntriesCh, reqCh, 
                                   respCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, idx, m, srvId, idx0, 
                                   srvId0, idx1, srvId1, newCommitIndex, 
                                   srvId2, srvId3, leader0, req, resp, reqIdx, 
                                   timeout >>

s3(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)

serverBecomeLeaderLoop(self) == /\ pc[self] = "serverBecomeLeaderLoop"
                                /\ IF TRUE
                                      THEN /\ (((state)[srvId3[self]]) = (Candidate)) /\ (isQuorum((votesGranted)[srvId3[self]]))
                                           /\ LET i == srvId3[self] IN
                                                /\ state' = [state EXCEPT ![i] = Leader]
                                                /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> (Len((log)[i])) + (1)]]
                                                /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
                                                /\ leader' = [leader EXCEPT ![i] = i]
                                                /\ appendEntriesCh' = TRUE
                                                /\ IF Debug
                                                      THEN /\ PrintT(<<"BecomeLeader", i, (currentTerm)[i]>>)
                                                           /\ pc' = [pc EXCEPT ![self] = "serverBecomeLeaderLoop"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverBecomeLeaderLoop"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           /\ UNCHANGED << state, nextIndex, 
                                                           matchIndex, leader, 
                                                           appendEntriesCh >>
                                /\ UNCHANGED << network, fd, currentTerm, 
                                                commitIndex, log, plog, 
                                                votedFor, votesResponded, 
                                                votesGranted, sm, smDomain, 
                                                leaderTimeout, reqCh, respCh, 
                                                requestVoteSrvId, 
                                                appendEntriesSrvId, 
                                                advanceCommitIndexSrvId, 
                                                becomeLeaderSrvId, idx, m, 
                                                srvId, idx0, srvId0, idx1, 
                                                srvId1, newCommitIndex, srvId2, 
                                                srvId3, leader0, req, resp, 
                                                reqIdx, timeout >>

s4(self) == serverBecomeLeaderLoop(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ (Len(reqCh)) > (0)
                                     /\ LET res00 == Head(reqCh) IN
                                          /\ reqCh' = Tail(reqCh)
                                          /\ LET yielded_reqCh0 == res00 IN
                                               /\ req' = [req EXCEPT ![self] = yielded_reqCh0]
                                               /\ reqIdx' = [reqIdx EXCEPT ![self] = (reqIdx[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                     /\ UNCHANGED <<network, resp>>
                                  \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 3502, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg10 == Head(((network)[self]).queue) IN
                                          /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                          /\ LET yielded_network20 == readMsg10 IN
                                               /\ resp' = [resp EXCEPT ![self] = yielded_network20]
                                               /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                     /\ UNCHANGED <<reqCh, req, reqIdx>>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, reqCh, req, resp, 
                                               reqIdx >>
                    /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                    nextIndex, matchIndex, log, plog, votedFor, 
                                    votesResponded, votesGranted, leader, sm, 
                                    smDomain, leaderTimeout, appendEntriesCh, 
                                    respCh, requestVoteSrvId, 
                                    appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    idx, m, srvId, idx0, srvId0, idx1, srvId1, 
                                    newCommitIndex, srvId2, srvId3, leader0, 
                                    timeout >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (leader0[self]) = (Nil)
                      THEN /\ \E srv1 \in ServerSet:
                                /\ leader0' = [leader0 EXCEPT ![self] = srv1]
                                /\ IF Debug
                                      THEN /\ PrintT(<<"ClientSndReq", self, leader0'[self], req[self]>>)
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
                                 THEN /\ PrintT(<<"ClientSndReq", self, leader0[self], req[self]>>)
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
                                reqCh, respCh, requestVoteSrvId, 
                                appendEntriesSrvId, advanceCommitIndexSrvId, 
                                becomeLeaderSrvId, idx, m, srvId, idx0, srvId0, 
                                idx1, srvId1, newCommitIndex, srvId2, srvId3, 
                                req, resp, reqIdx, timeout >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 3664, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg20 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network30 == readMsg20 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network30]
                                 /\ IF Debug
                                       THEN /\ PrintT(<<"ClientRcvResp", resp'[self]>>)
                                            /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3672, column 15.")
                                            /\ IF ((resp'[self]).msuccess) /\ ((((resp'[self]).mresponse).idx) # (reqIdx[self]))
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3677, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3681, column 19.")
                                                                  /\ respCh' = resp'[self]
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                       ELSE /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 3687, column 15.")
                                            /\ IF ((resp'[self]).msuccess) /\ ((((resp'[self]).mresponse).idx) # (reqIdx[self]))
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED << respCh, 
                                                                       leader0 >>
                                                  ELSE /\ leader0' = [leader0 EXCEPT ![self] = (resp'[self]).mleaderHint]
                                                       /\ Assert(((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse))), 
                                                                 "Failure of assertion at line 3692, column 17.")
                                                       /\ IF ~ ((resp'[self]).msuccess)
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                                  /\ UNCHANGED respCh
                                                             ELSE /\ Assert(((((resp'[self]).mresponse).idx) = (reqIdx[self])) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                            "Failure of assertion at line 3696, column 19.")
                                                                  /\ respCh' = resp'[self]
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                    \/ /\ LET yielded_fd60 == (fd)[leader0[self]] IN
                            LET yielded_network40 == Len(((network)[self]).queue) IN
                              /\ ((yielded_fd60) /\ ((yielded_network40) = (0))) \/ (timeout[self])
                              /\ leader0' = [leader0 EXCEPT ![self] = Nil]
                              /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                       /\ UNCHANGED <<network, respCh, resp>>
                 /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                 nextIndex, matchIndex, log, plog, votedFor, 
                                 votesResponded, votesGranted, leader, sm, 
                                 smDomain, leaderTimeout, appendEntriesCh, 
                                 reqCh, requestVoteSrvId, appendEntriesSrvId, 
                                 advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                 idx, m, srvId, idx0, srvId0, idx1, srvId1, 
                                 newCommitIndex, srvId2, srvId3, req, reqIdx, 
                                 timeout >>

client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: s0(self))
           \/ (\E self \in ServerRequestVoteSet: s1(self))
           \/ (\E self \in ServerAppendEntriesSet: s2(self))
           \/ (\E self \in ServerAdvanceCommitIndexSet: s3(self))
           \/ (\E self \in ServerBecomeLeaderSet: s4(self))
           \/ (\E self \in ClientSet: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(s0(self))
        /\ \A self \in ServerRequestVoteSet : WF_vars(s1(self))
        /\ \A self \in ServerAppendEntriesSet : WF_vars(s2(self))
        /\ \A self \in ServerAdvanceCommitIndexSet : WF_vars(s3(self))
        /\ \A self \in ServerBecomeLeaderSet : WF_vars(s4(self))
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
                        /\ sm[i] = sm[j]
                        /\ smDomain[i] = smDomain[j]

plogOK == \A i \in ServerSet: log[i] = plog[i]

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

ClientRcvResp(i) == pc[i] = "rcvResp" ~> pc[i] = "clientLoop"
ClientsOK == (\E i \in ServerSet: state[i] = Leader) => \A i \in ClientSet: ClientRcvResp(i)

\* Expected this to be violated if NumServers > 1,
\* but TLC doesn't report violation in case of NumServers = 2 because 
\* of using temporal properties and state constraints at the same time. 
\* TLC reports violation when NumServers = 3.
ElectionLiveness == <>(\E i \in ServerSet: state[i] = Leader)

=============================================================================
