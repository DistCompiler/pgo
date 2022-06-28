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
CONSTANT Debug

CONSTANT NumServers

CONSTANT BufferSize

CONSTANT MaxTerm
CONSTANT MaxCommitIndex

CONSTANT MaxNodeFail

CONSTANT LogConcat
CONSTANT LogPop

CONSTANT LeaderTimeoutReset

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

        ProposeMessage == "prm"
        AcceptMessage  == "acm"

        Key1   == "key1"
        Key2   == "key2"
        Value1 == "value1"

        LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

        ServerNetListenerSet                == (0*NumServers+1)..(1*NumServers)
        ServerPropChListenerSet             == (1*NumServers+1)..(2*NumServers) 
        ServerRequestVoteSet                == (2*NumServers+1)..(3*NumServers)
        ServerAppendEntriesSet              == (3*NumServers+1)..(4*NumServers)
        ServerAdvanceCommitIndexSet         == (4*NumServers+1)..(5*NumServers)
        ServerBecomeLeaderSet               == (5*NumServers+1)..(6*NumServers)
        ServerFollowerAdvanceCommitIndexSet == (6*NumServers+1)..(7*NumServers)

        ServerCrasherSet == IF ExploreFail 
                            THEN (7*NumServers+1)..(7*NumServers+MaxNodeFail)
                            ELSE {}

        NodeSet   == ServerSet

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
            await Len($variable) < BufferSize;
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

    archetype AServerNetListener(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
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

                \* HandleAppendEntriesRequest
                with (
                    i = self, j = m.msource,
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

                            fAdvCommitIdxCh[i] := m;
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
                            nextIndex[i] := [nextIndex[i] EXCEPT ![j] = m.mmatchIndex + 1];
                            matchIndex[i] := [matchIndex[i] EXCEPT ![j] = m.mmatchIndex];
                        } else {
                            nextIndex[i] := [nextIndex[i] EXCEPT ![j] = Max({nextIndex[i][j]-1, 1})];
                        };
                    };
                };
            } else if (m.mtype = ProposeMessage) {
                \* HandleProposeMessage

                with (i = self) {
                    debug(<<"HandleProposeMessage", i, currentTerm[i], state[i], leader[i]>>);

                    if (state[i] = Leader) {
                        with (entry = [term |-> currentTerm[i],
                                       cmd  |-> m.mcmd]
                        ) {
                            log[i]  := Append(log[i], entry);
                            plog[i] := [cmd |-> LogConcat, entries |-> <<entry>>];

                            \* commented out for perf optimization
                            \* appendEntriesCh := TRUE;
                        };
                    } else if (leader[i] /= Nil) {
                        with (j = leader[i]) {
                            Send(net, j, fd, [
                                mtype   |-> ProposeMessage,
                                mcmd    |-> m.mcmd,
                                msource |-> i,
                                mdest   |-> j
                            ]);
                        };
                    };
                };
            };
        };
    }

    archetype AServerPropChListener(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
    variables
        idx = 1,
        m;
    {
    serverLoop:
        while (TRUE) {
            \* checkFail(self, netEnabled);

            with (i = srvId) {
                m := propCh[i];
                debug(<<"ReceiveProposeMessage", i, currentTerm[i], state[i], leader[i], m>>);
            };

        handleMsg:
            \* checkFail(self, netEnabled);

            \* HandleProposeMessage
            assert m.mtype = ProposeMessage;

            with (i = srvId) {
                debug(<<"HandleProposeMessage", i, currentTerm[i], state[i], leader[i]>>);

                if (state[i] = Leader) {
                    with (entry = [term |-> currentTerm[i],
                                    cmd  |-> m.mcmd]
                    ) {
                        log[i]  := Append(log[i], entry);
                        plog[i] := [cmd |-> LogConcat, entries |-> <<entry>>];

                        \* commented out for perf optimization
                        \* appendEntriesCh := TRUE;
                    };
                } else if (leader[i] /= Nil) {
                    with (j = leader[i]) {
                        Send(net, j, fd, [
                            mtype   |-> ProposeMessage,
                            mcmd    |-> m.mcmd,
                            msource |-> i,
                            mdest   |-> j
                        ]);
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
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
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
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
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
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
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
                    cmd   = entry.cmd
                ) {
                    debug(<<"ServerAccept", i, cmd>>);
                    acctCh[i] := [
                        mtype |-> AcceptMessage,
                        mcmd  |-> cmd
                    ];
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
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
    {
    serverBecomeLeaderLoop:
        while (becomeLeaderCh[srvId]) {
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

    archetype AServerFollowerAdvanceCommitIndex(
        srvId,
        ref net[_], ref netLen[_], ref netEnabled[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        \* added by Shayan
        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
    variable m;
    {
    serverFollowerAdvanceCommitIndexLoop:
        while (TRUE) {
            m := fAdvCommitIdxCh[srvId];

        acctLoop:
            while (commitIndex[srvId] < m.mcommitIndex) {
                commitIndex[srvId] := commitIndex[srvId] + 1;
                with (
                    i = srvId,
                    k = commitIndex[i],
                    entry = log[i][k],
                    cmd   = entry.cmd
                ) {
                    debug(<<"ServerAccept", i, cmd>>);
                    acctCh[i] := [
                        mtype |-> AcceptMessage,
                        mcmd  |-> cmd
                    ];
                };
            };
        };
    }

    archetype AServerCrasher(srvId, ref netEnabled[_], ref fd[_]) {
    serverCrash:
        netEnabled[srvId] := FALSE;
    fdUpdate:
        fd[srvId] := TRUE;
    }

    archetype AProposer(ref propCh[_]) {
    sndReq:
        propCh[1] := [
            mtype |-> ProposeMessage,
            mcmd  |-> [data |-> "hello"]
        ];
    }

    variables
        network = [i \in NodeSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd      = [i \in ServerSet |-> FALSE];

        state       = [i \in ServerSet |-> Follower];
        \* state       = [i \in ServerSet |-> IF i = 1 THEN Leader ELSE Follower];
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
        \* leader = [i \in ServerSet |-> 1];

        propCh = [i \in ServerSet |-> <<>>];
        acctCh = [i \in ServerSet |-> <<>>];

        leaderTimeout   = TRUE;
        appendEntriesCh = TRUE;
        becomeLeaderCh  = [i \in ServerSet |-> 
            IF NumServers > 1 
            THEN <<>>
            ELSE <<TRUE>>
        ];
        fAdvCommitIdxCh = [i \in ServerSet |-> <<>>];

        netListenerSrvId        = [i \in ServerNetListenerSet                |-> i - 0*NumServers];
        propChListenerSrvId     = [i \in ServerPropChListenerSet             |-> i - 1*NumServers];
        requestVoteSrvId        = [i \in ServerRequestVoteSet                |-> i - 2*NumServers];
        appendEntriesSrvId      = [i \in ServerAppendEntriesSet              |-> i - 3*NumServers];
        advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet         |-> i - 4*NumServers];
        becomeLeaderSrvId       = [i \in ServerBecomeLeaderSet               |-> i - 5*NumServers];
        fAdvCommitSrvId         = [i \in ServerFollowerAdvanceCommitIndexSet |-> i - 6*NumServers];
        crasherSrvId            = [i \in ServerCrasherSet                    |-> i - 7*NumServers];

    fair process (s0 \in ServerNetListenerSet) == instance AServerNetListener(
        netListenerSrvId[s0],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s1 \in ServerPropChListenerSet) == instance AServerPropChListener(
        propChListenerSrvId[s1],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s2 \in ServerRequestVoteSet) == instance AServerRequestVote(
        requestVoteSrvId[s2],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s3 \in ServerAppendEntriesSet) == instance AServerAppendEntries(
        appendEntriesSrvId[s3],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s4 \in ServerAdvanceCommitIndexSet) == instance AServerAdvanceCommitIndex(
        advanceCommitIndexSrvId[s4],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (s5 \in ServerBecomeLeaderSet) == instance AServerBecomeLeader(
        becomeLeaderSrvId[s5],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process(s6 \in ServerFollowerAdvanceCommitIndexSet) == instance AServerFollowerAdvanceCommitIndex(
        fAdvCommitSrvId[s6],
        ref network[_], ref network[_], ref network[_], ref fd[_],
        ref state[_], ref currentTerm[_],
        ref log[_], ref plog[_],
        ref commitIndex[_], ref nextIndex[_], ref matchIndex[_],
        ref votedFor[_], ref votesResponded[_], ref votesGranted[_],

        ref leader[_],
        ref propCh[_], ref acctCh[_],
        ref leaderTimeout,
        ref appendEntriesCh, ref becomeLeaderCh[_], ref fAdvCommitIdxCh[_]
    )
        mapping @2[_]  via ReliableFIFOLink
        mapping @3[_]  via NetworkBufferLength
        mapping @4[_]  via NetworkToggle
        mapping @5[_]  via PerfectFD
        mapping @9[_]  via PersistentLog
        mapping @17[_] via Channel
        mapping @18[_] via Channel
        mapping @21[_] via Channel
        mapping @22[_] via Channel;

    fair process (crasher \in ServerCrasherSet) == instance AServerCrasher(
        crasherSrvId[crasher],
        ref network[_], ref fd[_]
    )
        mapping @2[_] via NetworkToggle
        mapping @3[_] via PerfectFD;
    
    fair process (proposer = 0) == instance AProposer(ref propCh[_])
        mapping @1[_] via Channel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm raft {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; state = [i \in ServerSet |-> Follower]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]; log = [i \in ServerSet |-> <<>>]; plog = [i \in ServerSet |-> <<>>]; votedFor = [i \in ServerSet |-> Nil]; votesResponded = [i \in ServerSet |-> {}]; votesGranted = [i \in ServerSet |-> {}]; leader = [i \in ServerSet |-> Nil]; propCh = [i \in ServerSet |-> <<>>]; acctCh = [i \in ServerSet |-> <<>>]; leaderTimeout = TRUE; appendEntriesCh = TRUE; becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]; fAdvCommitIdxCh = [i \in ServerSet |-> <<>>]; netListenerSrvId = [i \in ServerNetListenerSet |-> (i) - ((0) * (NumServers))]; propChListenerSrvId = [i \in ServerPropChListenerSet |-> (i) - ((1) * (NumServers))]; requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((2) * (NumServers))]; appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((3) * (NumServers))]; advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((4) * (NumServers))]; becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((5) * (NumServers))]; fAdvCommitSrvId = [i \in ServerFollowerAdvanceCommitIndexSet |-> (i) - ((6) * (NumServers))]; crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((7) * (NumServers))];
  define{
    Follower == "follower"
    Candidate == "candidate"
    Leader == "leader"
    RequestVoteRequest == "rvq"
    RequestVoteResponse == "rvp"
    AppendEntriesRequest == "apq"
    AppendEntriesResponse == "app"
    ProposeMessage == "prm"
    AcceptMessage == "acm"
    Key1 == "key1"
    Key2 == "key2"
    Value1 == "value1"
    LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
    ServerNetListenerSet == (((0) * (NumServers)) + (1)) .. ((1) * (NumServers))
    ServerPropChListenerSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
    ServerRequestVoteSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
    ServerAppendEntriesSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
    ServerAdvanceCommitIndexSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
    ServerBecomeLeaderSet == (((5) * (NumServers)) + (1)) .. ((6) * (NumServers))
    ServerFollowerAdvanceCommitIndexSet == (((6) * (NumServers)) + (1)) .. ((7) * (NumServers))
    ServerCrasherSet == IF ExploreFail THEN (((7) * (NumServers)) + (1)) .. (((7) * (NumServers)) + (MaxNodeFail)) ELSE {}
    NodeSet == ServerSet
    KeySet == {}
  }
  
  fair process (s0 \in ServerNetListenerSet)
    variables idx = 1; m; srvId = (netListenerSrvId)[self];
  {
    serverLoop:
      if (TRUE) {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg00 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network1 = readMsg00) {
            m := yielded_network1;
            assert ((m).mdest) = (self);
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
                  with (value17 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]];
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      goto serverLoop;
                    } else {
                      goto serverLoop;
                    };
                  };
                } or {
                  with (yielded_fd6 = (fd)[j]) {
                    await yielded_fd6;
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
                  with (value18 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]];
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
                  with (yielded_fd7 = (fd)[j]) {
                    await yielded_fd7;
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
                with (yielded_fd8 = (fd)[j]) {
                  await yielded_fd8;
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
                with (value20 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]];
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
                    with (value00 = TRUE) {
                      await (Len((becomeLeaderCh)[i])) < (BufferSize);
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value00)];
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
                    with (value01 = TRUE) {
                      await (Len((becomeLeaderCh)[i])) < (BufferSize);
                      becomeLeaderCh := [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value01)];
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
                with (
                  leader1 = [leader EXCEPT ![self] = Nil], 
                  i = self, 
                  j = (m).msource, 
                  logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len((log)[i])))) /\ (((m).mprevLogTerm) = ((((log)[i])[(m).mprevLogIndex]).term)))
                ) {
                  assert ((m).mterm) <= ((currentTerm)[i]);
                  if (((m).mterm) = ((currentTerm)[i])) {
                    leader := [leader1 EXCEPT ![i] = (m).msource];
                    leaderTimeout := LeaderTimeoutReset;
                    if ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Candidate))) {
                      state := [state1 EXCEPT ![i] = Follower];
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value110 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value110), enabled |-> ((network)[j]).enabled]];
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
                        with (
                          index = ((m).mprevLogIndex) + (1), 
                          value21 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                        ) {
                          if (((value21).cmd) = (LogConcat)) {
                            with (
                              plog8 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value21).entries)], 
                              log8 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value30 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value30).cmd) = (LogConcat)) {
                                plog := [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value30).entries)];
                                log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value40 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value40)];
                                  either {
                                    with (value50 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd10 = (fd)[j]) {
                                      await yielded_fd10;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value30).cmd) = (LogPop)) {
                                  plog := [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - ((value30).cnt))];
                                  log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value41 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value41)];
                                    either {
                                      with (value51 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log8 EXCEPT ![i] = ((log8)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value42 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value42)];
                                    either {
                                      with (value52 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]];
                                        plog := plog8;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd12 = (fd)[j]) {
                                        await yielded_fd12;
                                        plog := plog8;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              };
                            };
                          } else {
                            if (((value21).cmd) = (LogPop)) {
                              with (
                                plog9 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value21).cnt))], 
                                log9 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value31 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value31).cmd) = (LogConcat)) {
                                  plog := [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value31).entries)];
                                  log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value43 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value43)];
                                    either {
                                      with (value53 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd13 = (fd)[j]) {
                                        await yielded_fd13;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value31).cmd) = (LogPop)) {
                                    plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - ((value31).cnt))];
                                    log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value44 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value44)];
                                      either {
                                        with (value54 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log9 EXCEPT ![i] = ((log9)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value45 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value45)];
                                      either {
                                        with (value55 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]];
                                          plog := plog9;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd15 = (fd)[j]) {
                                          await yielded_fd15;
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
                                log10 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value32 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value32).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)];
                                  log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value46 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value46)];
                                    either {
                                      with (value56 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]];
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
                                  if (((value32).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value32).cnt))];
                                    log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value47 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value47)];
                                      either {
                                        with (value57 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log10 EXCEPT ![i] = ((log10)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value48 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value48)];
                                      either {
                                        with (value58 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd18 = (fd)[j]) {
                                          await yielded_fd18;
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
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value111 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value111), enabled |-> ((network)[j]).enabled]];
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
                        with (
                          index = ((m).mprevLogIndex) + (1), 
                          value22 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                        ) {
                          if (((value22).cmd) = (LogConcat)) {
                            with (
                              plog10 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value22).entries)], 
                              log11 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value33 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value33).cmd) = (LogConcat)) {
                                plog := [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value33).entries)];
                                log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value49 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value49)];
                                  either {
                                    with (value59 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]];
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd19 = (fd)[j]) {
                                      await yielded_fd19;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value33).cmd) = (LogPop)) {
                                  plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - ((value33).cnt))];
                                  log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value410 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value410)];
                                    either {
                                      with (value510 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log11 EXCEPT ![i] = ((log11)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value411 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value411)];
                                    either {
                                      with (value511 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]];
                                        plog := plog10;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd111 = (fd)[j]) {
                                        await yielded_fd111;
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
                            if (((value22).cmd) = (LogPop)) {
                              with (
                                plog11 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value22).cnt))], 
                                log12 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value34 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value34).cmd) = (LogConcat)) {
                                  plog := [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value34).entries)];
                                  log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value412 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value412)];
                                    either {
                                      with (value512 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd112 = (fd)[j]) {
                                        await yielded_fd112;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value34).cmd) = (LogPop)) {
                                    plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - ((value34).cnt))];
                                    log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value413 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value413)];
                                      either {
                                        with (value513 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log12 EXCEPT ![i] = ((log12)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value414 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value414)];
                                      either {
                                        with (value514 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]];
                                          plog := plog11;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd114 = (fd)[j]) {
                                          await yielded_fd114;
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
                                log13 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value35 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value35).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value35).entries)];
                                  log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value415 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value415)];
                                    either {
                                      with (value515 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]];
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd115 = (fd)[j]) {
                                        await yielded_fd115;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value35).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value35).cnt))];
                                    log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value416 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value416)];
                                      either {
                                        with (value516 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log13 EXCEPT ![i] = ((log13)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value417 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value417)];
                                      either {
                                        with (value517 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]];
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
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    };
                  } else {
                    if ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Candidate))) {
                      state := [state1 EXCEPT ![i] = Follower];
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value112 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value112), enabled |-> ((network)[j]).enabled]];
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
                        assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m).mprevLogIndex) + (1), 
                          value23 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                        ) {
                          if (((value23).cmd) = (LogConcat)) {
                            with (
                              plog12 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value23).entries)], 
                              log14 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value36 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value36).cmd) = (LogConcat)) {
                                plog := [plog12 EXCEPT ![i] = ((plog12)[i]) \o ((value36).entries)];
                                log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value418 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value418)];
                                  either {
                                    with (value518 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]];
                                      leader := leader1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd118 = (fd)[j]) {
                                      await yielded_fd118;
                                      leader := leader1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value36).cmd) = (LogPop)) {
                                  plog := [plog12 EXCEPT ![i] = SubSeq((plog12)[i], 1, (Len((plog12)[i])) - ((value36).cnt))];
                                  log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value419 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value419)];
                                    either {
                                      with (value519 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log14 EXCEPT ![i] = ((log14)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value420 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value420)];
                                    either {
                                      with (value520 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]];
                                        plog := plog12;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd120 = (fd)[j]) {
                                        await yielded_fd120;
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
                            if (((value23).cmd) = (LogPop)) {
                              with (
                                plog13 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value23).cnt))], 
                                log15 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value37 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value37).cmd) = (LogConcat)) {
                                  plog := [plog13 EXCEPT ![i] = ((plog13)[i]) \o ((value37).entries)];
                                  log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value421 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value421)];
                                    either {
                                      with (value521 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd121 = (fd)[j]) {
                                        await yielded_fd121;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value37).cmd) = (LogPop)) {
                                    plog := [plog13 EXCEPT ![i] = SubSeq((plog13)[i], 1, (Len((plog13)[i])) - ((value37).cnt))];
                                    log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value422 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value422)];
                                      either {
                                        with (value522 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log15 EXCEPT ![i] = ((log15)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value423 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value423)];
                                      either {
                                        with (value523 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]];
                                          plog := plog13;
                                          leader := leader1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd123 = (fd)[j]) {
                                          await yielded_fd123;
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
                                log16 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value38 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value38).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value38).entries)];
                                  log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value424 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value424)];
                                    either {
                                      with (value524 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd124 = (fd)[j]) {
                                        await yielded_fd124;
                                        leader := leader1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value38).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value38).cnt))];
                                    log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value425 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value425)];
                                      either {
                                        with (value525 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log16 EXCEPT ![i] = ((log16)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value426 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value426)];
                                      either {
                                        with (value526 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]];
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
                                  };
                                };
                              };
                            };
                          };
                        };
                      };
                    } else {
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value113 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value113), enabled |-> ((network)[j]).enabled]];
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
                        assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK);
                        with (
                          index = ((m).mprevLogIndex) + (1), 
                          value24 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                        ) {
                          if (((value24).cmd) = (LogConcat)) {
                            with (
                              plog14 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value24).entries)], 
                              log17 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value39 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value39).cmd) = (LogConcat)) {
                                plog := [plog14 EXCEPT ![i] = ((plog14)[i]) \o ((value39).entries)];
                                log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value427 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value427)];
                                  either {
                                    with (value527 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]];
                                      leader := leader1;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd127 = (fd)[j]) {
                                      await yielded_fd127;
                                      leader := leader1;
                                      state := state1;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value39).cmd) = (LogPop)) {
                                  plog := [plog14 EXCEPT ![i] = SubSeq((plog14)[i], 1, (Len((plog14)[i])) - ((value39).cnt))];
                                  log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value428 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value428)];
                                    either {
                                      with (value528 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log17 EXCEPT ![i] = ((log17)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value429 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value429)];
                                    either {
                                      with (value529 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]];
                                        plog := plog14;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd129 = (fd)[j]) {
                                        await yielded_fd129;
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
                            if (((value24).cmd) = (LogPop)) {
                              with (
                                plog15 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value24).cnt))], 
                                log18 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value310 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value310).cmd) = (LogConcat)) {
                                  plog := [plog15 EXCEPT ![i] = ((plog15)[i]) \o ((value310).entries)];
                                  log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value430 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value430)];
                                    either {
                                      with (value530 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd130 = (fd)[j]) {
                                        await yielded_fd130;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value310).cmd) = (LogPop)) {
                                    plog := [plog15 EXCEPT ![i] = SubSeq((plog15)[i], 1, (Len((plog15)[i])) - ((value310).cnt))];
                                    log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value431 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value431)];
                                      either {
                                        with (value531 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log18 EXCEPT ![i] = ((log18)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value432 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value432)];
                                      either {
                                        with (value532 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]];
                                          plog := plog15;
                                          leader := leader1;
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd132 = (fd)[j]) {
                                          await yielded_fd132;
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
                                log19 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                                value311 = [cmd |-> LogConcat, entries |-> (m).mentries]
                              ) {
                                if (((value311).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)];
                                  log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value433 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value433)];
                                    either {
                                      with (value533 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]];
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd133 = (fd)[j]) {
                                        await yielded_fd133;
                                        leader := leader1;
                                        state := state1;
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                } else {
                                  if (((value311).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value311).cnt))];
                                    log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value434 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value434)];
                                      either {
                                        with (value534 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]];
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
                                    log := [log19 EXCEPT ![i] = ((log19)[i]) \o ((m).mentries)];
                                    assert ((m).mcommitIndex) <= (Len((log)[i]));
                                    with (value435 = m) {
                                      await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value435)];
                                      either {
                                        with (value535 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]];
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
                i = self, 
                j = (m).msource, 
                logOK = (((m).mprevLogIndex) = (0)) \/ (((((m).mprevLogIndex) > (0)) /\ (((m).mprevLogIndex) <= (Len((log)[i])))) /\ (((m).mprevLogTerm) = ((((log)[i])[(m).mprevLogIndex]).term)))
              ) {
                assert ((m).mterm) <= ((currentTerm)[i]);
                if (((m).mterm) = ((currentTerm)[i])) {
                  leader := [leader EXCEPT ![i] = (m).msource];
                  leaderTimeout := LeaderTimeoutReset;
                  if ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))) {
                    state := [state EXCEPT ![i] = Follower];
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value114 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value114), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd04 = (fd)[j]) {
                          await yielded_fd04;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m).mprevLogIndex) + (1), 
                        value25 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                      ) {
                        if (((value25).cmd) = (LogConcat)) {
                          with (
                            plog16 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value25).entries)], 
                            log20 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                            value312 = [cmd |-> LogConcat, entries |-> (m).mentries]
                          ) {
                            if (((value312).cmd) = (LogConcat)) {
                              plog := [plog16 EXCEPT ![i] = ((plog16)[i]) \o ((value312).entries)];
                              log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m).mentries)];
                              assert ((m).mcommitIndex) <= (Len((log)[i]));
                              with (value436 = m) {
                                await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value436)];
                                either {
                                  with (value536 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]];
                                    goto serverLoop;
                                  };
                                } or {
                                  with (yielded_fd136 = (fd)[j]) {
                                    await yielded_fd136;
                                    goto serverLoop;
                                  };
                                };
                              };
                            } else {
                              if (((value312).cmd) = (LogPop)) {
                                plog := [plog16 EXCEPT ![i] = SubSeq((plog16)[i], 1, (Len((plog16)[i])) - ((value312).cnt))];
                                log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value437 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value437)];
                                  either {
                                    with (value537 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]];
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
                                log := [log20 EXCEPT ![i] = ((log20)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value438 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value438)];
                                  either {
                                    with (value538 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]];
                                      plog := plog16;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd138 = (fd)[j]) {
                                      await yielded_fd138;
                                      plog := plog16;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value25).cmd) = (LogPop)) {
                            with (
                              plog17 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value25).cnt))], 
                              log21 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value313 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value313).cmd) = (LogConcat)) {
                                plog := [plog17 EXCEPT ![i] = ((plog17)[i]) \o ((value313).entries)];
                                log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value439 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value439)];
                                  either {
                                    with (value539 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd139 = (fd)[j]) {
                                      await yielded_fd139;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value313).cmd) = (LogPop)) {
                                  plog := [plog17 EXCEPT ![i] = SubSeq((plog17)[i], 1, (Len((plog17)[i])) - ((value313).cnt))];
                                  log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value440 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value440)];
                                    either {
                                      with (value540 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log21 EXCEPT ![i] = ((log21)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value441 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value441)];
                                    either {
                                      with (value541 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]];
                                        plog := plog17;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd141 = (fd)[j]) {
                                        await yielded_fd141;
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
                              log22 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value314 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value314).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)];
                                log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value442 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value442)];
                                  either {
                                    with (value542 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]];
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
                                if (((value314).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value314).cnt))];
                                  log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value443 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value443)];
                                    either {
                                      with (value543 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log22 EXCEPT ![i] = ((log22)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value444 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value444)];
                                    either {
                                      with (value544 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd144 = (fd)[j]) {
                                        await yielded_fd144;
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
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value115 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value115), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd05 = (fd)[j]) {
                          await yielded_fd05;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m).mprevLogIndex) + (1), 
                        value26 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                      ) {
                        if (((value26).cmd) = (LogConcat)) {
                          with (
                            plog18 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value26).entries)], 
                            log23 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                            value315 = [cmd |-> LogConcat, entries |-> (m).mentries]
                          ) {
                            if (((value315).cmd) = (LogConcat)) {
                              plog := [plog18 EXCEPT ![i] = ((plog18)[i]) \o ((value315).entries)];
                              log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m).mentries)];
                              assert ((m).mcommitIndex) <= (Len((log)[i]));
                              with (value445 = m) {
                                await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value445)];
                                either {
                                  with (value545 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]];
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
                              if (((value315).cmd) = (LogPop)) {
                                plog := [plog18 EXCEPT ![i] = SubSeq((plog18)[i], 1, (Len((plog18)[i])) - ((value315).cnt))];
                                log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value446 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value446)];
                                  either {
                                    with (value546 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]];
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
                                log := [log23 EXCEPT ![i] = ((log23)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value447 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value447)];
                                  either {
                                    with (value547 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]];
                                      plog := plog18;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd147 = (fd)[j]) {
                                      await yielded_fd147;
                                      plog := plog18;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value26).cmd) = (LogPop)) {
                            with (
                              plog19 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value26).cnt))], 
                              log24 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value316 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value316).cmd) = (LogConcat)) {
                                plog := [plog19 EXCEPT ![i] = ((plog19)[i]) \o ((value316).entries)];
                                log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value448 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value448)];
                                  either {
                                    with (value548 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]];
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
                                if (((value316).cmd) = (LogPop)) {
                                  plog := [plog19 EXCEPT ![i] = SubSeq((plog19)[i], 1, (Len((plog19)[i])) - ((value316).cnt))];
                                  log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value449 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value449)];
                                    either {
                                      with (value549 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log24 EXCEPT ![i] = ((log24)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value450 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value450)];
                                    either {
                                      with (value550 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]];
                                        plog := plog19;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd150 = (fd)[j]) {
                                        await yielded_fd150;
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
                              log25 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value317 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value317).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value317).entries)];
                                log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value451 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value451)];
                                  either {
                                    with (value551 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd151 = (fd)[j]) {
                                      await yielded_fd151;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value317).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value317).cnt))];
                                  log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value452 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value452)];
                                    either {
                                      with (value552 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log25 EXCEPT ![i] = ((log25)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value453 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value453)];
                                    either {
                                      with (value553 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd153 = (fd)[j]) {
                                        await yielded_fd153;
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
                  if ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))) {
                    state := [state EXCEPT ![i] = Follower];
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value116 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value116), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd06 = (fd)[j]) {
                          await yielded_fd06;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m).mprevLogIndex) + (1), 
                        value27 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                      ) {
                        if (((value27).cmd) = (LogConcat)) {
                          with (
                            plog20 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value27).entries)], 
                            log26 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                            value318 = [cmd |-> LogConcat, entries |-> (m).mentries]
                          ) {
                            if (((value318).cmd) = (LogConcat)) {
                              plog := [plog20 EXCEPT ![i] = ((plog20)[i]) \o ((value318).entries)];
                              log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m).mentries)];
                              assert ((m).mcommitIndex) <= (Len((log)[i]));
                              with (value454 = m) {
                                await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value454)];
                                either {
                                  with (value554 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]];
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
                              if (((value318).cmd) = (LogPop)) {
                                plog := [plog20 EXCEPT ![i] = SubSeq((plog20)[i], 1, (Len((plog20)[i])) - ((value318).cnt))];
                                log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value455 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value455)];
                                  either {
                                    with (value555 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]];
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
                                log := [log26 EXCEPT ![i] = ((log26)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value456 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value456)];
                                  either {
                                    with (value556 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]];
                                      plog := plog20;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd156 = (fd)[j]) {
                                      await yielded_fd156;
                                      plog := plog20;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value27).cmd) = (LogPop)) {
                            with (
                              plog21 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value27).cnt))], 
                              log27 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value319 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value319).cmd) = (LogConcat)) {
                                plog := [plog21 EXCEPT ![i] = ((plog21)[i]) \o ((value319).entries)];
                                log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value457 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value457)];
                                  either {
                                    with (value557 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]];
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
                                if (((value319).cmd) = (LogPop)) {
                                  plog := [plog21 EXCEPT ![i] = SubSeq((plog21)[i], 1, (Len((plog21)[i])) - ((value319).cnt))];
                                  log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value458 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value458)];
                                    either {
                                      with (value558 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log27 EXCEPT ![i] = ((log27)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value459 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value459)];
                                    either {
                                      with (value559 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]];
                                        plog := plog21;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd159 = (fd)[j]) {
                                        await yielded_fd159;
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
                              log28 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value320 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value320).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value320).entries)];
                                log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value460 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value460)];
                                  either {
                                    with (value560 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd160 = (fd)[j]) {
                                      await yielded_fd160;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value320).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value320).cnt))];
                                  log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value461 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value461)];
                                    either {
                                      with (value561 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log28 EXCEPT ![i] = ((log28)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value462 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value462)];
                                    either {
                                      with (value562 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd162 = (fd)[j]) {
                                        await yielded_fd162;
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
                    if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                      either {
                        with (value117 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                          await ((network)[j]).enabled;
                          await (Len(((network)[j]).queue)) < (BufferSize);
                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value117), enabled |-> ((network)[j]).enabled]];
                          goto serverLoop;
                        };
                      } or {
                        with (yielded_fd07 = (fd)[j]) {
                          await yielded_fd07;
                          goto serverLoop;
                        };
                      };
                    } else {
                      assert ((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK);
                      with (
                        index = ((m).mprevLogIndex) + (1), 
                        value28 = [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m).mprevLogIndex)]
                      ) {
                        if (((value28).cmd) = (LogConcat)) {
                          with (
                            plog22 = [plog EXCEPT ![i] = ((plog)[i]) \o ((value28).entries)], 
                            log29 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                            value321 = [cmd |-> LogConcat, entries |-> (m).mentries]
                          ) {
                            if (((value321).cmd) = (LogConcat)) {
                              plog := [plog22 EXCEPT ![i] = ((plog22)[i]) \o ((value321).entries)];
                              log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m).mentries)];
                              assert ((m).mcommitIndex) <= (Len((log)[i]));
                              with (value463 = m) {
                                await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value463)];
                                either {
                                  with (value563 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                    await ((network)[j]).enabled;
                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]];
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
                              if (((value321).cmd) = (LogPop)) {
                                plog := [plog22 EXCEPT ![i] = SubSeq((plog22)[i], 1, (Len((plog22)[i])) - ((value321).cnt))];
                                log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value464 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value464)];
                                  either {
                                    with (value564 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value564), enabled |-> ((network)[j]).enabled]];
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
                                log := [log29 EXCEPT ![i] = ((log29)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value465 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value465)];
                                  either {
                                    with (value565 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value565), enabled |-> ((network)[j]).enabled]];
                                      plog := plog22;
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd165 = (fd)[j]) {
                                      await yielded_fd165;
                                      plog := plog22;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              };
                            };
                          };
                        } else {
                          if (((value28).cmd) = (LogPop)) {
                            with (
                              plog23 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value28).cnt))], 
                              log30 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value322 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value322).cmd) = (LogConcat)) {
                                plog := [plog23 EXCEPT ![i] = ((plog23)[i]) \o ((value322).entries)];
                                log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value466 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value466)];
                                  either {
                                    with (value566 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value566), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd166 = (fd)[j]) {
                                      await yielded_fd166;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value322).cmd) = (LogPop)) {
                                  plog := [plog23 EXCEPT ![i] = SubSeq((plog23)[i], 1, (Len((plog23)[i])) - ((value322).cnt))];
                                  log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value467 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value467)];
                                    either {
                                      with (value567 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value567), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log30 EXCEPT ![i] = ((log30)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value468 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value468)];
                                    either {
                                      with (value568 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value568), enabled |-> ((network)[j]).enabled]];
                                        plog := plog23;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd168 = (fd)[j]) {
                                        await yielded_fd168;
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
                              log31 = [log EXCEPT ![i] = SubSeq((log)[i], 1, (m).mprevLogIndex)], 
                              value323 = [cmd |-> LogConcat, entries |-> (m).mentries]
                            ) {
                              if (((value323).cmd) = (LogConcat)) {
                                plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value323).entries)];
                                log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m).mentries)];
                                assert ((m).mcommitIndex) <= (Len((log)[i]));
                                with (value469 = m) {
                                  await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value469)];
                                  either {
                                    with (value569 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value569), enabled |-> ((network)[j]).enabled]];
                                      goto serverLoop;
                                    };
                                  } or {
                                    with (yielded_fd169 = (fd)[j]) {
                                      await yielded_fd169;
                                      goto serverLoop;
                                    };
                                  };
                                };
                              } else {
                                if (((value323).cmd) = (LogPop)) {
                                  plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value323).cnt))];
                                  log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value470 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value470)];
                                    either {
                                      with (value570 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value570), enabled |-> ((network)[j]).enabled]];
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
                                  log := [log31 EXCEPT ![i] = ((log31)[i]) \o ((m).mentries)];
                                  assert ((m).mcommitIndex) <= (Len((log)[i]));
                                  with (value471 = m) {
                                    await (Len((fAdvCommitIdxCh)[i])) < (BufferSize);
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value471)];
                                    either {
                                      with (value571 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value571), enabled |-> ((network)[j]).enabled]];
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd171 = (fd)[j]) {
                                        await yielded_fd171;
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
              if (((m).mtype) = (ProposeMessage)) {
                with (i = self) {
                  if (Debug) {
                    print <<"HandleProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i]>>;
                    if (((state)[i]) = (Leader)) {
                      with (entry = [term |-> (currentTerm)[i], cmd |-> (m).mcmd]) {
                        log := [log EXCEPT ![i] = Append((log)[i], entry)];
                        with (value60 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                          if (((value60).cmd) = (LogConcat)) {
                            plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value60).entries)];
                            goto serverLoop;
                          } else {
                            if (((value60).cmd) = (LogPop)) {
                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value60).cnt))];
                              goto serverLoop;
                            } else {
                              goto serverLoop;
                            };
                          };
                        };
                      };
                    } else {
                      if (((leader)[i]) # (Nil)) {
                        with (j = (leader)[i]) {
                          either {
                            with (value70 = [mtype |-> ProposeMessage, mcmd |-> (m).mcmd, msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value70), enabled |-> ((network)[j]).enabled]];
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
                    };
                  } else {
                    if (((state)[i]) = (Leader)) {
                      with (entry = [term |-> (currentTerm)[i], cmd |-> (m).mcmd]) {
                        log := [log EXCEPT ![i] = Append((log)[i], entry)];
                        with (value61 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                          if (((value61).cmd) = (LogConcat)) {
                            plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value61).entries)];
                            goto serverLoop;
                          } else {
                            if (((value61).cmd) = (LogPop)) {
                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value61).cnt))];
                              goto serverLoop;
                            } else {
                              goto serverLoop;
                            };
                          };
                        };
                      };
                    } else {
                      if (((leader)[i]) # (Nil)) {
                        with (j = (leader)[i]) {
                          either {
                            with (value71 = [mtype |-> ProposeMessage, mcmd |-> (m).mcmd, msource |-> i, mdest |-> j]) {
                              await ((network)[j]).enabled;
                              await (Len(((network)[j]).queue)) < (BufferSize);
                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value71), enabled |-> ((network)[j]).enabled]];
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
  
  fair process (s1 \in ServerPropChListenerSet)
    variables idx0 = 1; m0; srvId0 = (propChListenerSrvId)[self];
  {
    serverLoop:
      if (TRUE) {
        with (i = srvId0) {
          await (Len((propCh)[i])) > (0);
          with (res00 = Head((propCh)[i])) {
            propCh := [propCh EXCEPT ![i] = Tail((propCh)[i])];
            with (yielded_propCh0 = res00) {
              m0 := yielded_propCh0;
              if (Debug) {
                print <<"ReceiveProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i], m0>>;
                goto handleMsg;
              } else {
                goto handleMsg;
              };
            };
          };
        };
      } else {
        goto Done;
      };
    handleMsg:
      assert ((m0).mtype) = (ProposeMessage);
      with (i = srvId0) {
        if (Debug) {
          print <<"HandleProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i]>>;
          if (((state)[i]) = (Leader)) {
            with (entry = [term |-> (currentTerm)[i], cmd |-> (m0).mcmd]) {
              log := [log EXCEPT ![i] = Append((log)[i], entry)];
              with (value80 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                if (((value80).cmd) = (LogConcat)) {
                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value80).entries)];
                  goto serverLoop;
                } else {
                  if (((value80).cmd) = (LogPop)) {
                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value80).cnt))];
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              };
            };
          } else {
            if (((leader)[i]) # (Nil)) {
              with (j = (leader)[i]) {
                either {
                  with (value90 = [mtype |-> ProposeMessage, mcmd |-> (m0).mcmd, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value90), enabled |-> ((network)[j]).enabled]];
                    goto serverLoop;
                  };
                } or {
                  with (yielded_fd30 = (fd)[j]) {
                    await yielded_fd30;
                    goto serverLoop;
                  };
                };
              };
            } else {
              goto serverLoop;
            };
          };
        } else {
          if (((state)[i]) = (Leader)) {
            with (entry = [term |-> (currentTerm)[i], cmd |-> (m0).mcmd]) {
              log := [log EXCEPT ![i] = Append((log)[i], entry)];
              with (value81 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                if (((value81).cmd) = (LogConcat)) {
                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value81).entries)];
                  goto serverLoop;
                } else {
                  if (((value81).cmd) = (LogPop)) {
                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value81).cnt))];
                    goto serverLoop;
                  } else {
                    goto serverLoop;
                  };
                };
              };
            };
          } else {
            if (((leader)[i]) # (Nil)) {
              with (j = (leader)[i]) {
                either {
                  with (value91 = [mtype |-> ProposeMessage, mcmd |-> (m0).mcmd, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value91), enabled |-> ((network)[j]).enabled]];
                    goto serverLoop;
                  };
                } or {
                  with (yielded_fd31 = (fd)[j]) {
                    await yielded_fd31;
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
  }
  
  fair process (s2 \in ServerRequestVoteSet)
    variables idx1 = 1; srvId1 = (requestVoteSrvId)[self];
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
              idx1 := 1;
              goto requestVoteLoop;
            } else {
              idx1 := 1;
              goto requestVoteLoop;
            };
          };
        };
      } else {
        goto Done;
      };
    requestVoteLoop:
      if ((idx1) <= (NumServers)) {
        if ((idx1) # (srvId1)) {
          either {
            with (value100 = [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId1], mlastLogTerm |-> LastTerm((log)[srvId1]), mlastLogIndex |-> Len((log)[srvId1]), msource |-> srvId1, mdest |-> idx1]) {
              await ((network)[idx1]).enabled;
              await (Len(((network)[idx1]).queue)) < (BufferSize);
              network := [network EXCEPT ![idx1] = [queue |-> Append(((network)[idx1]).queue, value100), enabled |-> ((network)[idx1]).enabled]];
              idx1 := (idx1) + (1);
              goto requestVoteLoop;
            };
          } or {
            with (yielded_fd40 = (fd)[idx1]) {
              await yielded_fd40;
              idx1 := (idx1) + (1);
              goto requestVoteLoop;
            };
          };
        } else {
          idx1 := (idx1) + (1);
          goto requestVoteLoop;
        };
      } else {
        goto serverRequestVoteLoop;
      };
  }
  
  fair process (s3 \in ServerAppendEntriesSet)
    variables idx2; srvId2 = (appendEntriesSrvId)[self];
  {
    serverAppendEntriesLoop:
      if (appendEntriesCh) {
        await ((state)[srvId2]) = (Leader);
        idx2 := 1;
        goto appendEntriesLoop;
      } else {
        goto Done;
      };
    appendEntriesLoop:
      if ((((state)[srvId2]) = (Leader)) /\ ((idx2) <= (NumServers))) {
        if ((idx2) # (srvId2)) {
          with (
            prevLogIndex1 = (((nextIndex)[srvId2])[idx2]) - (1), 
            prevLogTerm1 = IF (prevLogIndex1) > (0) THEN (((log)[srvId2])[prevLogIndex1]).term ELSE 0, 
            entries1 = SubSeq((log)[srvId2], ((nextIndex)[srvId2])[idx2], Len((log)[srvId2]))
          ) {
            either {
              with (value118 = [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId2], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> (commitIndex)[srvId2], msource |-> srvId2, mdest |-> idx2]) {
                await ((network)[idx2]).enabled;
                await (Len(((network)[idx2]).queue)) < (BufferSize);
                network := [network EXCEPT ![idx2] = [queue |-> Append(((network)[idx2]).queue, value118), enabled |-> ((network)[idx2]).enabled]];
                idx2 := (idx2) + (1);
                goto appendEntriesLoop;
              };
            } or {
              with (yielded_fd50 = (fd)[idx2]) {
                await yielded_fd50;
                idx2 := (idx2) + (1);
                goto appendEntriesLoop;
              };
            };
          };
        } else {
          idx2 := (idx2) + (1);
          goto appendEntriesLoop;
        };
      } else {
        goto serverAppendEntriesLoop;
      };
  }
  
  fair process (s4 \in ServerAdvanceCommitIndexSet)
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
          cmd = (entry).cmd
        ) {
          if (Debug) {
            print <<"ServerAccept", i, cmd>>;
            with (value120 = [mtype |-> AcceptMessage, mcmd |-> cmd]) {
              await (Len((acctCh)[i])) < (BufferSize);
              acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value120)];
              goto applyLoop;
            };
          } else {
            with (value121 = [mtype |-> AcceptMessage, mcmd |-> cmd]) {
              await (Len((acctCh)[i])) < (BufferSize);
              acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value121)];
              goto applyLoop;
            };
          };
        };
      } else {
        goto serverAdvanceCommitIndexLoop;
      };
  }
  
  fair process (s5 \in ServerBecomeLeaderSet)
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
  
  fair process (s6 \in ServerFollowerAdvanceCommitIndexSet)
    variables m1; srvId5 = (fAdvCommitSrvId)[self];
  {
    serverFollowerAdvanceCommitIndexLoop:
      if (TRUE) {
        await (Len((fAdvCommitIdxCh)[srvId5])) > (0);
        with (res20 = Head((fAdvCommitIdxCh)[srvId5])) {
          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![srvId5] = Tail((fAdvCommitIdxCh)[srvId5])];
          with (yielded_fAdvCommitIdxCh0 = res20) {
            m1 := yielded_fAdvCommitIdxCh0;
            goto acctLoop;
          };
        };
      } else {
        goto Done;
      };
    acctLoop:
      if (((commitIndex)[srvId5]) < ((m1).mcommitIndex)) {
        commitIndex := [commitIndex EXCEPT ![srvId5] = ((commitIndex)[srvId5]) + (1)];
        with (
          i = srvId5, 
          k = (commitIndex)[i], 
          entry = ((log)[i])[k], 
          cmd = (entry).cmd
        ) {
          if (Debug) {
            print <<"ServerAccept", i, cmd>>;
            with (value130 = [mtype |-> AcceptMessage, mcmd |-> cmd]) {
              await (Len((acctCh)[i])) < (BufferSize);
              acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value130)];
              goto acctLoop;
            };
          } else {
            with (value131 = [mtype |-> AcceptMessage, mcmd |-> cmd]) {
              await (Len((acctCh)[i])) < (BufferSize);
              acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value131)];
              goto acctLoop;
            };
          };
        };
      } else {
        goto serverFollowerAdvanceCommitIndexLoop;
      };
  }
  
  fair process (crasher \in ServerCrasherSet)
    variables srvId6 = (crasherSrvId)[self];
  {
    serverCrash:
      with (value140 = FALSE) {
        network := [network EXCEPT ![srvId6] = [queue |-> ((network)[srvId6]).queue, enabled |-> value140]];
        goto fdUpdate;
      };
    fdUpdate:
      with (value150 = TRUE) {
        fd := [fd EXCEPT ![srvId6] = value150];
        goto Done;
      };
  }
  
  fair process (proposer = 0)
  {
    sndReq:
      with (value160 = [mtype |-> ProposeMessage, mcmd |-> [data |-> "hello"]]) {
        await (Len((propCh)[1])) < (BufferSize);
        propCh := [propCh EXCEPT ![1] = Append((propCh)[1], value160)];
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "4074f14a" /\ chksum(tla) = "db7d7c01") PCal-18049938ece8066a38eb5044080cf45c
\* Label serverLoop of process s0 at line 991 col 7 changed to serverLoop_
\* Label handleMsg of process s0 at line 1006 col 7 changed to handleMsg_
CONSTANT defaultInitValue
VARIABLES network, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, 
          log, plog, votedFor, votesResponded, votesGranted, leader, propCh, 
          acctCh, leaderTimeout, appendEntriesCh, becomeLeaderCh, 
          fAdvCommitIdxCh, netListenerSrvId, propChListenerSrvId, 
          requestVoteSrvId, appendEntriesSrvId, advanceCommitIndexSrvId, 
          becomeLeaderSrvId, fAdvCommitSrvId, crasherSrvId, pc

(* define statement *)
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ProposeMessage == "prm"
AcceptMessage == "acm"
Key1 == "key1"
Key2 == "key2"
Value1 == "value1"
LastTerm(xlog) == IF (Len(xlog)) = (0) THEN 0 ELSE ((xlog)[Len(xlog)]).term
ServerNetListenerSet == (((0) * (NumServers)) + (1)) .. ((1) * (NumServers))
ServerPropChListenerSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
ServerRequestVoteSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
ServerAppendEntriesSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
ServerAdvanceCommitIndexSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
ServerBecomeLeaderSet == (((5) * (NumServers)) + (1)) .. ((6) * (NumServers))
ServerFollowerAdvanceCommitIndexSet == (((6) * (NumServers)) + (1)) .. ((7) * (NumServers))
ServerCrasherSet == IF ExploreFail THEN (((7) * (NumServers)) + (1)) .. (((7) * (NumServers)) + (MaxNodeFail)) ELSE {}
NodeSet == ServerSet
KeySet == {}

VARIABLES idx, m, srvId, idx0, m0, srvId0, idx1, srvId1, idx2, srvId2, 
          newCommitIndex, srvId3, srvId4, m1, srvId5, srvId6

vars == << network, fd, state, currentTerm, commitIndex, nextIndex, 
           matchIndex, log, plog, votedFor, votesResponded, votesGranted, 
           leader, propCh, acctCh, leaderTimeout, appendEntriesCh, 
           becomeLeaderCh, fAdvCommitIdxCh, netListenerSrvId, 
           propChListenerSrvId, requestVoteSrvId, appendEntriesSrvId, 
           advanceCommitIndexSrvId, becomeLeaderSrvId, fAdvCommitSrvId, 
           crasherSrvId, pc, idx, m, srvId, idx0, m0, srvId0, idx1, srvId1, 
           idx2, srvId2, newCommitIndex, srvId3, srvId4, m1, srvId5, srvId6
        >>

ProcSet == (ServerNetListenerSet) \cup (ServerPropChListenerSet) \cup (ServerRequestVoteSet) \cup (ServerAppendEntriesSet) \cup (ServerAdvanceCommitIndexSet) \cup (ServerBecomeLeaderSet) \cup (ServerFollowerAdvanceCommitIndexSet) \cup (ServerCrasherSet) \cup {0}

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
        /\ propCh = [i \in ServerSet |-> <<>>]
        /\ acctCh = [i \in ServerSet |-> <<>>]
        /\ leaderTimeout = TRUE
        /\ appendEntriesCh = TRUE
        /\ becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]
        /\ fAdvCommitIdxCh = [i \in ServerSet |-> <<>>]
        /\ netListenerSrvId = [i \in ServerNetListenerSet |-> (i) - ((0) * (NumServers))]
        /\ propChListenerSrvId = [i \in ServerPropChListenerSet |-> (i) - ((1) * (NumServers))]
        /\ requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((2) * (NumServers))]
        /\ appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((3) * (NumServers))]
        /\ advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((4) * (NumServers))]
        /\ becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((5) * (NumServers))]
        /\ fAdvCommitSrvId = [i \in ServerFollowerAdvanceCommitIndexSet |-> (i) - ((6) * (NumServers))]
        /\ crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((7) * (NumServers))]
        (* Process s0 *)
        /\ idx = [self \in ServerNetListenerSet |-> 1]
        /\ m = [self \in ServerNetListenerSet |-> defaultInitValue]
        /\ srvId = [self \in ServerNetListenerSet |-> (netListenerSrvId)[self]]
        (* Process s1 *)
        /\ idx0 = [self \in ServerPropChListenerSet |-> 1]
        /\ m0 = [self \in ServerPropChListenerSet |-> defaultInitValue]
        /\ srvId0 = [self \in ServerPropChListenerSet |-> (propChListenerSrvId)[self]]
        (* Process s2 *)
        /\ idx1 = [self \in ServerRequestVoteSet |-> 1]
        /\ srvId1 = [self \in ServerRequestVoteSet |-> (requestVoteSrvId)[self]]
        (* Process s3 *)
        /\ idx2 = [self \in ServerAppendEntriesSet |-> defaultInitValue]
        /\ srvId2 = [self \in ServerAppendEntriesSet |-> (appendEntriesSrvId)[self]]
        (* Process s4 *)
        /\ newCommitIndex = [self \in ServerAdvanceCommitIndexSet |-> 0]
        /\ srvId3 = [self \in ServerAdvanceCommitIndexSet |-> (advanceCommitIndexSrvId)[self]]
        (* Process s5 *)
        /\ srvId4 = [self \in ServerBecomeLeaderSet |-> (becomeLeaderSrvId)[self]]
        (* Process s6 *)
        /\ m1 = [self \in ServerFollowerAdvanceCommitIndexSet |-> defaultInitValue]
        /\ srvId5 = [self \in ServerFollowerAdvanceCommitIndexSet |-> (fAdvCommitSrvId)[self]]
        (* Process crasher *)
        /\ srvId6 = [self \in ServerCrasherSet |-> (crasherSrvId)[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerNetListenerSet -> "serverLoop_"
                                        [] self \in ServerPropChListenerSet -> "serverLoop"
                                        [] self \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                                        [] self \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                                        [] self \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                                        [] self \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                                        [] self \in ServerFollowerAdvanceCommitIndexSet -> "serverFollowerAdvanceCommitIndexLoop"
                                        [] self \in ServerCrasherSet -> "serverCrash"
                                        [] self = 0 -> "sndReq"]

serverLoop_(self) == /\ pc[self] = "serverLoop_"
                     /\ IF TRUE
                           THEN /\ Assert(((network)[self]).enabled, 
                                          "Failure of assertion at line 992, column 9.")
                                /\ (Len(((network)[self]).queue)) > (0)
                                /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                     /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                     /\ LET yielded_network1 == readMsg00 IN
                                          /\ m' = [m EXCEPT ![self] = yielded_network1]
                                          /\ Assert(((m'[self]).mdest) = (self), 
                                                    "Failure of assertion at line 998, column 13.")
                                          /\ pc' = [pc EXCEPT ![self] = "handleMsg_"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << network, m >>
                     /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                     nextIndex, matchIndex, log, plog, 
                                     votedFor, votesResponded, votesGranted, 
                                     leader, propCh, acctCh, leaderTimeout, 
                                     appendEntriesCh, becomeLeaderCh, 
                                     fAdvCommitIdxCh, netListenerSrvId, 
                                     propChListenerSrvId, requestVoteSrvId, 
                                     appendEntriesSrvId, 
                                     advanceCommitIndexSrvId, 
                                     becomeLeaderSrvId, fAdvCommitSrvId, 
                                     crasherSrvId, idx, srvId, idx0, m0, 
                                     srvId0, idx1, srvId1, idx2, srvId2, 
                                     newCommitIndex, srvId3, srvId4, m1, 
                                     srvId5, srvId6 >>

handleMsg_(self) == /\ pc[self] = "handleMsg_"
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
                                                                    "Failure of assertion at line 1018, column 15.")
                                                          /\ IF grant
                                                                THEN /\ votedFor' = [votedFor1 EXCEPT ![i] = j]
                                                                     /\ \/ /\ LET value17 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                /\ ((network)[j]).enabled
                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]]
                                                                                /\ IF Debug
                                                                                      THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                        \/ /\ LET yielded_fd6 == (fd)[j] IN
                                                                                /\ yielded_fd6
                                                                                /\ IF Debug
                                                                                      THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                           /\ UNCHANGED network
                                                                ELSE /\ \/ /\ LET value18 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                                /\ ((network)[j]).enabled
                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]]
                                                                                /\ IF Debug
                                                                                      THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                           /\ votedFor' = votedFor1
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      ELSE /\ votedFor' = votedFor1
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                        \/ /\ LET yielded_fd7 == (fd)[j] IN
                                                                                /\ yielded_fd7
                                                                                /\ IF Debug
                                                                                      THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                           /\ votedFor' = votedFor1
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      ELSE /\ votedFor' = votedFor1
                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                           /\ UNCHANGED network
                                     ELSE /\ LET i == self IN
                                               LET j == (m[self]).msource IN
                                                 LET logOK == (((m[self]).mlastLogTerm) > (LastTerm((log)[i]))) \/ ((((m[self]).mlastLogTerm) = (LastTerm((log)[i]))) /\ (((m[self]).mlastLogIndex) >= (Len((log)[i])))) IN
                                                   LET grant == ((((m[self]).mterm) = ((currentTerm)[i])) /\ (logOK)) /\ (((votedFor)[self]) \in ({Nil, j})) IN
                                                     /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                               "Failure of assertion at line 1082, column 13.")
                                                     /\ IF grant
                                                           THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                                                /\ \/ /\ LET value19 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                           /\ ((network)[j]).enabled
                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value19), enabled |-> ((network)[j]).enabled]]
                                                                           /\ IF Debug
                                                                                 THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                   \/ /\ LET yielded_fd8 == (fd)[j] IN
                                                                           /\ yielded_fd8
                                                                           /\ IF Debug
                                                                                 THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                      /\ UNCHANGED network
                                                           ELSE /\ \/ /\ LET value20 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                           /\ ((network)[j]).enabled
                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value20), enabled |-> ((network)[j]).enabled]]
                                                                           /\ IF Debug
                                                                                 THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                   \/ /\ LET yielded_fd9 == (fd)[j] IN
                                                                           /\ yielded_fd9
                                                                           /\ IF Debug
                                                                                 THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                      /\ UNCHANGED network
                                                                /\ UNCHANGED votedFor
                                          /\ UNCHANGED << state, currentTerm, 
                                                          leader >>
                               /\ UNCHANGED << nextIndex, matchIndex, log, 
                                               plog, votesResponded, 
                                               votesGranted, leaderTimeout, 
                                               becomeLeaderCh, fAdvCommitIdxCh >>
                          ELSE /\ IF ((m[self]).mtype) = (RequestVoteResponse)
                                     THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                     /\ state' = [state EXCEPT ![self] = Follower]
                                                     /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                     /\ leader' = [leader EXCEPT ![self] = Nil]
                                                     /\ IF ((m[self]).mterm) < ((currentTerm')[self])
                                                           THEN /\ TRUE
                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                /\ UNCHANGED << votesResponded, 
                                                                                votesGranted, 
                                                                                becomeLeaderCh >>
                                                           ELSE /\ LET i == self IN
                                                                     LET j == (m[self]).msource IN
                                                                       /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                 "Failure of assertion at line 1150, column 17.")
                                                                       /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                       /\ IF (m[self]).mvoteGranted
                                                                             THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                  /\ IF (((state')[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                        THEN /\ LET value00 == TRUE IN
                                                                                                  /\ (Len((becomeLeaderCh)[i])) < (BufferSize)
                                                                                                  /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value00)]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                             /\ UNCHANGED becomeLeaderCh
                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                  /\ UNCHANGED << votesGranted, 
                                                                                                  becomeLeaderCh >>
                                                ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                           THEN /\ TRUE
                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                /\ UNCHANGED << votesResponded, 
                                                                                votesGranted, 
                                                                                becomeLeaderCh >>
                                                           ELSE /\ LET i == self IN
                                                                     LET j == (m[self]).msource IN
                                                                       /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                 "Failure of assertion at line 1177, column 17.")
                                                                       /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                       /\ IF (m[self]).mvoteGranted
                                                                             THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                  /\ IF (((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                        THEN /\ LET value01 == TRUE IN
                                                                                                  /\ (Len((becomeLeaderCh)[i])) < (BufferSize)
                                                                                                  /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value01)]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                             /\ UNCHANGED becomeLeaderCh
                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                  /\ UNCHANGED << votesGranted, 
                                                                                                  becomeLeaderCh >>
                                                     /\ UNCHANGED << state, 
                                                                     currentTerm, 
                                                                     votedFor, 
                                                                     leader >>
                                          /\ UNCHANGED << network, nextIndex, 
                                                          matchIndex, log, 
                                                          plog, leaderTimeout, 
                                                          fAdvCommitIdxCh >>
                                     ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                                THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                           THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                                /\ LET state1 == [state EXCEPT ![self] = Follower] IN
                                                                     /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                     /\ LET leader1 == [leader EXCEPT ![self] = Nil] IN
                                                                          LET i == self IN
                                                                            LET j == (m[self]).msource IN
                                                                              LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                                /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                                          "Failure of assertion at line 1208, column 19.")
                                                                                /\ IF ((m[self]).mterm) = ((currentTerm')[i])
                                                                                      THEN /\ leader' = [leader1 EXCEPT ![i] = (m[self]).msource]
                                                                                           /\ leaderTimeout' = LeaderTimeoutReset
                                                                                           /\ IF (((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                                 THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                                      /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                            THEN /\ \/ /\ LET value110 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value110), enabled |-> ((network)[j]).enabled]]
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                    \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                                                                            /\ yielded_fd00
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                       /\ UNCHANGED network
                                                                                                                 /\ UNCHANGED << log, 
                                                                                                                                 plog, 
                                                                                                                                 fAdvCommitIdxCh >>
                                                                                                            ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                           "Failure of assertion at line 1229, column 25.")
                                                                                                                 /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                                      LET value21 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                        IF ((value21).cmd) = (LogConcat)
                                                                                                                           THEN /\ LET plog8 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value21).entries)] IN
                                                                                                                                     LET log8 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                       LET value30 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                         IF ((value30).cmd) = (LogConcat)
                                                                                                                                            THEN /\ plog' = [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value30).entries)]
                                                                                                                                                 /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                           "Failure of assertion at line 1243, column 33.")
                                                                                                                                                 /\ LET value40 == m[self] IN
                                                                                                                                                      /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value40)]
                                                                                                                                                      /\ \/ /\ LET value50 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                         \/ /\ LET yielded_fd10 == (fd)[j] IN
                                                                                                                                                                 /\ yielded_fd10
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                            /\ UNCHANGED network
                                                                                                                                            ELSE /\ IF ((value30).cmd) = (LogPop)
                                                                                                                                                       THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - ((value30).cnt))]
                                                                                                                                                            /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1265, column 35.")
                                                                                                                                                            /\ LET value41 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value41)]
                                                                                                                                                                 /\ \/ /\ LET value51 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd11
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ log' = [log8 EXCEPT ![i] = ((log8)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1285, column 35.")
                                                                                                                                                            /\ LET value42 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value42)]
                                                                                                                                                                 /\ \/ /\ LET value52 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog8
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd12
                                                                                                                                                                            /\ plog' = plog8
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                           ELSE /\ IF ((value21).cmd) = (LogPop)
                                                                                                                                      THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value21).cnt))] IN
                                                                                                                                                LET log9 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                  LET value31 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                    IF ((value31).cmd) = (LogConcat)
                                                                                                                                                       THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value31).entries)]
                                                                                                                                                            /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1318, column 35.")
                                                                                                                                                            /\ LET value43 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value43)]
                                                                                                                                                                 /\ \/ /\ LET value53 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd13
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ IF ((value31).cmd) = (LogPop)
                                                                                                                                                                  THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - ((value31).cnt))]
                                                                                                                                                                       /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1340, column 37.")
                                                                                                                                                                       /\ LET value44 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value44)]
                                                                                                                                                                            /\ \/ /\ LET value54 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd14 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd14
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ log' = [log9 EXCEPT ![i] = ((log9)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1360, column 37.")
                                                                                                                                                                       /\ LET value45 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value45)]
                                                                                                                                                                            /\ \/ /\ LET value55 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog9
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd15 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd15
                                                                                                                                                                                       /\ plog' = plog9
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                      ELSE /\ LET log10 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                LET value32 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                  IF ((value32).cmd) = (LogConcat)
                                                                                                                                                     THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)]
                                                                                                                                                          /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                    "Failure of assertion at line 1391, column 35.")
                                                                                                                                                          /\ LET value46 == m[self] IN
                                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value46)]
                                                                                                                                                               /\ \/ /\ LET value56 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                  \/ /\ LET yielded_fd16 == (fd)[j] IN
                                                                                                                                                                          /\ yielded_fd16
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                     ELSE /\ IF ((value32).cmd) = (LogPop)
                                                                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value32).cnt))]
                                                                                                                                                                     /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1413, column 37.")
                                                                                                                                                                     /\ LET value47 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value47)]
                                                                                                                                                                          /\ \/ /\ LET value57 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd17 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd17
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = [log10 EXCEPT ![i] = ((log10)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1433, column 37.")
                                                                                                                                                                     /\ LET value48 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value48)]
                                                                                                                                                                          /\ \/ /\ LET value58 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd18 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd18
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                     /\ plog' = plog
                                                                                                 ELSE /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                            THEN /\ \/ /\ LET value111 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value111), enabled |-> ((network)[j]).enabled]]
                                                                                                                            /\ state' = state1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                    \/ /\ LET yielded_fd01 == (fd)[j] IN
                                                                                                                            /\ yielded_fd01
                                                                                                                            /\ state' = state1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                       /\ UNCHANGED network
                                                                                                                 /\ UNCHANGED << log, 
                                                                                                                                 plog, 
                                                                                                                                 fAdvCommitIdxCh >>
                                                                                                            ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                           "Failure of assertion at line 1476, column 25.")
                                                                                                                 /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                                      LET value22 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                        IF ((value22).cmd) = (LogConcat)
                                                                                                                           THEN /\ LET plog10 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value22).entries)] IN
                                                                                                                                     LET log11 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                       LET value33 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                         IF ((value33).cmd) = (LogConcat)
                                                                                                                                            THEN /\ plog' = [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value33).entries)]
                                                                                                                                                 /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                           "Failure of assertion at line 1490, column 33.")
                                                                                                                                                 /\ LET value49 == m[self] IN
                                                                                                                                                      /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value49)]
                                                                                                                                                      /\ \/ /\ LET value59 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                         \/ /\ LET yielded_fd19 == (fd)[j] IN
                                                                                                                                                                 /\ yielded_fd19
                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                            /\ UNCHANGED network
                                                                                                                                            ELSE /\ IF ((value33).cmd) = (LogPop)
                                                                                                                                                       THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - ((value33).cnt))]
                                                                                                                                                            /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1514, column 35.")
                                                                                                                                                            /\ LET value410 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value410)]
                                                                                                                                                                 /\ \/ /\ LET value510 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd110 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd110
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ log' = [log11 EXCEPT ![i] = ((log11)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1536, column 35.")
                                                                                                                                                            /\ LET value411 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value411)]
                                                                                                                                                                 /\ \/ /\ LET value511 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog10
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd111 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd111
                                                                                                                                                                            /\ plog' = plog10
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                           ELSE /\ IF ((value22).cmd) = (LogPop)
                                                                                                                                      THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value22).cnt))] IN
                                                                                                                                                LET log12 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                  LET value34 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                    IF ((value34).cmd) = (LogConcat)
                                                                                                                                                       THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value34).entries)]
                                                                                                                                                            /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1571, column 35.")
                                                                                                                                                            /\ LET value412 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value412)]
                                                                                                                                                                 /\ \/ /\ LET value512 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd112 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd112
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ IF ((value34).cmd) = (LogPop)
                                                                                                                                                                  THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - ((value34).cnt))]
                                                                                                                                                                       /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1595, column 37.")
                                                                                                                                                                       /\ LET value413 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value413)]
                                                                                                                                                                            /\ \/ /\ LET value513 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd113 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd113
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ log' = [log12 EXCEPT ![i] = ((log12)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1617, column 37.")
                                                                                                                                                                       /\ LET value414 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value414)]
                                                                                                                                                                            /\ \/ /\ LET value514 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog11
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd114 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd114
                                                                                                                                                                                       /\ plog' = plog11
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                      ELSE /\ LET log13 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                LET value35 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                  IF ((value35).cmd) = (LogConcat)
                                                                                                                                                     THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value35).entries)]
                                                                                                                                                          /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                    "Failure of assertion at line 1650, column 35.")
                                                                                                                                                          /\ LET value415 == m[self] IN
                                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value415)]
                                                                                                                                                               /\ \/ /\ LET value515 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                  \/ /\ LET yielded_fd115 == (fd)[j] IN
                                                                                                                                                                          /\ yielded_fd115
                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                     ELSE /\ IF ((value35).cmd) = (LogPop)
                                                                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value35).cnt))]
                                                                                                                                                                     /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1674, column 37.")
                                                                                                                                                                     /\ LET value416 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value416)]
                                                                                                                                                                          /\ \/ /\ LET value516 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd116 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd116
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = [log13 EXCEPT ![i] = ((log13)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1696, column 37.")
                                                                                                                                                                     /\ LET value417 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value417)]
                                                                                                                                                                          /\ \/ /\ LET value517 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd117 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd117
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                     /\ plog' = plog
                                                                                      ELSE /\ IF (((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                                 THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                                      /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                            THEN /\ \/ /\ LET value112 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value112), enabled |-> ((network)[j]).enabled]]
                                                                                                                            /\ leader' = leader1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                    \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                                                                            /\ yielded_fd02
                                                                                                                            /\ leader' = leader1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                       /\ UNCHANGED network
                                                                                                                 /\ UNCHANGED << log, 
                                                                                                                                 plog, 
                                                                                                                                 fAdvCommitIdxCh >>
                                                                                                            ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                           "Failure of assertion at line 1744, column 25.")
                                                                                                                 /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                                      LET value23 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                        IF ((value23).cmd) = (LogConcat)
                                                                                                                           THEN /\ LET plog12 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value23).entries)] IN
                                                                                                                                     LET log14 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                       LET value36 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                         IF ((value36).cmd) = (LogConcat)
                                                                                                                                            THEN /\ plog' = [plog12 EXCEPT ![i] = ((plog12)[i]) \o ((value36).entries)]
                                                                                                                                                 /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                           "Failure of assertion at line 1758, column 33.")
                                                                                                                                                 /\ LET value418 == m[self] IN
                                                                                                                                                      /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value418)]
                                                                                                                                                      /\ \/ /\ LET value518 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                 /\ leader' = leader1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                         \/ /\ LET yielded_fd118 == (fd)[j] IN
                                                                                                                                                                 /\ yielded_fd118
                                                                                                                                                                 /\ leader' = leader1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                            /\ UNCHANGED network
                                                                                                                                            ELSE /\ IF ((value36).cmd) = (LogPop)
                                                                                                                                                       THEN /\ plog' = [plog12 EXCEPT ![i] = SubSeq((plog12)[i], 1, (Len((plog12)[i])) - ((value36).cnt))]
                                                                                                                                                            /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1782, column 35.")
                                                                                                                                                            /\ LET value419 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value419)]
                                                                                                                                                                 /\ \/ /\ LET value519 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd119 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd119
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ log' = [log14 EXCEPT ![i] = ((log14)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1804, column 35.")
                                                                                                                                                            /\ LET value420 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value420)]
                                                                                                                                                                 /\ \/ /\ LET value520 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog12
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd120 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd120
                                                                                                                                                                            /\ plog' = plog12
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                           ELSE /\ IF ((value23).cmd) = (LogPop)
                                                                                                                                      THEN /\ LET plog13 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value23).cnt))] IN
                                                                                                                                                LET log15 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                  LET value37 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                    IF ((value37).cmd) = (LogConcat)
                                                                                                                                                       THEN /\ plog' = [plog13 EXCEPT ![i] = ((plog13)[i]) \o ((value37).entries)]
                                                                                                                                                            /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 1839, column 35.")
                                                                                                                                                            /\ LET value421 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value421)]
                                                                                                                                                                 /\ \/ /\ LET value521 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd121 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd121
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ IF ((value37).cmd) = (LogPop)
                                                                                                                                                                  THEN /\ plog' = [plog13 EXCEPT ![i] = SubSeq((plog13)[i], 1, (Len((plog13)[i])) - ((value37).cnt))]
                                                                                                                                                                       /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1863, column 37.")
                                                                                                                                                                       /\ LET value422 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value422)]
                                                                                                                                                                            /\ \/ /\ LET value522 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd122 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd122
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ log' = [log15 EXCEPT ![i] = ((log15)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 1885, column 37.")
                                                                                                                                                                       /\ LET value423 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value423)]
                                                                                                                                                                            /\ \/ /\ LET value523 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog13
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd123 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd123
                                                                                                                                                                                       /\ plog' = plog13
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                      ELSE /\ LET log16 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                LET value38 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                  IF ((value38).cmd) = (LogConcat)
                                                                                                                                                     THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value38).entries)]
                                                                                                                                                          /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                    "Failure of assertion at line 1918, column 35.")
                                                                                                                                                          /\ LET value424 == m[self] IN
                                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value424)]
                                                                                                                                                               /\ \/ /\ LET value524 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                          /\ leader' = leader1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                  \/ /\ LET yielded_fd124 == (fd)[j] IN
                                                                                                                                                                          /\ yielded_fd124
                                                                                                                                                                          /\ leader' = leader1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                     ELSE /\ IF ((value38).cmd) = (LogPop)
                                                                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value38).cnt))]
                                                                                                                                                                     /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1942, column 37.")
                                                                                                                                                                     /\ LET value425 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value425)]
                                                                                                                                                                          /\ \/ /\ LET value525 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd125 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd125
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = [log16 EXCEPT ![i] = ((log16)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 1964, column 37.")
                                                                                                                                                                     /\ LET value426 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value426)]
                                                                                                                                                                          /\ \/ /\ LET value526 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd126 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd126
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                     /\ plog' = plog
                                                                                                 ELSE /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                            THEN /\ \/ /\ LET value113 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value113), enabled |-> ((network)[j]).enabled]]
                                                                                                                            /\ leader' = leader1
                                                                                                                            /\ state' = state1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                    \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                                                                            /\ yielded_fd03
                                                                                                                            /\ leader' = leader1
                                                                                                                            /\ state' = state1
                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                       /\ UNCHANGED network
                                                                                                                 /\ UNCHANGED << log, 
                                                                                                                                 plog, 
                                                                                                                                 fAdvCommitIdxCh >>
                                                                                                            ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                           "Failure of assertion at line 2011, column 25.")
                                                                                                                 /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                                      LET value24 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                        IF ((value24).cmd) = (LogConcat)
                                                                                                                           THEN /\ LET plog14 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value24).entries)] IN
                                                                                                                                     LET log17 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                       LET value39 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                         IF ((value39).cmd) = (LogConcat)
                                                                                                                                            THEN /\ plog' = [plog14 EXCEPT ![i] = ((plog14)[i]) \o ((value39).entries)]
                                                                                                                                                 /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                           "Failure of assertion at line 2025, column 33.")
                                                                                                                                                 /\ LET value427 == m[self] IN
                                                                                                                                                      /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value427)]
                                                                                                                                                      /\ \/ /\ LET value527 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                 /\ leader' = leader1
                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                         \/ /\ LET yielded_fd127 == (fd)[j] IN
                                                                                                                                                                 /\ yielded_fd127
                                                                                                                                                                 /\ leader' = leader1
                                                                                                                                                                 /\ state' = state1
                                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                            /\ UNCHANGED network
                                                                                                                                            ELSE /\ IF ((value39).cmd) = (LogPop)
                                                                                                                                                       THEN /\ plog' = [plog14 EXCEPT ![i] = SubSeq((plog14)[i], 1, (Len((plog14)[i])) - ((value39).cnt))]
                                                                                                                                                            /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 2051, column 35.")
                                                                                                                                                            /\ LET value428 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value428)]
                                                                                                                                                                 /\ \/ /\ LET value528 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd128 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd128
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ log' = [log17 EXCEPT ![i] = ((log17)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 2075, column 35.")
                                                                                                                                                            /\ LET value429 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value429)]
                                                                                                                                                                 /\ \/ /\ LET value529 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog14
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd129 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd129
                                                                                                                                                                            /\ plog' = plog14
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                           ELSE /\ IF ((value24).cmd) = (LogPop)
                                                                                                                                      THEN /\ LET plog15 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value24).cnt))] IN
                                                                                                                                                LET log18 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                  LET value310 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                    IF ((value310).cmd) = (LogConcat)
                                                                                                                                                       THEN /\ plog' = [plog15 EXCEPT ![i] = ((plog15)[i]) \o ((value310).entries)]
                                                                                                                                                            /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                      "Failure of assertion at line 2112, column 35.")
                                                                                                                                                            /\ LET value430 == m[self] IN
                                                                                                                                                                 /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value430)]
                                                                                                                                                                 /\ \/ /\ LET value530 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                    \/ /\ LET yielded_fd130 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd130
                                                                                                                                                                            /\ leader' = leader1
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ IF ((value310).cmd) = (LogPop)
                                                                                                                                                                  THEN /\ plog' = [plog15 EXCEPT ![i] = SubSeq((plog15)[i], 1, (Len((plog15)[i])) - ((value310).cnt))]
                                                                                                                                                                       /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 2138, column 37.")
                                                                                                                                                                       /\ LET value431 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value431)]
                                                                                                                                                                            /\ \/ /\ LET value531 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd131 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd131
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ log' = [log18 EXCEPT ![i] = ((log18)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                       /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                                 "Failure of assertion at line 2162, column 37.")
                                                                                                                                                                       /\ LET value432 == m[self] IN
                                                                                                                                                                            /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value432)]
                                                                                                                                                                            /\ \/ /\ LET value532 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog15
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                               \/ /\ LET yielded_fd132 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd132
                                                                                                                                                                                       /\ plog' = plog15
                                                                                                                                                                                       /\ leader' = leader1
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                      ELSE /\ LET log19 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                                LET value311 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                  IF ((value311).cmd) = (LogConcat)
                                                                                                                                                     THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)]
                                                                                                                                                          /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                    "Failure of assertion at line 2197, column 35.")
                                                                                                                                                          /\ LET value433 == m[self] IN
                                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value433)]
                                                                                                                                                               /\ \/ /\ LET value533 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                          /\ leader' = leader1
                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                  \/ /\ LET yielded_fd133 == (fd)[j] IN
                                                                                                                                                                          /\ yielded_fd133
                                                                                                                                                                          /\ leader' = leader1
                                                                                                                                                                          /\ state' = state1
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                     ELSE /\ IF ((value311).cmd) = (LogPop)
                                                                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value311).cnt))]
                                                                                                                                                                     /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 2223, column 37.")
                                                                                                                                                                     /\ LET value434 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value434)]
                                                                                                                                                                          /\ \/ /\ LET value534 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd134 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd134
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = [log19 EXCEPT ![i] = ((log19)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                               "Failure of assertion at line 2247, column 37.")
                                                                                                                                                                     /\ LET value435 == m[self] IN
                                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value435)]
                                                                                                                                                                          /\ \/ /\ LET value535 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                             \/ /\ LET yielded_fd135 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd135
                                                                                                                                                                                     /\ leader' = leader1
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                     /\ plog' = plog
                                                                                           /\ UNCHANGED leaderTimeout
                                                           ELSE /\ LET i == self IN
                                                                     LET j == (m[self]).msource IN
                                                                       LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                         /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                                                   "Failure of assertion at line 2286, column 17.")
                                                                         /\ IF ((m[self]).mterm) = ((currentTerm)[i])
                                                                               THEN /\ leader' = [leader EXCEPT ![i] = (m[self]).msource]
                                                                                    /\ leaderTimeout' = LeaderTimeoutReset
                                                                                    /\ IF (((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                                          THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                               /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                     THEN /\ \/ /\ LET value114 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value114), enabled |-> ((network)[j]).enabled]]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                             \/ /\ LET yielded_fd04 == (fd)[j] IN
                                                                                                                     /\ yielded_fd04
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                /\ UNCHANGED network
                                                                                                          /\ UNCHANGED << log, 
                                                                                                                          plog, 
                                                                                                                          fAdvCommitIdxCh >>
                                                                                                     ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                    "Failure of assertion at line 2307, column 23.")
                                                                                                          /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                               LET value25 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                 IF ((value25).cmd) = (LogConcat)
                                                                                                                    THEN /\ LET plog16 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value25).entries)] IN
                                                                                                                              LET log20 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                LET value312 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                  IF ((value312).cmd) = (LogConcat)
                                                                                                                                     THEN /\ plog' = [plog16 EXCEPT ![i] = ((plog16)[i]) \o ((value312).entries)]
                                                                                                                                          /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m[self]).mentries)]
                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                    "Failure of assertion at line 2321, column 31.")
                                                                                                                                          /\ LET value436 == m[self] IN
                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value436)]
                                                                                                                                               /\ \/ /\ LET value536 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                  \/ /\ LET yielded_fd136 == (fd)[j] IN
                                                                                                                                                          /\ yielded_fd136
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                     ELSE /\ IF ((value312).cmd) = (LogPop)
                                                                                                                                                THEN /\ plog' = [plog16 EXCEPT ![i] = SubSeq((plog16)[i], 1, (Len((plog16)[i])) - ((value312).cnt))]
                                                                                                                                                     /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2343, column 33.")
                                                                                                                                                     /\ LET value437 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value437)]
                                                                                                                                                          /\ \/ /\ LET value537 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd137 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd137
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ log' = [log20 EXCEPT ![i] = ((log20)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2363, column 33.")
                                                                                                                                                     /\ LET value438 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value438)]
                                                                                                                                                          /\ \/ /\ LET value538 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ plog' = plog16
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd138 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd138
                                                                                                                                                                     /\ plog' = plog16
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                    ELSE /\ IF ((value25).cmd) = (LogPop)
                                                                                                                               THEN /\ LET plog17 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value25).cnt))] IN
                                                                                                                                         LET log21 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                           LET value313 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                             IF ((value313).cmd) = (LogConcat)
                                                                                                                                                THEN /\ plog' = [plog17 EXCEPT ![i] = ((plog17)[i]) \o ((value313).entries)]
                                                                                                                                                     /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2396, column 33.")
                                                                                                                                                     /\ LET value439 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value439)]
                                                                                                                                                          /\ \/ /\ LET value539 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd139 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd139
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ IF ((value313).cmd) = (LogPop)
                                                                                                                                                           THEN /\ plog' = [plog17 EXCEPT ![i] = SubSeq((plog17)[i], 1, (Len((plog17)[i])) - ((value313).cnt))]
                                                                                                                                                                /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2418, column 35.")
                                                                                                                                                                /\ LET value440 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value440)]
                                                                                                                                                                     /\ \/ /\ LET value540 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd140 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd140
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = [log21 EXCEPT ![i] = ((log21)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2438, column 35.")
                                                                                                                                                                /\ LET value441 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value441)]
                                                                                                                                                                     /\ \/ /\ LET value541 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ plog' = plog17
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd141 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd141
                                                                                                                                                                                /\ plog' = plog17
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                               ELSE /\ LET log22 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                         LET value314 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                           IF ((value314).cmd) = (LogConcat)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)]
                                                                                                                                                   /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m[self]).mentries)]
                                                                                                                                                   /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                             "Failure of assertion at line 2469, column 33.")
                                                                                                                                                   /\ LET value442 == m[self] IN
                                                                                                                                                        /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value442)]
                                                                                                                                                        /\ \/ /\ LET value542 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                           \/ /\ LET yielded_fd142 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd142
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ IF ((value314).cmd) = (LogPop)
                                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value314).cnt))]
                                                                                                                                                              /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 2491, column 35.")
                                                                                                                                                              /\ LET value443 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value443)]
                                                                                                                                                                   /\ \/ /\ LET value543 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd143 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd143
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ log' = [log22 EXCEPT ![i] = ((log22)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 2511, column 35.")
                                                                                                                                                              /\ LET value444 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value444)]
                                                                                                                                                                   /\ \/ /\ LET value544 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd144 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd144
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                              /\ plog' = plog
                                                                                          ELSE /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                     THEN /\ \/ /\ LET value115 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value115), enabled |-> ((network)[j]).enabled]]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                             \/ /\ LET yielded_fd05 == (fd)[j] IN
                                                                                                                     /\ yielded_fd05
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                /\ UNCHANGED network
                                                                                                          /\ UNCHANGED << log, 
                                                                                                                          plog, 
                                                                                                                          fAdvCommitIdxCh >>
                                                                                                     ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                                    "Failure of assertion at line 2552, column 23.")
                                                                                                          /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                               LET value26 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                 IF ((value26).cmd) = (LogConcat)
                                                                                                                    THEN /\ LET plog18 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value26).entries)] IN
                                                                                                                              LET log23 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                LET value315 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                  IF ((value315).cmd) = (LogConcat)
                                                                                                                                     THEN /\ plog' = [plog18 EXCEPT ![i] = ((plog18)[i]) \o ((value315).entries)]
                                                                                                                                          /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m[self]).mentries)]
                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                    "Failure of assertion at line 2566, column 31.")
                                                                                                                                          /\ LET value445 == m[self] IN
                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value445)]
                                                                                                                                               /\ \/ /\ LET value545 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                  \/ /\ LET yielded_fd145 == (fd)[j] IN
                                                                                                                                                          /\ yielded_fd145
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                     ELSE /\ IF ((value315).cmd) = (LogPop)
                                                                                                                                                THEN /\ plog' = [plog18 EXCEPT ![i] = SubSeq((plog18)[i], 1, (Len((plog18)[i])) - ((value315).cnt))]
                                                                                                                                                     /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2588, column 33.")
                                                                                                                                                     /\ LET value446 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value446)]
                                                                                                                                                          /\ \/ /\ LET value546 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd146 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd146
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ log' = [log23 EXCEPT ![i] = ((log23)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2608, column 33.")
                                                                                                                                                     /\ LET value447 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value447)]
                                                                                                                                                          /\ \/ /\ LET value547 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ plog' = plog18
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd147 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd147
                                                                                                                                                                     /\ plog' = plog18
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                    ELSE /\ IF ((value26).cmd) = (LogPop)
                                                                                                                               THEN /\ LET plog19 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value26).cnt))] IN
                                                                                                                                         LET log24 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                           LET value316 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                             IF ((value316).cmd) = (LogConcat)
                                                                                                                                                THEN /\ plog' = [plog19 EXCEPT ![i] = ((plog19)[i]) \o ((value316).entries)]
                                                                                                                                                     /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2641, column 33.")
                                                                                                                                                     /\ LET value448 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value448)]
                                                                                                                                                          /\ \/ /\ LET value548 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd148 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd148
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ IF ((value316).cmd) = (LogPop)
                                                                                                                                                           THEN /\ plog' = [plog19 EXCEPT ![i] = SubSeq((plog19)[i], 1, (Len((plog19)[i])) - ((value316).cnt))]
                                                                                                                                                                /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2663, column 35.")
                                                                                                                                                                /\ LET value449 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value449)]
                                                                                                                                                                     /\ \/ /\ LET value549 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd149 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd149
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = [log24 EXCEPT ![i] = ((log24)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2683, column 35.")
                                                                                                                                                                /\ LET value450 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value450)]
                                                                                                                                                                     /\ \/ /\ LET value550 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ plog' = plog19
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd150 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd150
                                                                                                                                                                                /\ plog' = plog19
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                               ELSE /\ LET log25 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                         LET value317 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                           IF ((value317).cmd) = (LogConcat)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value317).entries)]
                                                                                                                                                   /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m[self]).mentries)]
                                                                                                                                                   /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                             "Failure of assertion at line 2714, column 33.")
                                                                                                                                                   /\ LET value451 == m[self] IN
                                                                                                                                                        /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value451)]
                                                                                                                                                        /\ \/ /\ LET value551 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                           \/ /\ LET yielded_fd151 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd151
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ IF ((value317).cmd) = (LogPop)
                                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value317).cnt))]
                                                                                                                                                              /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 2736, column 35.")
                                                                                                                                                              /\ LET value452 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value452)]
                                                                                                                                                                   /\ \/ /\ LET value552 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd152 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd152
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ log' = [log25 EXCEPT ![i] = ((log25)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 2756, column 35.")
                                                                                                                                                              /\ LET value453 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value453)]
                                                                                                                                                                   /\ \/ /\ LET value553 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd153 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd153
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                              /\ plog' = plog
                                                                                               /\ state' = state
                                                                               ELSE /\ IF (((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                                          THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                               /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                     THEN /\ \/ /\ LET value116 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value116), enabled |-> ((network)[j]).enabled]]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                             \/ /\ LET yielded_fd06 == (fd)[j] IN
                                                                                                                     /\ yielded_fd06
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                /\ UNCHANGED network
                                                                                                          /\ UNCHANGED << log, 
                                                                                                                          plog, 
                                                                                                                          fAdvCommitIdxCh >>
                                                                                                     ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                    "Failure of assertion at line 2800, column 23.")
                                                                                                          /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                               LET value27 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                 IF ((value27).cmd) = (LogConcat)
                                                                                                                    THEN /\ LET plog20 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value27).entries)] IN
                                                                                                                              LET log26 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                LET value318 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                  IF ((value318).cmd) = (LogConcat)
                                                                                                                                     THEN /\ plog' = [plog20 EXCEPT ![i] = ((plog20)[i]) \o ((value318).entries)]
                                                                                                                                          /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m[self]).mentries)]
                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                    "Failure of assertion at line 2814, column 31.")
                                                                                                                                          /\ LET value454 == m[self] IN
                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value454)]
                                                                                                                                               /\ \/ /\ LET value554 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                  \/ /\ LET yielded_fd154 == (fd)[j] IN
                                                                                                                                                          /\ yielded_fd154
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                     ELSE /\ IF ((value318).cmd) = (LogPop)
                                                                                                                                                THEN /\ plog' = [plog20 EXCEPT ![i] = SubSeq((plog20)[i], 1, (Len((plog20)[i])) - ((value318).cnt))]
                                                                                                                                                     /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2836, column 33.")
                                                                                                                                                     /\ LET value455 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value455)]
                                                                                                                                                          /\ \/ /\ LET value555 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd155 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd155
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ log' = [log26 EXCEPT ![i] = ((log26)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2856, column 33.")
                                                                                                                                                     /\ LET value456 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value456)]
                                                                                                                                                          /\ \/ /\ LET value556 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ plog' = plog20
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd156 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd156
                                                                                                                                                                     /\ plog' = plog20
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                    ELSE /\ IF ((value27).cmd) = (LogPop)
                                                                                                                               THEN /\ LET plog21 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value27).cnt))] IN
                                                                                                                                         LET log27 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                           LET value319 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                             IF ((value319).cmd) = (LogConcat)
                                                                                                                                                THEN /\ plog' = [plog21 EXCEPT ![i] = ((plog21)[i]) \o ((value319).entries)]
                                                                                                                                                     /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 2889, column 33.")
                                                                                                                                                     /\ LET value457 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value457)]
                                                                                                                                                          /\ \/ /\ LET value557 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd157 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd157
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ IF ((value319).cmd) = (LogPop)
                                                                                                                                                           THEN /\ plog' = [plog21 EXCEPT ![i] = SubSeq((plog21)[i], 1, (Len((plog21)[i])) - ((value319).cnt))]
                                                                                                                                                                /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2911, column 35.")
                                                                                                                                                                /\ LET value458 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value458)]
                                                                                                                                                                     /\ \/ /\ LET value558 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd158 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd158
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = [log27 EXCEPT ![i] = ((log27)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 2931, column 35.")
                                                                                                                                                                /\ LET value459 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value459)]
                                                                                                                                                                     /\ \/ /\ LET value559 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ plog' = plog21
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd159 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd159
                                                                                                                                                                                /\ plog' = plog21
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                               ELSE /\ LET log28 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                         LET value320 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                           IF ((value320).cmd) = (LogConcat)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value320).entries)]
                                                                                                                                                   /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m[self]).mentries)]
                                                                                                                                                   /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                             "Failure of assertion at line 2962, column 33.")
                                                                                                                                                   /\ LET value460 == m[self] IN
                                                                                                                                                        /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value460)]
                                                                                                                                                        /\ \/ /\ LET value560 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                           \/ /\ LET yielded_fd160 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd160
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ IF ((value320).cmd) = (LogPop)
                                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value320).cnt))]
                                                                                                                                                              /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 2984, column 35.")
                                                                                                                                                              /\ LET value461 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value461)]
                                                                                                                                                                   /\ \/ /\ LET value561 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd161 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd161
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ log' = [log28 EXCEPT ![i] = ((log28)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 3004, column 35.")
                                                                                                                                                              /\ LET value462 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value462)]
                                                                                                                                                                   /\ \/ /\ LET value562 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd162 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd162
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                              /\ plog' = plog
                                                                                          ELSE /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                     THEN /\ \/ /\ LET value117 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value117), enabled |-> ((network)[j]).enabled]]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                             \/ /\ LET yielded_fd07 == (fd)[j] IN
                                                                                                                     /\ yielded_fd07
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                /\ UNCHANGED network
                                                                                                          /\ UNCHANGED << log, 
                                                                                                                          plog, 
                                                                                                                          fAdvCommitIdxCh >>
                                                                                                     ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                                    "Failure of assertion at line 3045, column 23.")
                                                                                                          /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                               LET value28 == [cmd |-> LogPop, cnt |-> (Len((log)[i])) - ((m[self]).mprevLogIndex)] IN
                                                                                                                 IF ((value28).cmd) = (LogConcat)
                                                                                                                    THEN /\ LET plog22 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value28).entries)] IN
                                                                                                                              LET log29 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                LET value321 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                  IF ((value321).cmd) = (LogConcat)
                                                                                                                                     THEN /\ plog' = [plog22 EXCEPT ![i] = ((plog22)[i]) \o ((value321).entries)]
                                                                                                                                          /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m[self]).mentries)]
                                                                                                                                          /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                    "Failure of assertion at line 3059, column 31.")
                                                                                                                                          /\ LET value463 == m[self] IN
                                                                                                                                               /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value463)]
                                                                                                                                               /\ \/ /\ LET value563 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                  \/ /\ LET yielded_fd163 == (fd)[j] IN
                                                                                                                                                          /\ yielded_fd163
                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                     ELSE /\ IF ((value321).cmd) = (LogPop)
                                                                                                                                                THEN /\ plog' = [plog22 EXCEPT ![i] = SubSeq((plog22)[i], 1, (Len((plog22)[i])) - ((value321).cnt))]
                                                                                                                                                     /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 3081, column 33.")
                                                                                                                                                     /\ LET value464 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value464)]
                                                                                                                                                          /\ \/ /\ LET value564 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value564), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd164 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd164
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ log' = [log29 EXCEPT ![i] = ((log29)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 3101, column 33.")
                                                                                                                                                     /\ LET value465 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value465)]
                                                                                                                                                          /\ \/ /\ LET value565 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value565), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ plog' = plog22
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd165 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd165
                                                                                                                                                                     /\ plog' = plog22
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                    ELSE /\ IF ((value28).cmd) = (LogPop)
                                                                                                                               THEN /\ LET plog23 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value28).cnt))] IN
                                                                                                                                         LET log30 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                           LET value322 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                             IF ((value322).cmd) = (LogConcat)
                                                                                                                                                THEN /\ plog' = [plog23 EXCEPT ![i] = ((plog23)[i]) \o ((value322).entries)]
                                                                                                                                                     /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m[self]).mentries)]
                                                                                                                                                     /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                               "Failure of assertion at line 3134, column 33.")
                                                                                                                                                     /\ LET value466 == m[self] IN
                                                                                                                                                          /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value466)]
                                                                                                                                                          /\ \/ /\ LET value566 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value566), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                             \/ /\ LET yielded_fd166 == (fd)[j] IN
                                                                                                                                                                     /\ yielded_fd166
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                ELSE /\ IF ((value322).cmd) = (LogPop)
                                                                                                                                                           THEN /\ plog' = [plog23 EXCEPT ![i] = SubSeq((plog23)[i], 1, (Len((plog23)[i])) - ((value322).cnt))]
                                                                                                                                                                /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 3156, column 35.")
                                                                                                                                                                /\ LET value467 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value467)]
                                                                                                                                                                     /\ \/ /\ LET value567 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value567), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd167 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd167
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                                                           ELSE /\ log' = [log30 EXCEPT ![i] = ((log30)[i]) \o ((m[self]).mentries)]
                                                                                                                                                                /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                          "Failure of assertion at line 3176, column 35.")
                                                                                                                                                                /\ LET value468 == m[self] IN
                                                                                                                                                                     /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                     /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value468)]
                                                                                                                                                                     /\ \/ /\ LET value568 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                /\ ((network)[j]).enabled
                                                                                                                                                                                /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value568), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                /\ plog' = plog23
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                        \/ /\ LET yielded_fd168 == (fd)[j] IN
                                                                                                                                                                                /\ yielded_fd168
                                                                                                                                                                                /\ plog' = plog23
                                                                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                           /\ UNCHANGED network
                                                                                                                               ELSE /\ LET log31 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (m[self]).mprevLogIndex)] IN
                                                                                                                                         LET value323 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                           IF ((value323).cmd) = (LogConcat)
                                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value323).entries)]
                                                                                                                                                   /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m[self]).mentries)]
                                                                                                                                                   /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                             "Failure of assertion at line 3207, column 33.")
                                                                                                                                                   /\ LET value469 == m[self] IN
                                                                                                                                                        /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value469)]
                                                                                                                                                        /\ \/ /\ LET value569 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value569), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                           \/ /\ LET yielded_fd169 == (fd)[j] IN
                                                                                                                                                                   /\ yielded_fd169
                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                              ELSE /\ IF ((value323).cmd) = (LogPop)
                                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value323).cnt))]
                                                                                                                                                              /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 3229, column 35.")
                                                                                                                                                              /\ LET value470 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value470)]
                                                                                                                                                                   /\ \/ /\ LET value570 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value570), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd170 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd170
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                         ELSE /\ log' = [log31 EXCEPT ![i] = ((log31)[i]) \o ((m[self]).mentries)]
                                                                                                                                                              /\ Assert(((m[self]).mcommitIndex) <= (Len((log')[i])), 
                                                                                                                                                                        "Failure of assertion at line 3249, column 35.")
                                                                                                                                                              /\ LET value471 == m[self] IN
                                                                                                                                                                   /\ (Len((fAdvCommitIdxCh)[i])) < (BufferSize)
                                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value471)]
                                                                                                                                                                   /\ \/ /\ LET value571 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value571), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                      \/ /\ LET yielded_fd171 == (fd)[j] IN
                                                                                                                                                                              /\ yielded_fd171
                                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                                              /\ plog' = plog
                                                                                               /\ state' = state
                                                                                    /\ UNCHANGED << leader, 
                                                                                                    leaderTimeout >>
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
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      /\ UNCHANGED << nextIndex, 
                                                                                                      matchIndex >>
                                                                                 ELSE /\ LET i == self IN
                                                                                           LET j == (m[self]).msource IN
                                                                                             /\ Assert(((m[self]).mterm) = ((currentTerm')[i]), 
                                                                                                       "Failure of assertion at line 3293, column 21.")
                                                                                             /\ IF (m[self]).msuccess
                                                                                                   THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                        /\ UNCHANGED matchIndex
                                                                      ELSE /\ IF ((m[self]).mterm) < ((currentTerm)[self])
                                                                                 THEN /\ TRUE
                                                                                      /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                      /\ UNCHANGED << nextIndex, 
                                                                                                      matchIndex >>
                                                                                 ELSE /\ LET i == self IN
                                                                                           LET j == (m[self]).msource IN
                                                                                             /\ Assert(((m[self]).mterm) = ((currentTerm)[i]), 
                                                                                                       "Failure of assertion at line 3313, column 21.")
                                                                                             /\ IF (m[self]).msuccess
                                                                                                   THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = ((m[self]).mmatchIndex) + (1)]]
                                                                                                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [(matchIndex)[i] EXCEPT ![j] = (m[self]).mmatchIndex]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [(nextIndex)[i] EXCEPT ![j] = Max({(((nextIndex)[i])[j]) - (1), 1})]]
                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                        /\ UNCHANGED matchIndex
                                                                           /\ UNCHANGED << state, 
                                                                                           currentTerm, 
                                                                                           votedFor, 
                                                                                           leader >>
                                                                /\ UNCHANGED << network, 
                                                                                log, 
                                                                                plog >>
                                                           ELSE /\ IF ((m[self]).mtype) = (ProposeMessage)
                                                                      THEN /\ LET i == self IN
                                                                                IF Debug
                                                                                   THEN /\ PrintT(<<"HandleProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i]>>)
                                                                                        /\ IF ((state)[i]) = (Leader)
                                                                                              THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m[self]).mcmd] IN
                                                                                                        /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                                                                        /\ LET value60 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                             IF ((value60).cmd) = (LogConcat)
                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value60).entries)]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                ELSE /\ IF ((value60).cmd) = (LogPop)
                                                                                                                           THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value60).cnt))]
                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                /\ plog' = plog
                                                                                                   /\ UNCHANGED network
                                                                                              ELSE /\ IF ((leader)[i]) # (Nil)
                                                                                                         THEN /\ LET j == (leader)[i] IN
                                                                                                                   \/ /\ LET value70 == [mtype |-> ProposeMessage, mcmd |-> (m[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value70), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                   \/ /\ LET yielded_fd20 == (fd)[j] IN
                                                                                                                           /\ yielded_fd20
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                      /\ UNCHANGED network
                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                              /\ UNCHANGED network
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   plog >>
                                                                                   ELSE /\ IF ((state)[i]) = (Leader)
                                                                                              THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m[self]).mcmd] IN
                                                                                                        /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                                                                        /\ LET value61 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                             IF ((value61).cmd) = (LogConcat)
                                                                                                                THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value61).entries)]
                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                ELSE /\ IF ((value61).cmd) = (LogPop)
                                                                                                                           THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value61).cnt))]
                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                                /\ plog' = plog
                                                                                                   /\ UNCHANGED network
                                                                                              ELSE /\ IF ((leader)[i]) # (Nil)
                                                                                                         THEN /\ LET j == (leader)[i] IN
                                                                                                                   \/ /\ LET value71 == [mtype |-> ProposeMessage, mcmd |-> (m[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value71), enabled |-> ((network)[j]).enabled]]
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                   \/ /\ LET yielded_fd21 == (fd)[j] IN
                                                                                                                           /\ yielded_fd21
                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                                      /\ UNCHANGED network
                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                                                              /\ UNCHANGED network
                                                                                                   /\ UNCHANGED << log, 
                                                                                                                   plog >>
                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop_"]
                                                                           /\ UNCHANGED << network, 
                                                                                           log, 
                                                                                           plog >>
                                                                /\ UNCHANGED << state, 
                                                                                currentTerm, 
                                                                                nextIndex, 
                                                                                matchIndex, 
                                                                                votedFor, 
                                                                                leader >>
                                                     /\ UNCHANGED << leaderTimeout, 
                                                                     fAdvCommitIdxCh >>
                                          /\ UNCHANGED << votesResponded, 
                                                          votesGranted, 
                                                          becomeLeaderCh >>
                    /\ UNCHANGED << fd, commitIndex, propCh, acctCh, 
                                    appendEntriesCh, netListenerSrvId, 
                                    propChListenerSrvId, requestVoteSrvId, 
                                    appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    fAdvCommitSrvId, crasherSrvId, idx, m, 
                                    srvId, idx0, m0, srvId0, idx1, srvId1, 
                                    idx2, srvId2, newCommitIndex, srvId3, 
                                    srvId4, m1, srvId5, srvId6 >>

s0(self) == serverLoop_(self) \/ handleMsg_(self)

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ LET i == srvId0[self] IN
                                    /\ (Len((propCh)[i])) > (0)
                                    /\ LET res00 == Head((propCh)[i]) IN
                                         /\ propCh' = [propCh EXCEPT ![i] = Tail((propCh)[i])]
                                         /\ LET yielded_propCh0 == res00 IN
                                              /\ m0' = [m0 EXCEPT ![self] = yielded_propCh0]
                                              /\ IF Debug
                                                    THEN /\ PrintT(<<"ReceiveProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i], m0'[self]>>)
                                                         /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << propCh, m0 >>
                    /\ UNCHANGED << network, fd, state, currentTerm, 
                                    commitIndex, nextIndex, matchIndex, log, 
                                    plog, votedFor, votesResponded, 
                                    votesGranted, leader, acctCh, 
                                    leaderTimeout, appendEntriesCh, 
                                    becomeLeaderCh, fAdvCommitIdxCh, 
                                    netListenerSrvId, propChListenerSrvId, 
                                    requestVoteSrvId, appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    fAdvCommitSrvId, crasherSrvId, idx, m, 
                                    srvId, idx0, srvId0, idx1, srvId1, idx2, 
                                    srvId2, newCommitIndex, srvId3, srvId4, m1, 
                                    srvId5, srvId6 >>

handleMsg(self) == /\ pc[self] = "handleMsg"
                   /\ Assert(((m0[self]).mtype) = (ProposeMessage), 
                             "Failure of assertion at line 3442, column 7.")
                   /\ LET i == srvId0[self] IN
                        IF Debug
                           THEN /\ PrintT(<<"HandleProposeMessage", i, (currentTerm)[i], (state)[i], (leader)[i]>>)
                                /\ IF ((state)[i]) = (Leader)
                                      THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m0[self]).mcmd] IN
                                                /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                /\ LET value80 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                     IF ((value80).cmd) = (LogConcat)
                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value80).entries)]
                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                        ELSE /\ IF ((value80).cmd) = (LogPop)
                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value80).cnt))]
                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                        /\ plog' = plog
                                           /\ UNCHANGED network
                                      ELSE /\ IF ((leader)[i]) # (Nil)
                                                 THEN /\ LET j == (leader)[i] IN
                                                           \/ /\ LET value90 == [mtype |-> ProposeMessage, mcmd |-> (m0[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                   /\ ((network)[j]).enabled
                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value90), enabled |-> ((network)[j]).enabled]]
                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                           \/ /\ LET yielded_fd30 == (fd)[j] IN
                                                                   /\ yielded_fd30
                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                              /\ UNCHANGED network
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                      /\ UNCHANGED network
                                           /\ UNCHANGED << log, plog >>
                           ELSE /\ IF ((state)[i]) = (Leader)
                                      THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m0[self]).mcmd] IN
                                                /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                /\ LET value81 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                     IF ((value81).cmd) = (LogConcat)
                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value81).entries)]
                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                        ELSE /\ IF ((value81).cmd) = (LogPop)
                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - ((value81).cnt))]
                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                        /\ plog' = plog
                                           /\ UNCHANGED network
                                      ELSE /\ IF ((leader)[i]) # (Nil)
                                                 THEN /\ LET j == (leader)[i] IN
                                                           \/ /\ LET value91 == [mtype |-> ProposeMessage, mcmd |-> (m0[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                   /\ ((network)[j]).enabled
                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value91), enabled |-> ((network)[j]).enabled]]
                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                           \/ /\ LET yielded_fd31 == (fd)[j] IN
                                                                   /\ yielded_fd31
                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                              /\ UNCHANGED network
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                      /\ UNCHANGED network
                                           /\ UNCHANGED << log, plog >>
                   /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                   nextIndex, matchIndex, votedFor, 
                                   votesResponded, votesGranted, leader, 
                                   propCh, acctCh, leaderTimeout, 
                                   appendEntriesCh, becomeLeaderCh, 
                                   fAdvCommitIdxCh, netListenerSrvId, 
                                   propChListenerSrvId, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, fAdvCommitSrvId, 
                                   crasherSrvId, idx, m, srvId, idx0, m0, 
                                   srvId0, idx1, srvId1, idx2, srvId2, 
                                   newCommitIndex, srvId3, srvId4, m1, srvId5, 
                                   srvId6 >>

s1(self) == serverLoop(self) \/ handleMsg(self)

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
                                                               /\ idx1' = [idx1 EXCEPT ![self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                          ELSE /\ idx1' = [idx1 EXCEPT ![self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                          /\ UNCHANGED << state, currentTerm, 
                                                          votedFor, 
                                                          votesResponded, 
                                                          votesGranted, leader, 
                                                          idx1 >>
                               /\ UNCHANGED << network, fd, commitIndex, 
                                               nextIndex, matchIndex, log, 
                                               plog, propCh, acctCh, 
                                               leaderTimeout, appendEntriesCh, 
                                               becomeLeaderCh, fAdvCommitIdxCh, 
                                               netListenerSrvId, 
                                               propChListenerSrvId, 
                                               requestVoteSrvId, 
                                               appendEntriesSrvId, 
                                               advanceCommitIndexSrvId, 
                                               becomeLeaderSrvId, 
                                               fAdvCommitSrvId, crasherSrvId, 
                                               idx, m, srvId, idx0, m0, srvId0, 
                                               srvId1, idx2, srvId2, 
                                               newCommitIndex, srvId3, srvId4, 
                                               m1, srvId5, srvId6 >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx1[self]) <= (NumServers)
                               THEN /\ IF (idx1[self]) # (srvId1[self])
                                          THEN /\ \/ /\ LET value100 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId1[self]], mlastLogTerm |-> LastTerm((log)[srvId1[self]]), mlastLogIndex |-> Len((log)[srvId1[self]]), msource |-> srvId1[self], mdest |-> idx1[self]] IN
                                                          /\ ((network)[idx1[self]]).enabled
                                                          /\ (Len(((network)[idx1[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![idx1[self]] = [queue |-> Append(((network)[idx1[self]]).queue, value100), enabled |-> ((network)[idx1[self]]).enabled]]
                                                          /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                  \/ /\ LET yielded_fd40 == (fd)[idx1[self]] IN
                                                          /\ yielded_fd40
                                                          /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                     /\ UNCHANGED network
                                          ELSE /\ idx1' = [idx1 EXCEPT ![self] = (idx1[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                               /\ UNCHANGED network
                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverRequestVoteLoop"]
                                    /\ UNCHANGED << network, idx1 >>
                         /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                         nextIndex, matchIndex, log, plog, 
                                         votedFor, votesResponded, 
                                         votesGranted, leader, propCh, acctCh, 
                                         leaderTimeout, appendEntriesCh, 
                                         becomeLeaderCh, fAdvCommitIdxCh, 
                                         netListenerSrvId, propChListenerSrvId, 
                                         requestVoteSrvId, appendEntriesSrvId, 
                                         advanceCommitIndexSrvId, 
                                         becomeLeaderSrvId, fAdvCommitSrvId, 
                                         crasherSrvId, idx, m, srvId, idx0, m0, 
                                         srvId0, srvId1, idx2, srvId2, 
                                         newCommitIndex, srvId3, srvId4, m1, 
                                         srvId5, srvId6 >>

s2(self) == serverRequestVoteLoop(self) \/ requestVoteLoop(self)

serverAppendEntriesLoop(self) == /\ pc[self] = "serverAppendEntriesLoop"
                                 /\ IF appendEntriesCh
                                       THEN /\ ((state)[srvId2[self]]) = (Leader)
                                            /\ idx2' = [idx2 EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                            /\ idx2' = idx2
                                 /\ UNCHANGED << network, fd, state, 
                                                 currentTerm, commitIndex, 
                                                 nextIndex, matchIndex, log, 
                                                 plog, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, propCh, acctCh, 
                                                 leaderTimeout, 
                                                 appendEntriesCh, 
                                                 becomeLeaderCh, 
                                                 fAdvCommitIdxCh, 
                                                 netListenerSrvId, 
                                                 propChListenerSrvId, 
                                                 requestVoteSrvId, 
                                                 appendEntriesSrvId, 
                                                 advanceCommitIndexSrvId, 
                                                 becomeLeaderSrvId, 
                                                 fAdvCommitSrvId, crasherSrvId, 
                                                 idx, m, srvId, idx0, m0, 
                                                 srvId0, idx1, srvId1, srvId2, 
                                                 newCommitIndex, srvId3, 
                                                 srvId4, m1, srvId5, srvId6 >>

appendEntriesLoop(self) == /\ pc[self] = "appendEntriesLoop"
                           /\ IF (((state)[srvId2[self]]) = (Leader)) /\ ((idx2[self]) <= (NumServers))
                                 THEN /\ IF (idx2[self]) # (srvId2[self])
                                            THEN /\ LET prevLogIndex1 == (((nextIndex)[srvId2[self]])[idx2[self]]) - (1) IN
                                                      LET prevLogTerm1 == IF (prevLogIndex1) > (0) THEN (((log)[srvId2[self]])[prevLogIndex1]).term ELSE 0 IN
                                                        LET entries1 == SubSeq((log)[srvId2[self]], ((nextIndex)[srvId2[self]])[idx2[self]], Len((log)[srvId2[self]])) IN
                                                          \/ /\ LET value118 == [mtype |-> AppendEntriesRequest, mterm |-> (currentTerm)[srvId2[self]], mprevLogIndex |-> prevLogIndex1, mprevLogTerm |-> prevLogTerm1, mentries |-> entries1, mcommitIndex |-> (commitIndex)[srvId2[self]], msource |-> srvId2[self], mdest |-> idx2[self]] IN
                                                                  /\ ((network)[idx2[self]]).enabled
                                                                  /\ (Len(((network)[idx2[self]]).queue)) < (BufferSize)
                                                                  /\ network' = [network EXCEPT ![idx2[self]] = [queue |-> Append(((network)[idx2[self]]).queue, value118), enabled |-> ((network)[idx2[self]]).enabled]]
                                                                  /\ idx2' = [idx2 EXCEPT ![self] = (idx2[self]) + (1)]
                                                                  /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                          \/ /\ LET yielded_fd50 == (fd)[idx2[self]] IN
                                                                  /\ yielded_fd50
                                                                  /\ idx2' = [idx2 EXCEPT ![self] = (idx2[self]) + (1)]
                                                                  /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                             /\ UNCHANGED network
                                            ELSE /\ idx2' = [idx2 EXCEPT ![self] = (idx2[self]) + (1)]
                                                 /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
                                                 /\ UNCHANGED network
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "serverAppendEntriesLoop"]
                                      /\ UNCHANGED << network, idx2 >>
                           /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                           nextIndex, matchIndex, log, plog, 
                                           votedFor, votesResponded, 
                                           votesGranted, leader, propCh, 
                                           acctCh, leaderTimeout, 
                                           appendEntriesCh, becomeLeaderCh, 
                                           fAdvCommitIdxCh, netListenerSrvId, 
                                           propChListenerSrvId, 
                                           requestVoteSrvId, 
                                           appendEntriesSrvId, 
                                           advanceCommitIndexSrvId, 
                                           becomeLeaderSrvId, fAdvCommitSrvId, 
                                           crasherSrvId, idx, m, srvId, idx0, 
                                           m0, srvId0, idx1, srvId1, srvId2, 
                                           newCommitIndex, srvId3, srvId4, m1, 
                                           srvId5, srvId6 >>

s3(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)

serverAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverAdvanceCommitIndexLoop"
                                      /\ IF TRUE
                                            THEN /\ ((state)[srvId3[self]]) = (Leader)
                                                 /\ LET i == srvId3[self] IN
                                                      LET maxAgreeIndex == FindMaxAgreeIndex((log)[i], i, (matchIndex)[i]) IN
                                                        LET nCommitIndex == IF ((maxAgreeIndex) # (Nil)) /\ (((((log)[i])[maxAgreeIndex]).term) = ((currentTerm)[i])) THEN maxAgreeIndex ELSE (commitIndex)[i] IN
                                                          /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                                          /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                                    "Failure of assertion at line 3639, column 11.")
                                                          /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                 /\ UNCHANGED newCommitIndex
                                      /\ UNCHANGED << network, fd, state, 
                                                      currentTerm, commitIndex, 
                                                      nextIndex, matchIndex, 
                                                      log, plog, votedFor, 
                                                      votesResponded, 
                                                      votesGranted, leader, 
                                                      propCh, acctCh, 
                                                      leaderTimeout, 
                                                      appendEntriesCh, 
                                                      becomeLeaderCh, 
                                                      fAdvCommitIdxCh, 
                                                      netListenerSrvId, 
                                                      propChListenerSrvId, 
                                                      requestVoteSrvId, 
                                                      appendEntriesSrvId, 
                                                      advanceCommitIndexSrvId, 
                                                      becomeLeaderSrvId, 
                                                      fAdvCommitSrvId, 
                                                      crasherSrvId, idx, m, 
                                                      srvId, idx0, m0, srvId0, 
                                                      idx1, srvId1, idx2, 
                                                      srvId2, srvId3, srvId4, 
                                                      m1, srvId5, srvId6 >>

applyLoop(self) == /\ pc[self] = "applyLoop"
                   /\ IF ((commitIndex)[srvId3[self]]) < (newCommitIndex[self])
                         THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId3[self]] = ((commitIndex)[srvId3[self]]) + (1)]
                              /\ LET i == srvId3[self] IN
                                   LET k == (commitIndex')[i] IN
                                     LET entry == ((log)[i])[k] IN
                                       LET cmd == (entry).cmd IN
                                         IF Debug
                                            THEN /\ PrintT(<<"ServerAccept", i, cmd>>)
                                                 /\ LET value120 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                                      /\ (Len((acctCh)[i])) < (BufferSize)
                                                      /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value120)]
                                                      /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                                            ELSE /\ LET value121 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                                      /\ (Len((acctCh)[i])) < (BufferSize)
                                                      /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value121)]
                                                      /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverAdvanceCommitIndexLoop"]
                              /\ UNCHANGED << commitIndex, acctCh >>
                   /\ UNCHANGED << network, fd, state, currentTerm, nextIndex, 
                                   matchIndex, log, plog, votedFor, 
                                   votesResponded, votesGranted, leader, 
                                   propCh, leaderTimeout, appendEntriesCh, 
                                   becomeLeaderCh, fAdvCommitIdxCh, 
                                   netListenerSrvId, propChListenerSrvId, 
                                   requestVoteSrvId, appendEntriesSrvId, 
                                   advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                   fAdvCommitSrvId, crasherSrvId, idx, m, 
                                   srvId, idx0, m0, srvId0, idx1, srvId1, idx2, 
                                   srvId2, newCommitIndex, srvId3, srvId4, m1, 
                                   srvId5, srvId6 >>

s4(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)

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
                                                votesGranted, propCh, acctCh, 
                                                leaderTimeout, fAdvCommitIdxCh, 
                                                netListenerSrvId, 
                                                propChListenerSrvId, 
                                                requestVoteSrvId, 
                                                appendEntriesSrvId, 
                                                advanceCommitIndexSrvId, 
                                                becomeLeaderSrvId, 
                                                fAdvCommitSrvId, crasherSrvId, 
                                                idx, m, srvId, idx0, m0, 
                                                srvId0, idx1, srvId1, idx2, 
                                                srvId2, newCommitIndex, srvId3, 
                                                srvId4, m1, srvId5, srvId6 >>

s5(self) == serverBecomeLeaderLoop(self)

serverFollowerAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverFollowerAdvanceCommitIndexLoop"
                                              /\ IF TRUE
                                                    THEN /\ (Len((fAdvCommitIdxCh)[srvId5[self]])) > (0)
                                                         /\ LET res20 == Head((fAdvCommitIdxCh)[srvId5[self]]) IN
                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![srvId5[self]] = Tail((fAdvCommitIdxCh)[srvId5[self]])]
                                                              /\ LET yielded_fAdvCommitIdxCh0 == res20 IN
                                                                   /\ m1' = [m1 EXCEPT ![self] = yielded_fAdvCommitIdxCh0]
                                                                   /\ pc' = [pc EXCEPT ![self] = "acctLoop"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                         /\ UNCHANGED << fAdvCommitIdxCh, 
                                                                         m1 >>
                                              /\ UNCHANGED << network, fd, 
                                                              state, 
                                                              currentTerm, 
                                                              commitIndex, 
                                                              nextIndex, 
                                                              matchIndex, log, 
                                                              plog, votedFor, 
                                                              votesResponded, 
                                                              votesGranted, 
                                                              leader, propCh, 
                                                              acctCh, 
                                                              leaderTimeout, 
                                                              appendEntriesCh, 
                                                              becomeLeaderCh, 
                                                              netListenerSrvId, 
                                                              propChListenerSrvId, 
                                                              requestVoteSrvId, 
                                                              appendEntriesSrvId, 
                                                              advanceCommitIndexSrvId, 
                                                              becomeLeaderSrvId, 
                                                              fAdvCommitSrvId, 
                                                              crasherSrvId, 
                                                              idx, m, srvId, 
                                                              idx0, m0, srvId0, 
                                                              idx1, srvId1, 
                                                              idx2, srvId2, 
                                                              newCommitIndex, 
                                                              srvId3, srvId4, 
                                                              srvId5, srvId6 >>

acctLoop(self) == /\ pc[self] = "acctLoop"
                  /\ IF ((commitIndex)[srvId5[self]]) < ((m1[self]).mcommitIndex)
                        THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId5[self]] = ((commitIndex)[srvId5[self]]) + (1)]
                             /\ LET i == srvId5[self] IN
                                  LET k == (commitIndex')[i] IN
                                    LET entry == ((log)[i])[k] IN
                                      LET cmd == (entry).cmd IN
                                        IF Debug
                                           THEN /\ PrintT(<<"ServerAccept", i, cmd>>)
                                                /\ LET value130 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                                     /\ (Len((acctCh)[i])) < (BufferSize)
                                                     /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value130)]
                                                     /\ pc' = [pc EXCEPT ![self] = "acctLoop"]
                                           ELSE /\ LET value131 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                                     /\ (Len((acctCh)[i])) < (BufferSize)
                                                     /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value131)]
                                                     /\ pc' = [pc EXCEPT ![self] = "acctLoop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverFollowerAdvanceCommitIndexLoop"]
                             /\ UNCHANGED << commitIndex, acctCh >>
                  /\ UNCHANGED << network, fd, state, currentTerm, nextIndex, 
                                  matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, propCh, 
                                  leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, fAdvCommitIdxCh, 
                                  netListenerSrvId, propChListenerSrvId, 
                                  requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  fAdvCommitSrvId, crasherSrvId, idx, m, srvId, 
                                  idx0, m0, srvId0, idx1, srvId1, idx2, srvId2, 
                                  newCommitIndex, srvId3, srvId4, m1, srvId5, 
                                  srvId6 >>

s6(self) == serverFollowerAdvanceCommitIndexLoop(self) \/ acctLoop(self)

serverCrash(self) == /\ pc[self] = "serverCrash"
                     /\ LET value140 == FALSE IN
                          /\ network' = [network EXCEPT ![srvId6[self]] = [queue |-> ((network)[srvId6[self]]).queue, enabled |-> value140]]
                          /\ pc' = [pc EXCEPT ![self] = "fdUpdate"]
                     /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                     nextIndex, matchIndex, log, plog, 
                                     votedFor, votesResponded, votesGranted, 
                                     leader, propCh, acctCh, leaderTimeout, 
                                     appendEntriesCh, becomeLeaderCh, 
                                     fAdvCommitIdxCh, netListenerSrvId, 
                                     propChListenerSrvId, requestVoteSrvId, 
                                     appendEntriesSrvId, 
                                     advanceCommitIndexSrvId, 
                                     becomeLeaderSrvId, fAdvCommitSrvId, 
                                     crasherSrvId, idx, m, srvId, idx0, m0, 
                                     srvId0, idx1, srvId1, idx2, srvId2, 
                                     newCommitIndex, srvId3, srvId4, m1, 
                                     srvId5, srvId6 >>

fdUpdate(self) == /\ pc[self] = "fdUpdate"
                  /\ LET value150 == TRUE IN
                       /\ fd' = [fd EXCEPT ![srvId6[self]] = value150]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << network, state, currentTerm, commitIndex, 
                                  nextIndex, matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, propCh, 
                                  acctCh, leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, fAdvCommitIdxCh, 
                                  netListenerSrvId, propChListenerSrvId, 
                                  requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  fAdvCommitSrvId, crasherSrvId, idx, m, srvId, 
                                  idx0, m0, srvId0, idx1, srvId1, idx2, srvId2, 
                                  newCommitIndex, srvId3, srvId4, m1, srvId5, 
                                  srvId6 >>

crasher(self) == serverCrash(self) \/ fdUpdate(self)

sndReq == /\ pc[0] = "sndReq"
          /\ LET value160 == [mtype |-> ProposeMessage, mcmd |-> [data |-> "hello"]] IN
               /\ (Len((propCh)[1])) < (BufferSize)
               /\ propCh' = [propCh EXCEPT ![1] = Append((propCh)[1], value160)]
               /\ pc' = [pc EXCEPT ![0] = "Done"]
          /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                          nextIndex, matchIndex, log, plog, votedFor, 
                          votesResponded, votesGranted, leader, acctCh, 
                          leaderTimeout, appendEntriesCh, becomeLeaderCh, 
                          fAdvCommitIdxCh, netListenerSrvId, 
                          propChListenerSrvId, requestVoteSrvId, 
                          appendEntriesSrvId, advanceCommitIndexSrvId, 
                          becomeLeaderSrvId, fAdvCommitSrvId, crasherSrvId, 
                          idx, m, srvId, idx0, m0, srvId0, idx1, srvId1, idx2, 
                          srvId2, newCommitIndex, srvId3, srvId4, m1, srvId5, 
                          srvId6 >>

proposer == sndReq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == proposer
           \/ (\E self \in ServerNetListenerSet: s0(self))
           \/ (\E self \in ServerPropChListenerSet: s1(self))
           \/ (\E self \in ServerRequestVoteSet: s2(self))
           \/ (\E self \in ServerAppendEntriesSet: s3(self))
           \/ (\E self \in ServerAdvanceCommitIndexSet: s4(self))
           \/ (\E self \in ServerBecomeLeaderSet: s5(self))
           \/ (\E self \in ServerFollowerAdvanceCommitIndexSet: s6(self))
           \/ (\E self \in ServerCrasherSet: crasher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerNetListenerSet : WF_vars(s0(self))
        /\ \A self \in ServerPropChListenerSet : WF_vars(s1(self))
        /\ \A self \in ServerRequestVoteSet : WF_vars(s2(self))
        /\ \A self \in ServerAppendEntriesSet : WF_vars(s3(self))
        /\ \A self \in ServerAdvanceCommitIndexSet : WF_vars(s4(self))
        /\ \A self \in ServerBecomeLeaderSet : WF_vars(s5(self))
        /\ \A self \in ServerFollowerAdvanceCommitIndexSet : WF_vars(s6(self))
        /\ \A self \in ServerCrasherSet : WF_vars(crasher(self))
        /\ WF_vars(proposer)

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
                                        /\ log[i][k] = log[j][k]
                                        /\ acctCh[i][k] = acctCh[j][k]

plogOK == \A i \in ServerSet: log[i] = plog[i]

TermOK == \A i \in ServerSet: currentTerm[i] <= MaxTerm
CommitIndexOK == \A i \in ServerSet: commitIndex[i] <= MaxCommitIndex

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

LeaderExists == \E i \in ServerSet: state[i] = Leader

\* Expected this to be violated if NumServers > 1,
\* but TLC doesn't report violation in case of NumServers = 2 because 
\* of using temporal properties and state constraints at the same time. 
\* TLC reports violation when NumServers = 3.
ElectionLiveness == []<>LeaderExists

AcceptLiveness == <>(LeaderExists => \A i \in ServerSet: Len(acctCh[i]) > 0)

=============================================================================
