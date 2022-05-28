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

        ServerRequestVoteSet                == (1*NumServers+1)..(2*NumServers)
        ServerAppendEntriesSet              == (2*NumServers+1)..(3*NumServers)
        ServerAdvanceCommitIndexSet         == (3*NumServers+1)..(4*NumServers)
        ServerBecomeLeaderSet               == (4*NumServers+1)..(5*NumServers)
        ServerFollowerAdvanceCommitIndexSet == (5*NumServers+1)..(6*NumServers)

        ServerCrasherSet == IF ExploreFail 
                            THEN (6*NumServers+1)..(6*NumServers+MaxNodeFail)
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

            either {
                m := net[self];
                assert m.mdest = self;
            } or {
                m := propCh[self];
            };

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
                                log[i]  := SubSeq(log[i], 1, Len(log[i]) - 1);
                                plog[i] := [cmd |-> LogPop];
                            };

                            \* no conflict: append entry
                            if (
                                /\ m.mentries /= << >>
                                /\ Len(log[i]) = m.mprevLogIndex
                            ) {
                                log[i]  := log[i] \o m.mentries;
                                plog[i] := [cmd |-> LogConcat, entries |-> m.mentries];
                            };

                            \* already done with request
                            if (
                                \/ m.mentries = << >>
                                \/ /\ m.mentries /= << >>
                                   /\ Len(log[i]) >= index
                                   /\ log[i][index].term = m.mentries[1].term
                            ) {
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
                    debug(<<"HandleProposeMessage", i, currentTerm[i], state[i]>>);

                    if (state[i] = Leader) {
                        with (entry = [term   |-> currentTerm[i],
                                       cmd    |-> m.mcmd]
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
    block:
        await FALSE;
    }

    archetype AProposer(ref propCh[_]) {
    sndReq:
        propCh[1] := [
            mtype |-> ProposeMessage,
            mcmd  |-> [data |-> "hello"]
        ];
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

        requestVoteSrvId        = [i \in ServerRequestVoteSet                |-> i - 1*NumServers];
        appendEntriesSrvId      = [i \in ServerAppendEntriesSet              |-> i - 2*NumServers];
        advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet         |-> i - 3*NumServers];
        becomeLeaderSrvId       = [i \in ServerBecomeLeaderSet               |-> i - 4*NumServers];
        fAdvCommitSrvId         = [i \in ServerFollowerAdvanceCommitIndexSet |-> i - 5*NumServers];
        crasherSrvId            = [i \in ServerCrasherSet                    |-> i - 6*NumServers];

    fair process (s0 \in ServerSet) == instance AServer(
        s0,
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

    fair process (s1 \in ServerRequestVoteSet) == instance AServerRequestVote(
        requestVoteSrvId[s1],
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

    fair process (s2 \in ServerAppendEntriesSet) == instance AServerAppendEntries(
        appendEntriesSrvId[s2],
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

    fair process (s3 \in ServerAdvanceCommitIndexSet) == instance AServerAdvanceCommitIndex(
        advanceCommitIndexSrvId[s3],
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

    fair process (s4 \in ServerBecomeLeaderSet) == instance AServerBecomeLeader(
        becomeLeaderSrvId[s4],
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

    fair process(s5 \in ServerFollowerAdvanceCommitIndexSet) == instance AServerFollowerAdvanceCommitIndex(
        fAdvCommitSrvId[s5],
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
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; state = [i \in ServerSet |-> Follower]; currentTerm = [i \in ServerSet |-> 1]; commitIndex = [i \in ServerSet |-> 0]; nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]; matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]; log = [i \in ServerSet |-> <<>>]; plog = [i \in ServerSet |-> <<>>]; votedFor = [i \in ServerSet |-> Nil]; votesResponded = [i \in ServerSet |-> {}]; votesGranted = [i \in ServerSet |-> {}]; leader = [i \in ServerSet |-> Nil]; propCh = [i \in ServerSet |-> <<>>]; acctCh = [i \in ServerSet |-> <<>>]; leaderTimeout = TRUE; appendEntriesCh = TRUE; becomeLeaderCh = [i \in ServerSet |-> IF (NumServers) > (1) THEN <<>> ELSE <<TRUE>>]; fAdvCommitIdxCh = [i \in ServerSet |-> <<>>]; requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]; appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]; advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]; becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]; fAdvCommitSrvId = [i \in ServerFollowerAdvanceCommitIndexSet |-> (i) - ((5) * (NumServers))]; crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((6) * (NumServers))];
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
    ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
    ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
    ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
    ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
    ServerFollowerAdvanceCommitIndexSet == (((5) * (NumServers)) + (1)) .. ((6) * (NumServers))
    ServerCrasherSet == IF ExploreFail THEN (((6) * (NumServers)) + (1)) .. (((6) * (NumServers)) + (MaxNodeFail)) ELSE {}
    NodeSet == ServerSet
    KeySet == {}
  }
  
  fair process (s0 \in ServerSet)
    variables idx = 1; m; srvId = self;
  {
    serverLoop:
      if (TRUE) {
        either {
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
        } or {
          await (Len((propCh)[self])) > (0);
          with (res00 = Head((propCh)[self])) {
            propCh := [propCh EXCEPT ![self] = Tail((propCh)[self])];
            with (yielded_propCh0 = res00) {
              m := yielded_propCh0;
              goto handleMsg;
            };
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
                  with (value15 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value15), enabled |-> ((network)[j]).enabled]];
                    if (Debug) {
                      print <<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>;
                      goto serverLoop;
                    } else {
                      goto serverLoop;
                    };
                  };
                } or {
                  with (yielded_fd5 = (fd)[j]) {
                    await yielded_fd5;
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
                  with (value16 = [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j]) {
                    await ((network)[j]).enabled;
                    await (Len(((network)[j]).queue)) < (BufferSize);
                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]];
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
                  with (yielded_fd6 = (fd)[j]) {
                    await yielded_fd6;
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
                with (leader1 = [leader EXCEPT ![self] = Nil]) {
                  leader := [leader1 EXCEPT ![self] = (m).msource];
                  leaderTimeout := LeaderTimeoutReset;
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
                          with (value19 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value19), enabled |-> ((network)[j]).enabled]];
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
                                          with (value40 = m) {
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
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value30).cmd) = (LogPop)) {
                                          plog := [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value41 = m) {
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
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value42 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value42)];
                                              either {
                                                with (value52 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]];
                                                  plog := plog4;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd12 = (fd)[j]) {
                                                  await yielded_fd12;
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
                                      with (value43 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value43)];
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
                                          with (yielded_fd13 = (fd)[j]) {
                                            await yielded_fd13;
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
                                if (((value20).cmd) = (LogPop)) {
                                  with (plog5 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                    if ((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m).mprevLogIndex))) {
                                      log := [log4 EXCEPT ![i] = ((log4)[i]) \o ((m).mentries)];
                                      with (value31 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                        if (((value31).cmd) = (LogConcat)) {
                                          plog := [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value31).entries)];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value44 = m) {
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
                                            goto serverLoop;
                                          };
                                        } else {
                                          if (((value31).cmd) = (LogPop)) {
                                            plog := [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (value45 = m) {
                                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value45)];
                                                either {
                                                  with (value55 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]];
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
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (value46 = m) {
                                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value46)];
                                                either {
                                                  with (value56 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]];
                                                    plog := plog5;
                                                    goto serverLoop;
                                                  };
                                                } or {
                                                  with (yielded_fd16 = (fd)[j]) {
                                                    await yielded_fd16;
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
                                        with (value47 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value47)];
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
                                            with (yielded_fd17 = (fd)[j]) {
                                              await yielded_fd17;
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
                                    with (value32 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value32).cmd) = (LogConcat)) {
                                        plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value48 = m) {
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
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value32).cmd) = (LogPop)) {
                                          plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value49 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value49)];
                                              either {
                                                with (value59 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]];
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
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value410 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value410)];
                                              either {
                                                with (value510 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]];
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
                                        };
                                      };
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value411 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value411)];
                                        either {
                                          with (value511 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]];
                                            log := log4;
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd111 = (fd)[j]) {
                                            await yielded_fd111;
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
                              with (value33 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                if (((value33).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (value412 = m) {
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value412)];
                                      either {
                                        with (value512 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]];
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd112 = (fd)[j]) {
                                          await yielded_fd112;
                                          goto serverLoop;
                                        };
                                      };
                                    };
                                  } else {
                                    goto serverLoop;
                                  };
                                } else {
                                  if (((value33).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value413 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value413)];
                                        either {
                                          with (value513 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]];
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
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value414 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value414)];
                                        either {
                                          with (value514 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]];
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
                                  };
                                };
                              };
                            } else {
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (value415 = m) {
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value415)];
                                  either {
                                    with (value515 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]];
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
                      };
                    } else {
                      if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))) {
                        either {
                          with (value110 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                            await ((network)[j]).enabled;
                            await (Len(((network)[j]).queue)) < (BufferSize);
                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value110), enabled |-> ((network)[j]).enabled]];
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
                                          with (value416 = m) {
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
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } else {
                                        if (((value34).cmd) = (LogPop)) {
                                          plog := [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value417 = m) {
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
                                          } else {
                                            state := state1;
                                            goto serverLoop;
                                          };
                                        } else {
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value418 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value418)];
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
                                                with (yielded_fd118 = (fd)[j]) {
                                                  await yielded_fd118;
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
                                      with (value419 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value419)];
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
                                          with (yielded_fd119 = (fd)[j]) {
                                            await yielded_fd119;
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
                                if (((value21).cmd) = (LogPop)) {
                                  with (plog7 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                    if ((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m).mprevLogIndex))) {
                                      log := [log5 EXCEPT ![i] = ((log5)[i]) \o ((m).mentries)];
                                      with (value35 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                        if (((value35).cmd) = (LogConcat)) {
                                          plog := [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value35).entries)];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value420 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value420)];
                                              either {
                                                with (value520 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]];
                                                  state := state1;
                                                  goto serverLoop;
                                                };
                                              } or {
                                                with (yielded_fd120 = (fd)[j]) {
                                                  await yielded_fd120;
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
                                          if (((value35).cmd) = (LogPop)) {
                                            plog := [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))];
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (value421 = m) {
                                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value421)];
                                                either {
                                                  with (value521 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                    await ((network)[j]).enabled;
                                                    await (Len(((network)[j]).queue)) < (BufferSize);
                                                    network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]];
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
                                            if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                              with (value422 = m) {
                                                fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value422)];
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
                                                  with (yielded_fd122 = (fd)[j]) {
                                                    await yielded_fd122;
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
                                        with (value423 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value423)];
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
                                            with (yielded_fd123 = (fd)[j]) {
                                              await yielded_fd123;
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
                                    with (value36 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                      if (((value36).cmd) = (LogConcat)) {
                                        plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value36).entries)];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value424 = m) {
                                            fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value424)];
                                            either {
                                              with (value524 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]];
                                                state := state1;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd124 = (fd)[j]) {
                                                await yielded_fd124;
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
                                        if (((value36).cmd) = (LogPop)) {
                                          plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value425 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value425)];
                                              either {
                                                with (value525 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]];
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
                                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                            with (value426 = m) {
                                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value426)];
                                              either {
                                                with (value526 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                  await ((network)[j]).enabled;
                                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]];
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
                                        };
                                      };
                                    };
                                  } else {
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value427 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value427)];
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
                                          with (yielded_fd127 = (fd)[j]) {
                                            await yielded_fd127;
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
                              with (value37 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                if (((value37).cmd) = (LogConcat)) {
                                  plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value37).entries)];
                                  if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                    with (value428 = m) {
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value428)];
                                      either {
                                        with (value528 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                          await ((network)[j]).enabled;
                                          await (Len(((network)[j]).queue)) < (BufferSize);
                                          network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]];
                                          state := state1;
                                          goto serverLoop;
                                        };
                                      } or {
                                        with (yielded_fd128 = (fd)[j]) {
                                          await yielded_fd128;
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
                                  if (((value37).cmd) = (LogPop)) {
                                    plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value429 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value429)];
                                        either {
                                          with (value529 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]];
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
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value430 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value430)];
                                        either {
                                          with (value530 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]];
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
                                  };
                                };
                              };
                            } else {
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (value431 = m) {
                                  fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value431)];
                                  either {
                                    with (value531 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                      await ((network)[j]).enabled;
                                      await (Len(((network)[j]).queue)) < (BufferSize);
                                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]];
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
                      };
                    };
                  };
                };
              };
            } else {
              leader := [leader EXCEPT ![self] = (m).msource];
              leaderTimeout := LeaderTimeoutReset;
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
                      with (value111 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value111), enabled |-> ((network)[j]).enabled]];
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
                                      with (value432 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value432)];
                                        either {
                                          with (value532 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]];
                                            goto serverLoop;
                                          };
                                        } or {
                                          with (yielded_fd132 = (fd)[j]) {
                                            await yielded_fd132;
                                            goto serverLoop;
                                          };
                                        };
                                      };
                                    } else {
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value38).cmd) = (LogPop)) {
                                      plog := [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value433 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value433)];
                                          either {
                                            with (value533 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]];
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
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value434 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value434)];
                                          either {
                                            with (value534 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]];
                                              plog := plog8;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd134 = (fd)[j]) {
                                              await yielded_fd134;
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
                                  with (value435 = m) {
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value435)];
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
                                      with (yielded_fd135 = (fd)[j]) {
                                        await yielded_fd135;
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
                            if (((value22).cmd) = (LogPop)) {
                              with (plog9 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m).mprevLogIndex))) {
                                  log := [log6 EXCEPT ![i] = ((log6)[i]) \o ((m).mentries)];
                                  with (value39 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value39).cmd) = (LogConcat)) {
                                      plog := [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value39).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value436 = m) {
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value39).cmd) = (LogPop)) {
                                        plog := [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value437 = m) {
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
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value438 = m) {
                                            fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value438)];
                                            either {
                                              with (value538 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]];
                                                plog := plog9;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd138 = (fd)[j]) {
                                                await yielded_fd138;
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
                                    with (value439 = m) {
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value439)];
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
                                        with (yielded_fd139 = (fd)[j]) {
                                          await yielded_fd139;
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
                                with (value310 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value310).cmd) = (LogConcat)) {
                                    plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value310).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value440 = m) {
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
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value310).cmd) = (LogPop)) {
                                      plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value441 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value441)];
                                          either {
                                            with (value541 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]];
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
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value442 = m) {
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
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value443 = m) {
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value443)];
                                    either {
                                      with (value543 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]];
                                        log := log6;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd143 = (fd)[j]) {
                                        await yielded_fd143;
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
                          with (value311 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                            if (((value311).cmd) = (LogConcat)) {
                              plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (value444 = m) {
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
                              } else {
                                goto serverLoop;
                              };
                            } else {
                              if (((value311).cmd) = (LogPop)) {
                                plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value445 = m) {
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
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value446 = m) {
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
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            with (value447 = m) {
                              fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value447)];
                              either {
                                with (value547 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                  await ((network)[j]).enabled;
                                  await (Len(((network)[j]).queue)) < (BufferSize);
                                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]];
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
                  };
                } else {
                  if ((((m).mterm) < ((currentTerm)[i])) \/ (((((m).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))) {
                    either {
                      with (value112 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j]) {
                        await ((network)[j]).enabled;
                        await (Len(((network)[j]).queue)) < (BufferSize);
                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value112), enabled |-> ((network)[j]).enabled]];
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
                                      with (value448 = m) {
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
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value312).cmd) = (LogPop)) {
                                      plog := [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value449 = m) {
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value450 = m) {
                                          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value450)];
                                          either {
                                            with (value550 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                              await ((network)[j]).enabled;
                                              await (Len(((network)[j]).queue)) < (BufferSize);
                                              network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]];
                                              plog := plog10;
                                              goto serverLoop;
                                            };
                                          } or {
                                            with (yielded_fd150 = (fd)[j]) {
                                              await yielded_fd150;
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
                                  with (value451 = m) {
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value451)];
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
                                      with (yielded_fd151 = (fd)[j]) {
                                        await yielded_fd151;
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
                            if (((value23).cmd) = (LogPop)) {
                              with (plog11 = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]) {
                                if ((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m).mprevLogIndex))) {
                                  log := [log7 EXCEPT ![i] = ((log7)[i]) \o ((m).mentries)];
                                  with (value313 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                    if (((value313).cmd) = (LogConcat)) {
                                      plog := [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value313).entries)];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value452 = m) {
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if (((value313).cmd) = (LogPop)) {
                                        plog := [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))];
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value453 = m) {
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
                                        } else {
                                          goto serverLoop;
                                        };
                                      } else {
                                        if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                          with (value454 = m) {
                                            fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value454)];
                                            either {
                                              with (value554 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                                await ((network)[j]).enabled;
                                                await (Len(((network)[j]).queue)) < (BufferSize);
                                                network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]];
                                                plog := plog11;
                                                goto serverLoop;
                                              };
                                            } or {
                                              with (yielded_fd154 = (fd)[j]) {
                                                await yielded_fd154;
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
                                    with (value455 = m) {
                                      fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value455)];
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
                                        with (yielded_fd155 = (fd)[j]) {
                                          await yielded_fd155;
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
                                with (value314 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                                  if (((value314).cmd) = (LogConcat)) {
                                    plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)];
                                    if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                      with (value456 = m) {
                                        fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value456)];
                                        either {
                                          with (value556 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                            await ((network)[j]).enabled;
                                            await (Len(((network)[j]).queue)) < (BufferSize);
                                            network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]];
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
                                      goto serverLoop;
                                    };
                                  } else {
                                    if (((value314).cmd) = (LogPop)) {
                                      plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value457 = m) {
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
                                        goto serverLoop;
                                      };
                                    } else {
                                      if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                        with (value458 = m) {
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
                                        goto serverLoop;
                                      };
                                    };
                                  };
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value459 = m) {
                                    fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value459)];
                                    either {
                                      with (value559 = [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m).mprevLogIndex) + (Len((m).mentries)), msource |-> i, mdest |-> j]) {
                                        await ((network)[j]).enabled;
                                        await (Len(((network)[j]).queue)) < (BufferSize);
                                        network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]];
                                        log := log7;
                                        goto serverLoop;
                                      };
                                    } or {
                                      with (yielded_fd159 = (fd)[j]) {
                                        await yielded_fd159;
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
                          with (value315 = [cmd |-> LogConcat, entries |-> (m).mentries]) {
                            if (((value315).cmd) = (LogConcat)) {
                              plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value315).entries)];
                              if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                with (value460 = m) {
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
                                goto serverLoop;
                              };
                            } else {
                              if (((value315).cmd) = (LogPop)) {
                                plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value461 = m) {
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
                                  goto serverLoop;
                                };
                              } else {
                                if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                                  with (value462 = m) {
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
                                } else {
                                  goto serverLoop;
                                };
                              };
                            };
                          };
                        } else {
                          if ((((m).mentries) = (<<>>)) \/ (((((m).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m).mentries)[1]).term)))) {
                            with (value463 = m) {
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
              if (((m).mtype) = (ProposeMessage)) {
                with (i = self) {
                  if (Debug) {
                    print <<"HandleProposeMessage", i, (currentTerm)[i], (state)[i]>>;
                    if (((state)[i]) = (Leader)) {
                      with (entry = [term |-> (currentTerm)[i], cmd |-> (m).mcmd]) {
                        log := [log EXCEPT ![i] = Append((log)[i], entry)];
                        with (value60 = [cmd |-> LogConcat, entries |-> <<entry>>]) {
                          if (((value60).cmd) = (LogConcat)) {
                            plog := [plog EXCEPT ![i] = ((plog)[i]) \o ((value60).entries)];
                            goto serverLoop;
                          } else {
                            if (((value60).cmd) = (LogPop)) {
                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
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
                              plog := [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))];
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
            with (yielded_fd30 = (fd)[idx0]) {
              await yielded_fd30;
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
              with (yielded_fd40 = (fd)[idx1]) {
                await yielded_fd40;
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
          value100 = [mtype |-> AcceptMessage, mcmd |-> cmd]
        ) {
          acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value100)];
          goto applyLoop;
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
      with (res1 = Head((becomeLeaderCh)[srvId3])) {
        becomeLeaderCh := [becomeLeaderCh EXCEPT ![srvId3] = Tail((becomeLeaderCh)[srvId3])];
        with (yielded_becomeLeaderCh = res1) {
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
  
  fair process (s5 \in ServerFollowerAdvanceCommitIndexSet)
    variables m0; srvId4 = (fAdvCommitSrvId)[self];
  {
    serverFollowerAdvanceCommitIndexLoop:
      if (TRUE) {
        await (Len((fAdvCommitIdxCh)[srvId4])) > (0);
        with (res20 = Head((fAdvCommitIdxCh)[srvId4])) {
          fAdvCommitIdxCh := [fAdvCommitIdxCh EXCEPT ![srvId4] = Tail((fAdvCommitIdxCh)[srvId4])];
          with (yielded_fAdvCommitIdxCh0 = res20) {
            m0 := yielded_fAdvCommitIdxCh0;
            goto acctLoop;
          };
        };
      } else {
        goto Done;
      };
    acctLoop:
      if (((commitIndex)[srvId4]) < ((m0).mcommitIndex)) {
        commitIndex := [commitIndex EXCEPT ![srvId4] = ((commitIndex)[srvId4]) + (1)];
        with (
          i = srvId4, 
          k = (commitIndex)[i], 
          entry = ((log)[i])[k], 
          cmd = (entry).cmd, 
          value113 = [mtype |-> AcceptMessage, mcmd |-> cmd]
        ) {
          acctCh := [acctCh EXCEPT ![i] = Append((acctCh)[i], value113)];
          goto acctLoop;
        };
      } else {
        goto serverFollowerAdvanceCommitIndexLoop;
      };
  }
  
  fair process (crasher \in ServerCrasherSet)
    variables srvId5 = (crasherSrvId)[self];
  {
    serverCrash:
      with (value120 = FALSE) {
        network := [network EXCEPT ![srvId5] = [queue |-> ((network)[srvId5]).queue, enabled |-> value120]];
        goto fdUpdate;
      };
    fdUpdate:
      with (value130 = TRUE) {
        fd := [fd EXCEPT ![srvId5] = value130];
        goto block;
      };
    block:
      await FALSE;
      goto Done;
  }
  
  fair process (proposer = 0)
  {
    sndReq:
      with (value140 = [mtype |-> ProposeMessage, mcmd |-> [data |-> "hello"]]) {
        propCh := [propCh EXCEPT ![1] = Append((propCh)[1], value140)];
        goto block;
      };
    block:
      await FALSE;
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "f148afc1" /\ chksum(tla) = "804f5830") PCal-18049938ece8066a38eb5044080cf45c
\* Label block of process crasher at line 3312 col 7 changed to block_
CONSTANT defaultInitValue
VARIABLES network, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, 
          log, plog, votedFor, votesResponded, votesGranted, leader, propCh, 
          acctCh, leaderTimeout, appendEntriesCh, becomeLeaderCh, 
          fAdvCommitIdxCh, requestVoteSrvId, appendEntriesSrvId, 
          advanceCommitIndexSrvId, becomeLeaderSrvId, fAdvCommitSrvId, 
          crasherSrvId, pc

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
ServerRequestVoteSet == (((1) * (NumServers)) + (1)) .. ((2) * (NumServers))
ServerAppendEntriesSet == (((2) * (NumServers)) + (1)) .. ((3) * (NumServers))
ServerAdvanceCommitIndexSet == (((3) * (NumServers)) + (1)) .. ((4) * (NumServers))
ServerBecomeLeaderSet == (((4) * (NumServers)) + (1)) .. ((5) * (NumServers))
ServerFollowerAdvanceCommitIndexSet == (((5) * (NumServers)) + (1)) .. ((6) * (NumServers))
ServerCrasherSet == IF ExploreFail THEN (((6) * (NumServers)) + (1)) .. (((6) * (NumServers)) + (MaxNodeFail)) ELSE {}
NodeSet == ServerSet
KeySet == {}

VARIABLES idx, m, srvId, idx0, srvId0, idx1, srvId1, newCommitIndex, srvId2, 
          srvId3, m0, srvId4, srvId5

vars == << network, fd, state, currentTerm, commitIndex, nextIndex, 
           matchIndex, log, plog, votedFor, votesResponded, votesGranted, 
           leader, propCh, acctCh, leaderTimeout, appendEntriesCh, 
           becomeLeaderCh, fAdvCommitIdxCh, requestVoteSrvId, 
           appendEntriesSrvId, advanceCommitIndexSrvId, becomeLeaderSrvId, 
           fAdvCommitSrvId, crasherSrvId, pc, idx, m, srvId, idx0, srvId0, 
           idx1, srvId1, newCommitIndex, srvId2, srvId3, m0, srvId4, srvId5
        >>

ProcSet == (ServerSet) \cup (ServerRequestVoteSet) \cup (ServerAppendEntriesSet) \cup (ServerAdvanceCommitIndexSet) \cup (ServerBecomeLeaderSet) \cup (ServerFollowerAdvanceCommitIndexSet) \cup (ServerCrasherSet) \cup {0}

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
        /\ requestVoteSrvId = [i \in ServerRequestVoteSet |-> (i) - ((1) * (NumServers))]
        /\ appendEntriesSrvId = [i \in ServerAppendEntriesSet |-> (i) - ((2) * (NumServers))]
        /\ advanceCommitIndexSrvId = [i \in ServerAdvanceCommitIndexSet |-> (i) - ((3) * (NumServers))]
        /\ becomeLeaderSrvId = [i \in ServerBecomeLeaderSet |-> (i) - ((4) * (NumServers))]
        /\ fAdvCommitSrvId = [i \in ServerFollowerAdvanceCommitIndexSet |-> (i) - ((5) * (NumServers))]
        /\ crasherSrvId = [i \in ServerCrasherSet |-> (i) - ((6) * (NumServers))]
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
        (* Process s5 *)
        /\ m0 = [self \in ServerFollowerAdvanceCommitIndexSet |-> defaultInitValue]
        /\ srvId4 = [self \in ServerFollowerAdvanceCommitIndexSet |-> (fAdvCommitSrvId)[self]]
        (* Process crasher *)
        /\ srvId5 = [self \in ServerCrasherSet |-> (crasherSrvId)[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                                        [] self \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                                        [] self \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                                        [] self \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                                        [] self \in ServerFollowerAdvanceCommitIndexSet -> "serverFollowerAdvanceCommitIndexLoop"
                                        [] self \in ServerCrasherSet -> "serverCrash"
                                        [] self = 0 -> "sndReq"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ \/ /\ Assert(((network)[self]).enabled, 
                                               "Failure of assertion at line 921, column 11.")
                                     /\ (Len(((network)[self]).queue)) > (0)
                                     /\ LET readMsg00 == Head(((network)[self]).queue) IN
                                          /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                                          /\ LET yielded_network1 == readMsg00 IN
                                               /\ m' = [m EXCEPT ![self] = yielded_network1]
                                               /\ Assert(((m'[self]).mdest) = (self), 
                                                         "Failure of assertion at line 927, column 15.")
                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED propCh
                                  \/ /\ (Len((propCh)[self])) > (0)
                                     /\ LET res00 == Head((propCh)[self]) IN
                                          /\ propCh' = [propCh EXCEPT ![self] = Tail((propCh)[self])]
                                          /\ LET yielded_propCh0 == res00 IN
                                               /\ m' = [m EXCEPT ![self] = yielded_propCh0]
                                               /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
                                     /\ UNCHANGED network
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, propCh, m >>
                    /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                    nextIndex, matchIndex, log, plog, votedFor, 
                                    votesResponded, votesGranted, leader, 
                                    acctCh, leaderTimeout, appendEntriesCh, 
                                    becomeLeaderCh, fAdvCommitIdxCh, 
                                    requestVoteSrvId, appendEntriesSrvId, 
                                    advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                    fAdvCommitSrvId, crasherSrvId, idx, srvId, 
                                    idx0, srvId0, idx1, srvId1, newCommitIndex, 
                                    srvId2, srvId3, m0, srvId4, srvId5 >>

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
                                                                   "Failure of assertion at line 957, column 15.")
                                                         /\ IF grant
                                                               THEN /\ votedFor' = [votedFor1 EXCEPT ![i] = j]
                                                                    /\ \/ /\ LET value15 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value15), enabled |-> ((network)[j]).enabled]]
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       \/ /\ LET yielded_fd5 == (fd)[j] IN
                                                                               /\ yielded_fd5
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                          /\ UNCHANGED network
                                                               ELSE /\ \/ /\ LET value16 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm')[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                               /\ ((network)[j]).enabled
                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value16), enabled |-> ((network)[j]).enabled]]
                                                                               /\ IF Debug
                                                                                     THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm')[i], grant>>)
                                                                                          /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                     ELSE /\ votedFor' = votedFor1
                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                       \/ /\ LET yielded_fd6 == (fd)[j] IN
                                                                               /\ yielded_fd6
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
                                                              "Failure of assertion at line 1021, column 13.")
                                                    /\ IF grant
                                                          THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                                                               /\ \/ /\ LET value17 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value17), enabled |-> ((network)[j]).enabled]]
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd7 == (fd)[j] IN
                                                                          /\ yielded_fd7
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                          ELSE /\ \/ /\ LET value18 == [mtype |-> RequestVoteResponse, mterm |-> (currentTerm)[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j] IN
                                                                          /\ ((network)[j]).enabled
                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value18), enabled |-> ((network)[j]).enabled]]
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                  \/ /\ LET yielded_fd8 == (fd)[j] IN
                                                                          /\ yielded_fd8
                                                                          /\ IF Debug
                                                                                THEN /\ PrintT(<<"HandleRequestVoteRequest", i, j, (currentTerm)[i], grant>>)
                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                     /\ UNCHANGED network
                                                               /\ UNCHANGED votedFor
                                         /\ UNCHANGED << state, currentTerm, 
                                                         leader >>
                              /\ UNCHANGED << nextIndex, matchIndex, log, plog, 
                                              votesResponded, votesGranted, 
                                              leaderTimeout, becomeLeaderCh, 
                                              fAdvCommitIdxCh >>
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
                                                                                "Failure of assertion at line 1089, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state')[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value00 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value00)]
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
                                                                                "Failure of assertion at line 1115, column 17.")
                                                                      /\ votesResponded' = [votesResponded EXCEPT ![i] = ((votesResponded)[i]) \union ({j})]
                                                                      /\ IF (m[self]).mvoteGranted
                                                                            THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = ((votesGranted)[i]) \union ({j})]
                                                                                 /\ IF (((state)[i]) = (Candidate)) /\ (isQuorum((votesGranted')[i]))
                                                                                       THEN /\ LET value01 == TRUE IN
                                                                                                 /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = Append((becomeLeaderCh)[i], value01)]
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
                                         /\ UNCHANGED << network, nextIndex, 
                                                         matchIndex, log, plog, 
                                                         leaderTimeout, 
                                                         fAdvCommitIdxCh >>
                                    ELSE /\ IF ((m[self]).mtype) = (AppendEntriesRequest)
                                               THEN /\ IF ((m[self]).mterm) > ((currentTerm)[self])
                                                          THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = (m[self]).mterm]
                                                               /\ LET state1 == [state EXCEPT ![self] = Follower] IN
                                                                    /\ votedFor' = [votedFor EXCEPT ![self] = Nil]
                                                                    /\ LET leader1 == [leader EXCEPT ![self] = Nil] IN
                                                                         /\ leader' = [leader1 EXCEPT ![self] = (m[self]).msource]
                                                                         /\ leaderTimeout' = LeaderTimeoutReset
                                                                         /\ LET i == self IN
                                                                              LET j == (m[self]).msource IN
                                                                                LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                                  /\ Assert(((m[self]).mterm) <= ((currentTerm')[i]), 
                                                                                            "Failure of assertion at line 1147, column 21.")
                                                                                  /\ IF (((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Candidate))
                                                                                        THEN /\ state' = [state1 EXCEPT ![i] = Follower]
                                                                                             /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                   THEN /\ \/ /\ LET value19 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value19), enabled |-> ((network)[j]).enabled]]
                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                           \/ /\ LET yielded_fd00 == (fd)[j] IN
                                                                                                                   /\ yielded_fd00
                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                              /\ UNCHANGED network
                                                                                                        /\ UNCHANGED << log, 
                                                                                                                        plog, 
                                                                                                                        fAdvCommitIdxCh >>
                                                                                                   ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                                  "Failure of assertion at line 1165, column 25.")
                                                                                                        /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                             IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                                THEN /\ LET log4 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                          LET value20 == [cmd |-> LogPop] IN
                                                                                                                            IF ((value20).cmd) = (LogConcat)
                                                                                                                               THEN /\ LET plog4 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value20).entries)] IN
                                                                                                                                         IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                            THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ LET value30 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                      IF ((value30).cmd) = (LogConcat)
                                                                                                                                                         THEN /\ plog' = [plog4 EXCEPT ![i] = ((plog4)[i]) \o ((value30).entries)]
                                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                    THEN /\ LET value40 == m[self] IN
                                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value40)]
                                                                                                                                                                              /\ \/ /\ LET value50 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value50), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 \/ /\ LET yielded_fd10 == (fd)[j] IN
                                                                                                                                                                                         /\ yielded_fd10
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                                         ELSE /\ IF ((value30).cmd) = (LogPop)
                                                                                                                                                                    THEN /\ plog' = [plog4 EXCEPT ![i] = SubSeq((plog4)[i], 1, (Len((plog4)[i])) - (1))]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value41 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value41)]
                                                                                                                                                                                         /\ \/ /\ LET value51 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value51), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd11 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd11
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                                                    ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value42 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value42)]
                                                                                                                                                                                         /\ \/ /\ LET value52 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value52), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ plog' = plog4
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd12 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd12
                                                                                                                                                                                                    /\ plog' = plog4
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ plog' = plog4
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                            ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                       THEN /\ LET value43 == m[self] IN
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value43)]
                                                                                                                                                                 /\ \/ /\ LET value53 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value53), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog4
                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    \/ /\ LET yielded_fd13 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd13
                                                                                                                                                                            /\ plog' = plog4
                                                                                                                                                                            /\ log' = log4
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED network
                                                                                                                                                       ELSE /\ plog' = plog4
                                                                                                                                                            /\ log' = log4
                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                            /\ UNCHANGED << network, 
                                                                                                                                                                            fAdvCommitIdxCh >>
                                                                                                                               ELSE /\ IF ((value20).cmd) = (LogPop)
                                                                                                                                          THEN /\ LET plog5 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ LET value31 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                                 IF ((value31).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog5 EXCEPT ![i] = ((plog5)[i]) \o ((value31).entries)]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value44 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value44)]
                                                                                                                                                                                         /\ \/ /\ LET value54 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value54), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd14 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd14
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                                                    ELSE /\ IF ((value31).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog5 EXCEPT ![i] = SubSeq((plog5)[i], 1, (Len((plog5)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET value45 == m[self] IN
                                                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value45)]
                                                                                                                                                                                                    /\ \/ /\ LET value55 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value55), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd15 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd15
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET value46 == m[self] IN
                                                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value46)]
                                                                                                                                                                                                    /\ \/ /\ LET value56 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value56), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog5
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd16 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd16
                                                                                                                                                                                                               /\ plog' = plog5
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ plog' = plog5
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET value47 == m[self] IN
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value47)]
                                                                                                                                                                            /\ \/ /\ LET value57 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value57), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog5
                                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd17 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd17
                                                                                                                                                                                       /\ plog' = plog5
                                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED network
                                                                                                                                                                  ELSE /\ plog' = plog5
                                                                                                                                                                       /\ log' = log4
                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       /\ UNCHANGED << network, 
                                                                                                                                                                                       fAdvCommitIdxCh >>
                                                                                                                                          ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                     THEN /\ log' = [log4 EXCEPT ![i] = ((log4)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ LET value32 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                               IF ((value32).cmd) = (LogConcat)
                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value32).entries)]
                                                                                                                                                                       /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET value48 == m[self] IN
                                                                                                                                                                                       /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value48)]
                                                                                                                                                                                       /\ \/ /\ LET value58 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value58), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd18 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd18
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                                  fAdvCommitIdxCh >>
                                                                                                                                                                  ELSE /\ IF ((value32).cmd) = (LogPop)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET value49 == m[self] IN
                                                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value49)]
                                                                                                                                                                                                  /\ \/ /\ LET value59 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value59), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd19 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd19
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET value410 == m[self] IN
                                                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value410)]
                                                                                                                                                                                                  /\ \/ /\ LET value510 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value510), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                     \/ /\ LET yielded_fd110 == (fd)[j] IN
                                                                                                                                                                                                             /\ yielded_fd110
                                                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                                                                  /\ plog' = plog
                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log4)[i])) >= (index))) /\ (((((log4)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                THEN /\ LET value411 == m[self] IN
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value411)]
                                                                                                                                                                          /\ \/ /\ LET value511 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value511), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ log' = log4
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             \/ /\ LET yielded_fd111 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd111
                                                                                                                                                                                     /\ log' = log4
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = log4
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                                          /\ plog' = plog
                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                           THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                                /\ LET value33 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                     IF ((value33).cmd) = (LogConcat)
                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value33).entries)]
                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                   THEN /\ LET value412 == m[self] IN
                                                                                                                                                             /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value412)]
                                                                                                                                                             /\ \/ /\ LET value512 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value512), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                \/ /\ LET yielded_fd112 == (fd)[j] IN
                                                                                                                                                                        /\ yielded_fd112
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                        fAdvCommitIdxCh >>
                                                                                                                                        ELSE /\ IF ((value33).cmd) = (LogPop)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET value413 == m[self] IN
                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value413)]
                                                                                                                                                                        /\ \/ /\ LET value513 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value513), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd113 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd113
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET value414 == m[self] IN
                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value414)]
                                                                                                                                                                        /\ \/ /\ LET value514 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value514), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                           \/ /\ LET yielded_fd114 == (fd)[j] IN
                                                                                                                                                                                   /\ yielded_fd114
                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                        /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                      THEN /\ LET value415 == m[self] IN
                                                                                                                                                /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value415)]
                                                                                                                                                /\ \/ /\ LET value515 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value515), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                   \/ /\ LET yielded_fd115 == (fd)[j] IN
                                                                                                                                                           /\ yielded_fd115
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                           fAdvCommitIdxCh >>
                                                                                                                                /\ UNCHANGED << log, 
                                                                                                                                                plog >>
                                                                                        ELSE /\ IF (((m[self]).mterm) < ((currentTerm')[i])) \/ (((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                                   THEN /\ \/ /\ LET value110 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value110), enabled |-> ((network)[j]).enabled]]
                                                                                                                   /\ state' = state1
                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                           \/ /\ LET yielded_fd01 == (fd)[j] IN
                                                                                                                   /\ yielded_fd01
                                                                                                                   /\ state' = state1
                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                              /\ UNCHANGED network
                                                                                                        /\ UNCHANGED << log, 
                                                                                                                        plog, 
                                                                                                                        fAdvCommitIdxCh >>
                                                                                                   ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm')[i])) /\ (((state1)[i]) = (Follower))) /\ (logOK), 
                                                                                                                  "Failure of assertion at line 1602, column 25.")
                                                                                                        /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                             IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                                THEN /\ LET log5 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                          LET value21 == [cmd |-> LogPop] IN
                                                                                                                            IF ((value21).cmd) = (LogConcat)
                                                                                                                               THEN /\ LET plog6 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value21).entries)] IN
                                                                                                                                         IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                            THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                 /\ LET value34 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                      IF ((value34).cmd) = (LogConcat)
                                                                                                                                                         THEN /\ plog' = [plog6 EXCEPT ![i] = ((plog6)[i]) \o ((value34).entries)]
                                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                    THEN /\ LET value416 == m[self] IN
                                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value416)]
                                                                                                                                                                              /\ \/ /\ LET value516 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value516), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                 \/ /\ LET yielded_fd116 == (fd)[j] IN
                                                                                                                                                                                         /\ yielded_fd116
                                                                                                                                                                                         /\ state' = state1
                                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                                    ELSE /\ state' = state1
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                                         ELSE /\ IF ((value34).cmd) = (LogPop)
                                                                                                                                                                    THEN /\ plog' = [plog6 EXCEPT ![i] = SubSeq((plog6)[i], 1, (Len((plog6)[i])) - (1))]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value417 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value417)]
                                                                                                                                                                                         /\ \/ /\ LET value517 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value517), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                                                    ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value418 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value418)]
                                                                                                                                                                                         /\ \/ /\ LET value518 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value518), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ plog' = plog6
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd118 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd118
                                                                                                                                                                                                    /\ plog' = plog6
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ plog' = plog6
                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                            ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                       THEN /\ LET value419 == m[self] IN
                                                                                                                                                                 /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value419)]
                                                                                                                                                                 /\ \/ /\ LET value519 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                            /\ ((network)[j]).enabled
                                                                                                                                                                            /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                            /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value519), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                            /\ plog' = plog6
                                                                                                                                                                            /\ log' = log5
                                                                                                                                                                            /\ state' = state1
                                                                                                                                                                            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    \/ /\ LET yielded_fd119 == (fd)[j] IN
                                                                                                                                                                            /\ yielded_fd119
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
                                                                                                                                                                            fAdvCommitIdxCh >>
                                                                                                                               ELSE /\ IF ((value21).cmd) = (LogPop)
                                                                                                                                          THEN /\ LET plog7 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                                    IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                       THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                            /\ LET value35 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                                 IF ((value35).cmd) = (LogConcat)
                                                                                                                                                                    THEN /\ plog' = [plog7 EXCEPT ![i] = ((plog7)[i]) \o ((value35).entries)]
                                                                                                                                                                         /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                               THEN /\ LET value420 == m[self] IN
                                                                                                                                                                                         /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value420)]
                                                                                                                                                                                         /\ \/ /\ LET value520 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                    /\ ((network)[j]).enabled
                                                                                                                                                                                                    /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                    /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value520), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                            \/ /\ LET yielded_fd120 == (fd)[j] IN
                                                                                                                                                                                                    /\ yielded_fd120
                                                                                                                                                                                                    /\ state' = state1
                                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED network
                                                                                                                                                                               ELSE /\ state' = state1
                                                                                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                    /\ UNCHANGED << network, 
                                                                                                                                                                                                    fAdvCommitIdxCh >>
                                                                                                                                                                    ELSE /\ IF ((value35).cmd) = (LogPop)
                                                                                                                                                                               THEN /\ plog' = [plog7 EXCEPT ![i] = SubSeq((plog7)[i], 1, (Len((plog7)[i])) - (1))]
                                                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET value421 == m[self] IN
                                                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value421)]
                                                                                                                                                                                                    /\ \/ /\ LET value521 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value521), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                                                               ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                          THEN /\ LET value422 == m[self] IN
                                                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value422)]
                                                                                                                                                                                                    /\ \/ /\ LET value522 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value522), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                               /\ plog' = plog7
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                       \/ /\ LET yielded_fd122 == (fd)[j] IN
                                                                                                                                                                                                               /\ yielded_fd122
                                                                                                                                                                                                               /\ plog' = plog7
                                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                                                          ELSE /\ plog' = plog7
                                                                                                                                                                                               /\ state' = state1
                                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                                       ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                  THEN /\ LET value423 == m[self] IN
                                                                                                                                                                            /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value423)]
                                                                                                                                                                            /\ \/ /\ LET value523 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                       /\ ((network)[j]).enabled
                                                                                                                                                                                       /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                       /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value523), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                       /\ plog' = plog7
                                                                                                                                                                                       /\ log' = log5
                                                                                                                                                                                       /\ state' = state1
                                                                                                                                                                                       /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                               \/ /\ LET yielded_fd123 == (fd)[j] IN
                                                                                                                                                                                       /\ yielded_fd123
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
                                                                                                                                                                                       fAdvCommitIdxCh >>
                                                                                                                                          ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                                     THEN /\ log' = [log5 EXCEPT ![i] = ((log5)[i]) \o ((m[self]).mentries)]
                                                                                                                                                          /\ LET value36 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                               IF ((value36).cmd) = (LogConcat)
                                                                                                                                                                  THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value36).entries)]
                                                                                                                                                                       /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                             THEN /\ LET value424 == m[self] IN
                                                                                                                                                                                       /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value424)]
                                                                                                                                                                                       /\ \/ /\ LET value524 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value524), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                          \/ /\ LET yielded_fd124 == (fd)[j] IN
                                                                                                                                                                                                  /\ yielded_fd124
                                                                                                                                                                                                  /\ state' = state1
                                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                                                             ELSE /\ state' = state1
                                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                                                  fAdvCommitIdxCh >>
                                                                                                                                                                  ELSE /\ IF ((value36).cmd) = (LogPop)
                                                                                                                                                                             THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                                  /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET value425 == m[self] IN
                                                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value425)]
                                                                                                                                                                                                  /\ \/ /\ LET value525 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value525), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                        THEN /\ LET value426 == m[self] IN
                                                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value426)]
                                                                                                                                                                                                  /\ \/ /\ LET value526 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value526), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                                                                  /\ plog' = plog
                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log5)[i])) >= (index))) /\ (((((log5)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                THEN /\ LET value427 == m[self] IN
                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value427)]
                                                                                                                                                                          /\ \/ /\ LET value527 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value527), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                     /\ log' = log5
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                             \/ /\ LET yielded_fd127 == (fd)[j] IN
                                                                                                                                                                                     /\ yielded_fd127
                                                                                                                                                                                     /\ log' = log5
                                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                ELSE /\ log' = log5
                                                                                                                                                                     /\ state' = state1
                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                                          /\ plog' = plog
                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                           THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                                /\ LET value37 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                     IF ((value37).cmd) = (LogConcat)
                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value37).entries)]
                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                   THEN /\ LET value428 == m[self] IN
                                                                                                                                                             /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value428)]
                                                                                                                                                             /\ \/ /\ LET value528 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value528), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                \/ /\ LET yielded_fd128 == (fd)[j] IN
                                                                                                                                                                        /\ yielded_fd128
                                                                                                                                                                        /\ state' = state1
                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                   ELSE /\ state' = state1
                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                        fAdvCommitIdxCh >>
                                                                                                                                        ELSE /\ IF ((value37).cmd) = (LogPop)
                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET value429 == m[self] IN
                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value429)]
                                                                                                                                                                        /\ \/ /\ LET value529 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value529), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                              THEN /\ LET value430 == m[self] IN
                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value430)]
                                                                                                                                                                        /\ \/ /\ LET value530 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value530), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                        /\ plog' = plog
                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                      THEN /\ LET value431 == m[self] IN
                                                                                                                                                /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value431)]
                                                                                                                                                /\ \/ /\ LET value531 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm')[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value531), enabled |-> ((network)[j]).enabled]]
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
                                                                                                                                                           fAdvCommitIdxCh >>
                                                                                                                                /\ UNCHANGED << log, 
                                                                                                                                                plog >>
                                                          ELSE /\ leader' = [leader EXCEPT ![self] = (m[self]).msource]
                                                               /\ leaderTimeout' = LeaderTimeoutReset
                                                               /\ LET i == self IN
                                                                    LET j == (m[self]).msource IN
                                                                      LET logOK == (((m[self]).mprevLogIndex) = (0)) \/ (((((m[self]).mprevLogIndex) > (0)) /\ (((m[self]).mprevLogIndex) <= (Len((log)[i])))) /\ (((m[self]).mprevLogTerm) = ((((log)[i])[(m[self]).mprevLogIndex]).term))) IN
                                                                        /\ Assert(((m[self]).mterm) <= ((currentTerm)[i]), 
                                                                                  "Failure of assertion at line 2081, column 17.")
                                                                        /\ IF (((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Candidate))
                                                                              THEN /\ state' = [state EXCEPT ![i] = Follower]
                                                                                   /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value111 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value111), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd02 == (fd)[j] IN
                                                                                                         /\ yielded_fd02
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << log, 
                                                                                                              plog, 
                                                                                                              fAdvCommitIdxCh >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state')[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2099, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log6 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                LET value22 == [cmd |-> LogPop] IN
                                                                                                                  IF ((value22).cmd) = (LogConcat)
                                                                                                                     THEN /\ LET plog8 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value22).entries)] IN
                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                  THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                       /\ LET value38 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                            IF ((value38).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog8 EXCEPT ![i] = ((plog8)[i]) \o ((value38).entries)]
                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                          THEN /\ LET value432 == m[self] IN
                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value432)]
                                                                                                                                                                    /\ \/ /\ LET value532 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value532), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd132 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd132
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                               ELSE /\ IF ((value38).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog8 EXCEPT ![i] = SubSeq((plog8)[i], 1, (Len((plog8)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value433 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value433)]
                                                                                                                                                                               /\ \/ /\ LET value533 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value533), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd133 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd133
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value434 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value434)]
                                                                                                                                                                               /\ \/ /\ LET value534 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value534), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd134 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd134
                                                                                                                                                                                          /\ plog' = plog8
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog8
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET value435 == m[self] IN
                                                                                                                                                       /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value435)]
                                                                                                                                                       /\ \/ /\ LET value535 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value535), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd135 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd135
                                                                                                                                                                  /\ plog' = plog8
                                                                                                                                                                  /\ log' = log6
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog8
                                                                                                                                                  /\ log' = log6
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  fAdvCommitIdxCh >>
                                                                                                                     ELSE /\ IF ((value22).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog9 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value39 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value39).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog9 EXCEPT ![i] = ((plog9)[i]) \o ((value39).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value436 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value436)]
                                                                                                                                                                               /\ \/ /\ LET value536 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value536), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd136 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd136
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                                          ELSE /\ IF ((value39).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog9 EXCEPT ![i] = SubSeq((plog9)[i], 1, (Len((plog9)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET value437 == m[self] IN
                                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value437)]
                                                                                                                                                                                          /\ \/ /\ LET value537 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value537), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd137 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd137
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET value438 == m[self] IN
                                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value438)]
                                                                                                                                                                                          /\ \/ /\ LET value538 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value538), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd138 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd138
                                                                                                                                                                                                     /\ plog' = plog9
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog9
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET value439 == m[self] IN
                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value439)]
                                                                                                                                                                  /\ \/ /\ LET value539 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value539), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd139 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd139
                                                                                                                                                                             /\ plog' = plog9
                                                                                                                                                                             /\ log' = log6
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog9
                                                                                                                                                             /\ log' = log6
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log6 EXCEPT ![i] = ((log6)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value310 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value310).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value310).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET value440 == m[self] IN
                                                                                                                                                                             /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value440)]
                                                                                                                                                                             /\ \/ /\ LET value540 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value540), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd140 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd140
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        fAdvCommitIdxCh >>
                                                                                                                                                        ELSE /\ IF ((value310).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET value441 == m[self] IN
                                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value441)]
                                                                                                                                                                                        /\ \/ /\ LET value541 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value541), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd141 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd141
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET value442 == m[self] IN
                                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value442)]
                                                                                                                                                                                        /\ \/ /\ LET value542 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value542), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd142 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd142
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log6)[i])) >= (index))) /\ (((((log6)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET value443 == m[self] IN
                                                                                                                                                                /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value443)]
                                                                                                                                                                /\ \/ /\ LET value543 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value543), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd143 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd143
                                                                                                                                                                           /\ log' = log6
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log6
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           fAdvCommitIdxCh >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value311 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value311).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value311).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET value444 == m[self] IN
                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value444)]
                                                                                                                                                   /\ \/ /\ LET value544 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value544), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd144 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd144
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              fAdvCommitIdxCh >>
                                                                                                                              ELSE /\ IF ((value311).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET value445 == m[self] IN
                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value445)]
                                                                                                                                                              /\ \/ /\ LET value545 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value545), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd145 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd145
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET value446 == m[self] IN
                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value446)]
                                                                                                                                                              /\ \/ /\ LET value546 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value546), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd146 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd146
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET value447 == m[self] IN
                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value447)]
                                                                                                                                      /\ \/ /\ LET value547 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value547), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd147 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd147
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 fAdvCommitIdxCh >>
                                                                                                                      /\ UNCHANGED << log, 
                                                                                                                                      plog >>
                                                                              ELSE /\ IF (((m[self]).mterm) < ((currentTerm)[i])) \/ (((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (~ (logOK)))
                                                                                         THEN /\ \/ /\ LET value112 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j] IN
                                                                                                         /\ ((network)[j]).enabled
                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value112), enabled |-> ((network)[j]).enabled]]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                 \/ /\ LET yielded_fd03 == (fd)[j] IN
                                                                                                         /\ yielded_fd03
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                    /\ UNCHANGED network
                                                                                              /\ UNCHANGED << log, 
                                                                                                              plog, 
                                                                                                              fAdvCommitIdxCh >>
                                                                                         ELSE /\ Assert(((((m[self]).mterm) = ((currentTerm)[i])) /\ (((state)[i]) = (Follower))) /\ (logOK), 
                                                                                                        "Failure of assertion at line 2534, column 21.")
                                                                                              /\ LET index == ((m[self]).mprevLogIndex) + (1) IN
                                                                                                   IF ((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) # ((((m[self]).mentries)[1]).term))
                                                                                                      THEN /\ LET log7 == [log EXCEPT ![i] = SubSeq((log)[i], 1, (Len((log)[i])) - (1))] IN
                                                                                                                LET value23 == [cmd |-> LogPop] IN
                                                                                                                  IF ((value23).cmd) = (LogConcat)
                                                                                                                     THEN /\ LET plog10 == [plog EXCEPT ![i] = ((plog)[i]) \o ((value23).entries)] IN
                                                                                                                               IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                  THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                       /\ LET value312 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                            IF ((value312).cmd) = (LogConcat)
                                                                                                                                               THEN /\ plog' = [plog10 EXCEPT ![i] = ((plog10)[i]) \o ((value312).entries)]
                                                                                                                                                    /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                          THEN /\ LET value448 == m[self] IN
                                                                                                                                                                    /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value448)]
                                                                                                                                                                    /\ \/ /\ LET value548 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                               /\ ((network)[j]).enabled
                                                                                                                                                                               /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                               /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value548), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                       \/ /\ LET yielded_fd148 == (fd)[j] IN
                                                                                                                                                                               /\ yielded_fd148
                                                                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED network
                                                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                               /\ UNCHANGED << network, 
                                                                                                                                                                               fAdvCommitIdxCh >>
                                                                                                                                               ELSE /\ IF ((value312).cmd) = (LogPop)
                                                                                                                                                          THEN /\ plog' = [plog10 EXCEPT ![i] = SubSeq((plog10)[i], 1, (Len((plog10)[i])) - (1))]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value449 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value449)]
                                                                                                                                                                               /\ \/ /\ LET value549 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value549), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd149 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd149
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                                          ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value450 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value450)]
                                                                                                                                                                               /\ \/ /\ LET value550 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value550), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd150 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd150
                                                                                                                                                                                          /\ plog' = plog10
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ plog' = plog10
                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                  ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                             THEN /\ LET value451 == m[self] IN
                                                                                                                                                       /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value451)]
                                                                                                                                                       /\ \/ /\ LET value551 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                  /\ ((network)[j]).enabled
                                                                                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value551), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                          \/ /\ LET yielded_fd151 == (fd)[j] IN
                                                                                                                                                                  /\ yielded_fd151
                                                                                                                                                                  /\ plog' = plog10
                                                                                                                                                                  /\ log' = log7
                                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED network
                                                                                                                                             ELSE /\ plog' = plog10
                                                                                                                                                  /\ log' = log7
                                                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                  /\ UNCHANGED << network, 
                                                                                                                                                                  fAdvCommitIdxCh >>
                                                                                                                     ELSE /\ IF ((value23).cmd) = (LogPop)
                                                                                                                                THEN /\ LET plog11 == [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))] IN
                                                                                                                                          IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                             THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                  /\ LET value313 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                       IF ((value313).cmd) = (LogConcat)
                                                                                                                                                          THEN /\ plog' = [plog11 EXCEPT ![i] = ((plog11)[i]) \o ((value313).entries)]
                                                                                                                                                               /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                     THEN /\ LET value452 == m[self] IN
                                                                                                                                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value452)]
                                                                                                                                                                               /\ \/ /\ LET value552 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value552), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                  \/ /\ LET yielded_fd152 == (fd)[j] IN
                                                                                                                                                                                          /\ yielded_fd152
                                                                                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED network
                                                                                                                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                          /\ UNCHANGED << network, 
                                                                                                                                                                                          fAdvCommitIdxCh >>
                                                                                                                                                          ELSE /\ IF ((value313).cmd) = (LogPop)
                                                                                                                                                                     THEN /\ plog' = [plog11 EXCEPT ![i] = SubSeq((plog11)[i], 1, (Len((plog11)[i])) - (1))]
                                                                                                                                                                          /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET value453 == m[self] IN
                                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value453)]
                                                                                                                                                                                          /\ \/ /\ LET value553 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value553), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd153 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd153
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                                                     ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                                THEN /\ LET value454 == m[self] IN
                                                                                                                                                                                          /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value454)]
                                                                                                                                                                                          /\ \/ /\ LET value554 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                     /\ ((network)[j]).enabled
                                                                                                                                                                                                     /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                     /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value554), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                             \/ /\ LET yielded_fd154 == (fd)[j] IN
                                                                                                                                                                                                     /\ yielded_fd154
                                                                                                                                                                                                     /\ plog' = plog11
                                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                                /\ UNCHANGED network
                                                                                                                                                                                ELSE /\ plog' = plog11
                                                                                                                                                                                     /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                     /\ UNCHANGED << network, 
                                                                                                                                                                                                     fAdvCommitIdxCh >>
                                                                                                                                             ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                        THEN /\ LET value455 == m[self] IN
                                                                                                                                                                  /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value455)]
                                                                                                                                                                  /\ \/ /\ LET value555 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                             /\ ((network)[j]).enabled
                                                                                                                                                                             /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                             /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value555), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                     \/ /\ LET yielded_fd155 == (fd)[j] IN
                                                                                                                                                                             /\ yielded_fd155
                                                                                                                                                                             /\ plog' = plog11
                                                                                                                                                                             /\ log' = log7
                                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED network
                                                                                                                                                        ELSE /\ plog' = plog11
                                                                                                                                                             /\ log' = log7
                                                                                                                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                             /\ UNCHANGED << network, 
                                                                                                                                                                             fAdvCommitIdxCh >>
                                                                                                                                ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                                           THEN /\ log' = [log7 EXCEPT ![i] = ((log7)[i]) \o ((m[self]).mentries)]
                                                                                                                                                /\ LET value314 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                                                     IF ((value314).cmd) = (LogConcat)
                                                                                                                                                        THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value314).entries)]
                                                                                                                                                             /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                   THEN /\ LET value456 == m[self] IN
                                                                                                                                                                             /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value456)]
                                                                                                                                                                             /\ \/ /\ LET value556 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                        /\ ((network)[j]).enabled
                                                                                                                                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value556), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                \/ /\ LET yielded_fd156 == (fd)[j] IN
                                                                                                                                                                                        /\ yielded_fd156
                                                                                                                                                                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED network
                                                                                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                        /\ UNCHANGED << network, 
                                                                                                                                                                                        fAdvCommitIdxCh >>
                                                                                                                                                        ELSE /\ IF ((value314).cmd) = (LogPop)
                                                                                                                                                                   THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                                                        /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET value457 == m[self] IN
                                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value457)]
                                                                                                                                                                                        /\ \/ /\ LET value557 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value557), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd157 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd157
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                                   ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                                              THEN /\ LET value458 == m[self] IN
                                                                                                                                                                                        /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value458)]
                                                                                                                                                                                        /\ \/ /\ LET value558 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                                                   /\ ((network)[j]).enabled
                                                                                                                                                                                                   /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                                                   /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value558), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                           \/ /\ LET yielded_fd158 == (fd)[j] IN
                                                                                                                                                                                                   /\ yielded_fd158
                                                                                                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                              /\ UNCHANGED network
                                                                                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                                   /\ UNCHANGED << network, 
                                                                                                                                                                                                   fAdvCommitIdxCh >>
                                                                                                                                                                        /\ plog' = plog
                                                                                                                                           ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log7)[i])) >= (index))) /\ (((((log7)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                      THEN /\ LET value459 == m[self] IN
                                                                                                                                                                /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value459)]
                                                                                                                                                                /\ \/ /\ LET value559 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                           /\ ((network)[j]).enabled
                                                                                                                                                                           /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                           /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value559), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                   \/ /\ LET yielded_fd159 == (fd)[j] IN
                                                                                                                                                                           /\ yielded_fd159
                                                                                                                                                                           /\ log' = log7
                                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                      /\ UNCHANGED network
                                                                                                                                                      ELSE /\ log' = log7
                                                                                                                                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                           /\ UNCHANGED << network, 
                                                                                                                                                                           fAdvCommitIdxCh >>
                                                                                                                                                /\ plog' = plog
                                                                                                      ELSE /\ IF (((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) = ((m[self]).mprevLogIndex))
                                                                                                                 THEN /\ log' = [log EXCEPT ![i] = ((log)[i]) \o ((m[self]).mentries)]
                                                                                                                      /\ LET value315 == [cmd |-> LogConcat, entries |-> (m[self]).mentries] IN
                                                                                                                           IF ((value315).cmd) = (LogConcat)
                                                                                                                              THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value315).entries)]
                                                                                                                                   /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                         THEN /\ LET value460 == m[self] IN
                                                                                                                                                   /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value460)]
                                                                                                                                                   /\ \/ /\ LET value560 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                              /\ ((network)[j]).enabled
                                                                                                                                                              /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                              /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value560), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                      \/ /\ LET yielded_fd160 == (fd)[j] IN
                                                                                                                                                              /\ yielded_fd160
                                                                                                                                                              /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED network
                                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                              /\ UNCHANGED << network, 
                                                                                                                                                              fAdvCommitIdxCh >>
                                                                                                                              ELSE /\ IF ((value315).cmd) = (LogPop)
                                                                                                                                         THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                                              /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET value461 == m[self] IN
                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value461)]
                                                                                                                                                              /\ \/ /\ LET value561 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value561), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd161 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd161
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                         ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log')[i])) >= (index))) /\ (((((log')[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                                                    THEN /\ LET value462 == m[self] IN
                                                                                                                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value462)]
                                                                                                                                                              /\ \/ /\ LET value562 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                                         /\ ((network)[j]).enabled
                                                                                                                                                                         /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                                         /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value562), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                 \/ /\ LET yielded_fd162 == (fd)[j] IN
                                                                                                                                                                         /\ yielded_fd162
                                                                                                                                                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                                    /\ UNCHANGED network
                                                                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                                         /\ UNCHANGED << network, 
                                                                                                                                                                         fAdvCommitIdxCh >>
                                                                                                                                              /\ plog' = plog
                                                                                                                 ELSE /\ IF (((m[self]).mentries) = (<<>>)) \/ (((((m[self]).mentries) # (<<>>)) /\ ((Len((log)[i])) >= (index))) /\ (((((log)[i])[index]).term) = ((((m[self]).mentries)[1]).term)))
                                                                                                                            THEN /\ LET value463 == m[self] IN
                                                                                                                                      /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![i] = Append((fAdvCommitIdxCh)[i], value463)]
                                                                                                                                      /\ \/ /\ LET value563 == [mtype |-> AppendEntriesResponse, mterm |-> (currentTerm)[i], msuccess |-> TRUE, mmatchIndex |-> ((m[self]).mprevLogIndex) + (Len((m[self]).mentries)), msource |-> i, mdest |-> j] IN
                                                                                                                                                 /\ ((network)[j]).enabled
                                                                                                                                                 /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                                                 /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value563), enabled |-> ((network)[j]).enabled]]
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                         \/ /\ LET yielded_fd163 == (fd)[j] IN
                                                                                                                                                 /\ yielded_fd163
                                                                                                                                                 /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                            /\ UNCHANGED network
                                                                                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                                 /\ UNCHANGED << network, 
                                                                                                                                                 fAdvCommitIdxCh >>
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
                                                                                                      "Failure of assertion at line 2971, column 21.")
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
                                                                                                      "Failure of assertion at line 2991, column 21.")
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
                                                          ELSE /\ IF ((m[self]).mtype) = (ProposeMessage)
                                                                     THEN /\ LET i == self IN
                                                                               IF Debug
                                                                                  THEN /\ PrintT(<<"HandleProposeMessage", i, (currentTerm)[i], (state)[i]>>)
                                                                                       /\ IF ((state)[i]) = (Leader)
                                                                                             THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m[self]).mcmd] IN
                                                                                                       /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                                                                       /\ LET value60 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                            IF ((value60).cmd) = (LogConcat)
                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value60).entries)]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               ELSE /\ IF ((value60).cmd) = (LogPop)
                                                                                                                          THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                               /\ plog' = plog
                                                                                                  /\ UNCHANGED network
                                                                                             ELSE /\ IF ((leader)[i]) # (Nil)
                                                                                                        THEN /\ LET j == (leader)[i] IN
                                                                                                                  \/ /\ LET value70 == [mtype |-> ProposeMessage, mcmd |-> (m[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value70), enabled |-> ((network)[j]).enabled]]
                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                  \/ /\ LET yielded_fd20 == (fd)[j] IN
                                                                                                                          /\ yielded_fd20
                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                     /\ UNCHANGED network
                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                             /\ UNCHANGED network
                                                                                                  /\ UNCHANGED << log, 
                                                                                                                  plog >>
                                                                                  ELSE /\ IF ((state)[i]) = (Leader)
                                                                                             THEN /\ LET entry == [term |-> (currentTerm)[i], cmd |-> (m[self]).mcmd] IN
                                                                                                       /\ log' = [log EXCEPT ![i] = Append((log)[i], entry)]
                                                                                                       /\ LET value61 == [cmd |-> LogConcat, entries |-> <<entry>>] IN
                                                                                                            IF ((value61).cmd) = (LogConcat)
                                                                                                               THEN /\ plog' = [plog EXCEPT ![i] = ((plog)[i]) \o ((value61).entries)]
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                               ELSE /\ IF ((value61).cmd) = (LogPop)
                                                                                                                          THEN /\ plog' = [plog EXCEPT ![i] = SubSeq((plog)[i], 1, (Len((plog)[i])) - (1))]
                                                                                                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                               /\ plog' = plog
                                                                                                  /\ UNCHANGED network
                                                                                             ELSE /\ IF ((leader)[i]) # (Nil)
                                                                                                        THEN /\ LET j == (leader)[i] IN
                                                                                                                  \/ /\ LET value71 == [mtype |-> ProposeMessage, mcmd |-> (m[self]).mcmd, msource |-> i, mdest |-> j] IN
                                                                                                                          /\ ((network)[j]).enabled
                                                                                                                          /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                                          /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value71), enabled |-> ((network)[j]).enabled]]
                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                  \/ /\ LET yielded_fd21 == (fd)[j] IN
                                                                                                                          /\ yielded_fd21
                                                                                                                          /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                                     /\ UNCHANGED network
                                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                                                                             /\ UNCHANGED network
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
                                                    /\ UNCHANGED << leaderTimeout, 
                                                                    fAdvCommitIdxCh >>
                                         /\ UNCHANGED << votesResponded, 
                                                         votesGranted, 
                                                         becomeLeaderCh >>
                   /\ UNCHANGED << fd, commitIndex, propCh, acctCh, 
                                   appendEntriesCh, requestVoteSrvId, 
                                   appendEntriesSrvId, advanceCommitIndexSrvId, 
                                   becomeLeaderSrvId, fAdvCommitSrvId, 
                                   crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                   idx1, srvId1, newCommitIndex, srvId2, 
                                   srvId3, m0, srvId4, srvId5 >>

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
                                               plog, propCh, acctCh, 
                                               leaderTimeout, appendEntriesCh, 
                                               becomeLeaderCh, fAdvCommitIdxCh, 
                                               requestVoteSrvId, 
                                               appendEntriesSrvId, 
                                               advanceCommitIndexSrvId, 
                                               becomeLeaderSrvId, 
                                               fAdvCommitSrvId, crasherSrvId, 
                                               idx, m, srvId, srvId0, idx1, 
                                               srvId1, newCommitIndex, srvId2, 
                                               srvId3, m0, srvId4, srvId5 >>

requestVoteLoop(self) == /\ pc[self] = "requestVoteLoop"
                         /\ IF (idx0[self]) <= (NumServers)
                               THEN /\ IF (idx0[self]) # (srvId0[self])
                                          THEN /\ \/ /\ LET value80 == [mtype |-> RequestVoteRequest, mterm |-> (currentTerm)[srvId0[self]], mlastLogTerm |-> LastTerm((log)[srvId0[self]]), mlastLogIndex |-> Len((log)[srvId0[self]]), msource |-> srvId0[self], mdest |-> idx0[self]] IN
                                                          /\ ((network)[idx0[self]]).enabled
                                                          /\ (Len(((network)[idx0[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![idx0[self]] = [queue |-> Append(((network)[idx0[self]]).queue, value80), enabled |-> ((network)[idx0[self]]).enabled]]
                                                          /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                          /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
                                                  \/ /\ LET yielded_fd30 == (fd)[idx0[self]] IN
                                                          /\ yielded_fd30
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
                                         votesGranted, leader, propCh, acctCh, 
                                         leaderTimeout, appendEntriesCh, 
                                         becomeLeaderCh, fAdvCommitIdxCh, 
                                         requestVoteSrvId, appendEntriesSrvId, 
                                         advanceCommitIndexSrvId, 
                                         becomeLeaderSrvId, fAdvCommitSrvId, 
                                         crasherSrvId, idx, m, srvId, srvId0, 
                                         idx1, srvId1, newCommitIndex, srvId2, 
                                         srvId3, m0, srvId4, srvId5 >>

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
                                                 leader, propCh, acctCh, 
                                                 leaderTimeout, 
                                                 appendEntriesCh, 
                                                 becomeLeaderCh, 
                                                 fAdvCommitIdxCh, 
                                                 requestVoteSrvId, 
                                                 appendEntriesSrvId, 
                                                 advanceCommitIndexSrvId, 
                                                 becomeLeaderSrvId, 
                                                 fAdvCommitSrvId, crasherSrvId, 
                                                 idx, m, srvId, idx0, srvId0, 
                                                 srvId1, newCommitIndex, 
                                                 srvId2, srvId3, m0, srvId4, 
                                                 srvId5 >>

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
                                                            \/ /\ LET yielded_fd40 == (fd)[idx1[self]] IN
                                                                    /\ yielded_fd40
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
                                           votesGranted, leader, propCh, 
                                           acctCh, leaderTimeout, 
                                           appendEntriesCh, becomeLeaderCh, 
                                           fAdvCommitIdxCh, requestVoteSrvId, 
                                           appendEntriesSrvId, 
                                           advanceCommitIndexSrvId, 
                                           becomeLeaderSrvId, fAdvCommitSrvId, 
                                           crasherSrvId, idx, m, srvId, idx0, 
                                           srvId0, srvId1, newCommitIndex, 
                                           srvId2, srvId3, m0, srvId4, srvId5 >>

s2(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)

serverAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverAdvanceCommitIndexLoop"
                                      /\ IF TRUE
                                            THEN /\ ((state)[srvId2[self]]) = (Leader)
                                                 /\ LET i == srvId2[self] IN
                                                      LET maxAgreeIndex == FindMaxAgreeIndex((log)[i], i, (matchIndex)[i]) IN
                                                        LET nCommitIndex == IF ((maxAgreeIndex) # (Nil)) /\ (((((log)[i])[maxAgreeIndex]).term) = ((currentTerm)[i])) THEN maxAgreeIndex ELSE (commitIndex)[i] IN
                                                          /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = nCommitIndex]
                                                          /\ Assert((newCommitIndex'[self]) >= ((commitIndex)[i]), 
                                                                    "Failure of assertion at line 3209, column 11.")
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
                                                      requestVoteSrvId, 
                                                      appendEntriesSrvId, 
                                                      advanceCommitIndexSrvId, 
                                                      becomeLeaderSrvId, 
                                                      fAdvCommitSrvId, 
                                                      crasherSrvId, idx, m, 
                                                      srvId, idx0, srvId0, 
                                                      idx1, srvId1, srvId2, 
                                                      srvId3, m0, srvId4, 
                                                      srvId5 >>

applyLoop(self) == /\ pc[self] = "applyLoop"
                   /\ IF ((commitIndex)[srvId2[self]]) < (newCommitIndex[self])
                         THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId2[self]] = ((commitIndex)[srvId2[self]]) + (1)]
                              /\ LET i == srvId2[self] IN
                                   LET k == (commitIndex')[i] IN
                                     LET entry == ((log)[i])[k] IN
                                       LET cmd == (entry).cmd IN
                                         LET value100 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                           /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value100)]
                                           /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "serverAdvanceCommitIndexLoop"]
                              /\ UNCHANGED << commitIndex, acctCh >>
                   /\ UNCHANGED << network, fd, state, currentTerm, nextIndex, 
                                   matchIndex, log, plog, votedFor, 
                                   votesResponded, votesGranted, leader, 
                                   propCh, leaderTimeout, appendEntriesCh, 
                                   becomeLeaderCh, fAdvCommitIdxCh, 
                                   requestVoteSrvId, appendEntriesSrvId, 
                                   advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                   fAdvCommitSrvId, crasherSrvId, idx, m, 
                                   srvId, idx0, srvId0, idx1, srvId1, 
                                   newCommitIndex, srvId2, srvId3, m0, srvId4, 
                                   srvId5 >>

s3(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)

serverBecomeLeaderLoop(self) == /\ pc[self] = "serverBecomeLeaderLoop"
                                /\ (Len((becomeLeaderCh)[srvId3[self]])) > (0)
                                /\ LET res1 == Head((becomeLeaderCh)[srvId3[self]]) IN
                                     /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![srvId3[self]] = Tail((becomeLeaderCh)[srvId3[self]])]
                                     /\ LET yielded_becomeLeaderCh == res1 IN
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
                                                votesGranted, propCh, acctCh, 
                                                leaderTimeout, fAdvCommitIdxCh, 
                                                requestVoteSrvId, 
                                                appendEntriesSrvId, 
                                                advanceCommitIndexSrvId, 
                                                becomeLeaderSrvId, 
                                                fAdvCommitSrvId, crasherSrvId, 
                                                idx, m, srvId, idx0, srvId0, 
                                                idx1, srvId1, newCommitIndex, 
                                                srvId2, srvId3, m0, srvId4, 
                                                srvId5 >>

s4(self) == serverBecomeLeaderLoop(self)

serverFollowerAdvanceCommitIndexLoop(self) == /\ pc[self] = "serverFollowerAdvanceCommitIndexLoop"
                                              /\ IF TRUE
                                                    THEN /\ (Len((fAdvCommitIdxCh)[srvId4[self]])) > (0)
                                                         /\ LET res20 == Head((fAdvCommitIdxCh)[srvId4[self]]) IN
                                                              /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![srvId4[self]] = Tail((fAdvCommitIdxCh)[srvId4[self]])]
                                                              /\ LET yielded_fAdvCommitIdxCh0 == res20 IN
                                                                   /\ m0' = [m0 EXCEPT ![self] = yielded_fAdvCommitIdxCh0]
                                                                   /\ pc' = [pc EXCEPT ![self] = "acctLoop"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                         /\ UNCHANGED << fAdvCommitIdxCh, 
                                                                         m0 >>
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
                                                              requestVoteSrvId, 
                                                              appendEntriesSrvId, 
                                                              advanceCommitIndexSrvId, 
                                                              becomeLeaderSrvId, 
                                                              fAdvCommitSrvId, 
                                                              crasherSrvId, 
                                                              idx, m, srvId, 
                                                              idx0, srvId0, 
                                                              idx1, srvId1, 
                                                              newCommitIndex, 
                                                              srvId2, srvId3, 
                                                              srvId4, srvId5 >>

acctLoop(self) == /\ pc[self] = "acctLoop"
                  /\ IF ((commitIndex)[srvId4[self]]) < ((m0[self]).mcommitIndex)
                        THEN /\ commitIndex' = [commitIndex EXCEPT ![srvId4[self]] = ((commitIndex)[srvId4[self]]) + (1)]
                             /\ LET i == srvId4[self] IN
                                  LET k == (commitIndex')[i] IN
                                    LET entry == ((log)[i])[k] IN
                                      LET cmd == (entry).cmd IN
                                        LET value113 == [mtype |-> AcceptMessage, mcmd |-> cmd] IN
                                          /\ acctCh' = [acctCh EXCEPT ![i] = Append((acctCh)[i], value113)]
                                          /\ pc' = [pc EXCEPT ![self] = "acctLoop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverFollowerAdvanceCommitIndexLoop"]
                             /\ UNCHANGED << commitIndex, acctCh >>
                  /\ UNCHANGED << network, fd, state, currentTerm, nextIndex, 
                                  matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, propCh, 
                                  leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, fAdvCommitIdxCh, 
                                  requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  fAdvCommitSrvId, crasherSrvId, idx, m, srvId, 
                                  idx0, srvId0, idx1, srvId1, newCommitIndex, 
                                  srvId2, srvId3, m0, srvId4, srvId5 >>

s5(self) == serverFollowerAdvanceCommitIndexLoop(self) \/ acctLoop(self)

serverCrash(self) == /\ pc[self] = "serverCrash"
                     /\ LET value120 == FALSE IN
                          /\ network' = [network EXCEPT ![srvId5[self]] = [queue |-> ((network)[srvId5[self]]).queue, enabled |-> value120]]
                          /\ pc' = [pc EXCEPT ![self] = "fdUpdate"]
                     /\ UNCHANGED << fd, state, currentTerm, commitIndex, 
                                     nextIndex, matchIndex, log, plog, 
                                     votedFor, votesResponded, votesGranted, 
                                     leader, propCh, acctCh, leaderTimeout, 
                                     appendEntriesCh, becomeLeaderCh, 
                                     fAdvCommitIdxCh, requestVoteSrvId, 
                                     appendEntriesSrvId, 
                                     advanceCommitIndexSrvId, 
                                     becomeLeaderSrvId, fAdvCommitSrvId, 
                                     crasherSrvId, idx, m, srvId, idx0, srvId0, 
                                     idx1, srvId1, newCommitIndex, srvId2, 
                                     srvId3, m0, srvId4, srvId5 >>

fdUpdate(self) == /\ pc[self] = "fdUpdate"
                  /\ LET value130 == TRUE IN
                       /\ fd' = [fd EXCEPT ![srvId5[self]] = value130]
                       /\ pc' = [pc EXCEPT ![self] = "block_"]
                  /\ UNCHANGED << network, state, currentTerm, commitIndex, 
                                  nextIndex, matchIndex, log, plog, votedFor, 
                                  votesResponded, votesGranted, leader, propCh, 
                                  acctCh, leaderTimeout, appendEntriesCh, 
                                  becomeLeaderCh, fAdvCommitIdxCh, 
                                  requestVoteSrvId, appendEntriesSrvId, 
                                  advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                  fAdvCommitSrvId, crasherSrvId, idx, m, srvId, 
                                  idx0, srvId0, idx1, srvId1, newCommitIndex, 
                                  srvId2, srvId3, m0, srvId4, srvId5 >>

block_(self) == /\ pc[self] = "block_"
                /\ FALSE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                                nextIndex, matchIndex, log, plog, votedFor, 
                                votesResponded, votesGranted, leader, propCh, 
                                acctCh, leaderTimeout, appendEntriesCh, 
                                becomeLeaderCh, fAdvCommitIdxCh, 
                                requestVoteSrvId, appendEntriesSrvId, 
                                advanceCommitIndexSrvId, becomeLeaderSrvId, 
                                fAdvCommitSrvId, crasherSrvId, idx, m, srvId, 
                                idx0, srvId0, idx1, srvId1, newCommitIndex, 
                                srvId2, srvId3, m0, srvId4, srvId5 >>

crasher(self) == serverCrash(self) \/ fdUpdate(self) \/ block_(self)

sndReq == /\ pc[0] = "sndReq"
          /\ LET value140 == [mtype |-> ProposeMessage, mcmd |-> [data |-> "hello"]] IN
               /\ propCh' = [propCh EXCEPT ![1] = Append((propCh)[1], value140)]
               /\ pc' = [pc EXCEPT ![0] = "block"]
          /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                          nextIndex, matchIndex, log, plog, votedFor, 
                          votesResponded, votesGranted, leader, acctCh, 
                          leaderTimeout, appendEntriesCh, becomeLeaderCh, 
                          fAdvCommitIdxCh, requestVoteSrvId, 
                          appendEntriesSrvId, advanceCommitIndexSrvId, 
                          becomeLeaderSrvId, fAdvCommitSrvId, crasherSrvId, 
                          idx, m, srvId, idx0, srvId0, idx1, srvId1, 
                          newCommitIndex, srvId2, srvId3, m0, srvId4, srvId5 >>

block == /\ pc[0] = "block"
         /\ FALSE
         /\ pc' = [pc EXCEPT ![0] = "Done"]
         /\ UNCHANGED << network, fd, state, currentTerm, commitIndex, 
                         nextIndex, matchIndex, log, plog, votedFor, 
                         votesResponded, votesGranted, leader, propCh, acctCh, 
                         leaderTimeout, appendEntriesCh, becomeLeaderCh, 
                         fAdvCommitIdxCh, requestVoteSrvId, appendEntriesSrvId, 
                         advanceCommitIndexSrvId, becomeLeaderSrvId, 
                         fAdvCommitSrvId, crasherSrvId, idx, m, srvId, idx0, 
                         srvId0, idx1, srvId1, newCommitIndex, srvId2, srvId3, 
                         m0, srvId4, srvId5 >>

proposer == sndReq \/ block

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == proposer
           \/ (\E self \in ServerSet: s0(self))
           \/ (\E self \in ServerRequestVoteSet: s1(self))
           \/ (\E self \in ServerAppendEntriesSet: s2(self))
           \/ (\E self \in ServerAdvanceCommitIndexSet: s3(self))
           \/ (\E self \in ServerBecomeLeaderSet: s4(self))
           \/ (\E self \in ServerFollowerAdvanceCommitIndexSet: s5(self))
           \/ (\E self \in ServerCrasherSet: crasher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(s0(self))
        /\ \A self \in ServerRequestVoteSet : WF_vars(s1(self))
        /\ \A self \in ServerAppendEntriesSet : WF_vars(s2(self))
        /\ \A self \in ServerAdvanceCommitIndexSet : WF_vars(s3(self))
        /\ \A self \in ServerBecomeLeaderSet : WF_vars(s4(self))
        /\ \A self \in ServerFollowerAdvanceCommitIndexSet : WF_vars(s5(self))
        /\ \A self \in ServerCrasherSet : WF_vars(crasher(self))
        /\ WF_vars(proposer)

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
                                        /\ log[i][k] = log[j][k]
                                        /\ acctCh[i][k] = acctCh[j][k]

plogOK == \A i \in ServerSet: log[i] = plog[i]

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (state[i] = Leader /\ state'[i] = Leader)
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

\* Expected this to be violated if NumServers > 1,
\* but TLC doesn't report violation in case of NumServers = 2 because 
\* of using temporal properties and state constraints at the same time. 
\* TLC reports violation when NumServers = 3.
ElectionLiveness == []<>(\E i \in ServerSet: state[i] = Leader)

=============================================================================
