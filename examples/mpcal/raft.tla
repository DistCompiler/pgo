/--------------------------------- MODULE raft ---------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Terms
CONSTANTS Slots
CONSTANTS N
CONSTANTS BUFFER_SIZE
CONSTANTS Follower
CONSTANTS Candidate
CONSTANTS Leader
CONSTANTS Steps
ASSUME Follower # Candidate /\ Candidate # Leader /\ Follower # Leader

\* A reserved value.
CONSTANTS NULL

\* Based on https://www.usenix.org/system/files/conference/atc14/atc14-paper-ongaro.pdf (specifically pg 5)

(***************************************************************************
\* 4/12
    \* 14:05 - 14:40
    \* 15:25 - 16:00
\* 4/13
    \* 13:25 - 15:30
\* 4/15
    \* 15:45 - 17:00
\* 4/16
    \* 11:20 - 11:45
    \* 13:05 - 13:45
    \* 14:00 - 14:45
\* 4/17
    \* 13:30 - 

    
--mpcal Raft {
    define {
        Servers == 1..N
        Heartbeats == N+1..N*2
        Clients == N*2+1..N*3
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log,index) == (IF index > 0 /\ Len(log) >= index /\ Len(log) > 0 THEN log[index].term ELSE 0)
    }
    
    \* Invokes a RequestVote RPC on every Node
    macro SendRequestVotes(network, cterm, candidateId, lastLogIndex, lastLogTerm, idx) {
        while (idx <= Cardinality(Servers)) {
            \* granted and entries are unused, but NULL wouldn't type check
            network[idx] := [sender |-> candidateId, type |-> RequestVote, term |-> cterm, granted |-> FALSE, entries |-> <<>>,
                             prevIndex |-> lastLogIndex, prevTerm |-> lastLogTerm, commit |-> NULL];

            idx := idx + 1;
        };
    }
    
    \* Invokes an AppendEntries RPC on every Node (can serve to make progress or just as a heartbeat from the leader)
    macro SendAppendEntries(network, cterm, candidateId, nextIndex, matchIndex, log, leaderCommit, idx) {
        while (idx <= Cardinality(Servers)) {
            \* granted is unused, but NULL wouldn't type check
            network[idx] := [sender |-> candidateId, type |-> AppendEntries, term |-> cterm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)),
                             prevIndex |-> nextIndex[idx]-1, prevTerm |-> Term(log, nextIndex[idx]-1), commit |-> leaderCommit];
            
            idx := idx + 1;
        };
    }
    
    \* Invokes empty AppendEntries RPC on every Node (serves as heartbeats)
    macro SendHeartBeats(network, cterm, candidateId, idx) {
        while (idx <= Cardinality(Servers)) {
            \* granted is unused, but NULL wouldn't type check
            network[idx] := [sender |-> candidateId, type |-> AppendEntries, term |-> cterm, granted |-> FALSE, entries |-> <<>>,
                             prevIndex |-> NULL, prevTerm |-> 0, commit |-> NULL];
            
            idx := idx + 1;
        };
    }
    
    \* Stable FIFOQueues, returns full queue of messages
    mapping macro FIFOQueues {
        read {
            with (msgs = $variable) {
                $variable := <<>>;
                yield msgs;
            };
        }
  
        write {
            await Len($variable) < BUFFER_SIZE;
            yield Append($variable, $value);
        }
    }
    
    \* Unstable FIFOQueues, ensures correct algorithm behavior in the face of network issues
    mapping macro UnstableFIFOQueues {
        read {
            with (msgs = $variable) {
                $variable := <<>>;
                yield msgs;
            };
        }
  
        write {
            await Len($variable) < BUFFER_SIZE;
            either { yield IF Len($variable) > 0 THEN $variable ELSE Append($variable, $value); } \* messages may be dropped
            or { yield Append($variable, $value); } \* Sent correctly
            or { yield <<$value>> \o $variable; } \* Sent out of order
            or { yield Append(Append($variable, $value), $value); }; \* Or duplicated
        }
    }
    
    \* Non-deterministic timeout (abstracted out of the implementation so proper timeouts can be implemented)
    mapping macro Timeout {
        read {
            either { yield FALSE; } or { yield TRUE; };
        }
  
        write { assert(FALSE); }
    }
    
    mapping macro ID {
        read { yield $variable; }
  
        write { yield $value; }
    }
    
    mapping macro Timer {
        read {
            (*with (time = $variable) {
                $variable := IF time = 0 THEN Steps ELSE time -1;
                either { yield IF time = 0 THEN TRUE ELSE FALSE; } or { yield TRUE; };
            };*)
            yield TRUE;
        }
  
        write { assert(FALSE); }
    }
    
    \* defines semantics of unbuffered Go channels
    mapping macro UnbufferedChannel {
        read {
            await $variable.value # NULL;
            with (v = $variable) {
                $variable.value := NULL;
                yield v;
            }
        }
        write {
            await $variable.value = NULL;
            yield $value;
        }
    }
    
    archetype Heartbeat(ref network, ref heartbeatchan, iAmTheLeader, term, timer)
    variable index, cterm; {
  HBLoop: 
    while (TRUE) {
      CheckHeartBeat:
        await(iAmTheLeader[self - N]);

      SendHeartBeatLoop:
        while (iAmTheLeader[self - N]) {
            if (timer[self]) {
                index := 1;
                cterm := term[self - N];
    
                \* Make AppendEntries RPC calls to every other node (as a heartbeat and to notify them of new entries)
              SendHeartBeats:
                SendHeartBeats(network, cterm, self - N, index);
            };
        };
    };
    }
    
    archetype Client(ref stream)
    variable next = 0; {
  ClientLoop: 
    while (TRUE) {
      WriteValue:
        stream[self-2*N] := [value |-> next];
        next := next+1;
    };
    }

    archetype Node(ref network, ref applied, values, timeout, heartbeat, ref iAmTheLeader, ref term)
    \* Every variable should be name correspondingly with those described on page 5 of the Ongaro paper
    variable currentTerm = 0,
             votedFor = NULL,
             log = <<>>,
             state = Follower,
             commitIndex = 0,
             lastApplied = 0,
             nextIndex,
             matchIndex,
             iterator,
             votes = [t \in 0..Terms |-> {}],
             \* The following are temporary state:
             value,
             msg,
             response,
             msgs; {
  NodeLoop: 
    while (TRUE) {
      TimeoutCheck:
        if (state # Leader /\ timeout[currentTerm]) { \* Election timeout, become candidate
            state := Candidate;
            \* Increment term
            currentTerm := currentTerm + 1;
            \* Vote for self
            votes[currentTerm] := {self};
            votedFor := self;
            iterator := 1;

          SendReqVotes:
            SendRequestVotes(network, currentTerm, self, Len(log), Term(log, Len(log)), iterator);
        };

      LeaderCheck:
        \* TODO: check for value before broadcasting
        if (state = Leader) { \* I am the leader for the currentTerm
            \* Make progress (append to the log)
GetVal:     value := values[self].value;
            log := Append(log, [val |-> value, term |-> currentTerm]);

            matchIndex[self] := Len(log);
            nextIndex[self] := Len(log)+1;

          AdvanceIndex:
            \* Can we commit more entries?
            while (Cardinality({i \in Servers: matchIndex[i] > commitIndex})*2 > Cardinality(Servers) /\ Term(log, commitIndex+1) = currentTerm) {
                commitIndex := commitIndex + 1;
            };

          ApplyCommited:
            \* Apply newly commited values
            while(lastApplied < commitIndex) {
                lastApplied := lastApplied + 1;
                applied[self] := [value |-> log[lastApplied].val];
            };

            iterator := 1;

          SendAppendEntries:
            \* Make AppendEntries RPC calls to every other node (as a heartbeat and to notify them of new entries)
            SendAppendEntries(network, currentTerm, self, nextIndex, matchIndex, log, commitIndex, iterator);
        };

      RecvMsg:
        \* Handle messages
        msgs := network[self];

      ProcessMsgs:
        while (Len(msgs) > 0) {
GetMsg:     msg := Head(msgs);
            msgs := Tail(msgs);

          CheckMsgTerm:
            if (msg.term > currentTerm) { \* If hearing of a later term, someone else must be the leader for that term
                iAmTheLeader[self] := FALSE;
                state := Follower;
                currentTerm := msg.term;
                \* Haven't voted for anyone in the new term
                votedFor := NULL;
            };
        
            \* Implements RPC request and response logic in figure 5
MsgSwitch:  if (msg.type = AppendEntries) {
                response := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                             entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL];

                if ((msg.term >= currentTerm) /\ ((msg.prevIndex > 0 /\ Len(log) < msg.prevIndex)
                                                  \/ Term(log, msg.prevIndex) # msg.prevTerm)) {
                    \* Following entries don't have matching terms
                    assert(state # Leader);
                    \* Delete entries that don't match
                    log := SubSeq(log, 1, msg.prevIndex-1);
                } elseif (msg.term >= currentTerm /\ Len(log) = msg.prevIndex) {
                    \* Append new entries
                    log := log \o msg.entries;
AEValid:            response := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE,
                                 entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> NULL, commit |-> NULL];
                };

AESendResponse: network[msg.sender] := response;

                if (msg.commit > commitIndex) { \* Maybe we can commit more entries
                    commitIndex := IF msg.commit < Len(log) THEN msg.commit ELSE Len(log);

                  AEApplyCommitted:
                    while(lastApplied < commitIndex) {
                        lastApplied := lastApplied + 1;
                        applied[self] := [value |-> log[lastApplied].val];
                    };
                };
            } elseif (msg.type = RequestVote) {
                response := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE,
                             entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL];

                \* Check if the candidate's log is at least as up-to-date as ours, and we haven't voted for someone else
                if ((votedFor = NULL \/ votedFor = msg.sender)
                    /\ (msg.term >= currentTerm)
                    /\ (msg.prevTerm > Term(log, Len(log))
                       \/ (msg.prevTerm = Term(log, Len(log)) /\ msg.prevIndex >= Len(log)))) {
                    \* Have to overwrite entire response cause PGo doesn't support overwriting record entries
RVValid:            response := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> TRUE,
                                 entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL];
                    votedFor := msg.sender;
                };

              RVSendResponse:
                network[msg.sender] := response;
            } elseif (msg.type = AppendEntriesResponse /\ msg.term = currentTerm /\ state = Leader) {
                if (msg.granted) { \* They successfully added all entries! Update index we have recorded for them
                    nextIndex[msg.sender] := msg.prevIndex + 1;
                    matchIndex[msg.sender] := msg.prevIndex;
                } else {
                    \* The append was rejected, try again with the previous index
                    nextIndex[msg.sender] := IF nextIndex[msg.sender] - 1 > 1 THEN nextIndex[msg.sender] - 1 ELSE 1;

                  RetryAppendEntry:
                    network[msg.sender] := [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[msg.sender], Len(log)),
                                            prevIndex |-> nextIndex[msg.sender]-1, prevTerm |-> Term(log, nextIndex[msg.sender]-1), commit |-> commitIndex];
                };
            } elseif (msg.type = RequestVoteResponse /\ msg.term = currentTerm /\ state = Candidate) {
                if (msg.granted) { \* This server has received an additional vote
                    votes[msg.term] := votes[msg.term] \union {msg.sender};
                    if (Cardinality(votes[msg.term])*2 > Cardinality(Servers)) {
                        \* Voters form a quorum!
BecomeLeader:           state := Leader;
                        \* Re-initialize volatile state
                        matchIndex := [s3 \in Servers |-> 0];
                        nextIndex := [s4 \in Servers |-> 1];
                        \* Initial empty AppendEntry heartbeats are handled by HeartBeat archetype
                        iAmTheLeader[self] := TRUE;
                        term[self] := currentTerm;
                    };
                };
            };
        };
    };
    }

    variables
        valueStream = [p \in Servers |-> [value |-> NULL]],
        learnedChan = [l \in Servers |-> [value |-> NULL]],
        heartbeatChan = [s \in Servers |-> [value |-> NULL]],
        leader = [s \in Servers |-> FALSE],
        terms = [s \in Servers |-> NULL],
        timers = [s \in Heartbeats |-> 2],
        mailboxes = [id \in Servers |-> <<>>];

    \* TODO: Copy valuestream instantiation from paxos spec (queue)
    fair process (server \in Servers) == instance Node(ref mailboxes, [s \in 1..Slots |-> [value |-> NULL]], valueStream, TRUE, heartbeatChan, ref leader, ref terms)
        mapping mailboxes[_] via FIFOQueues
        mapping @2[_] via UnbufferedChannel
        mapping valueStream[_] via UnbufferedChannel
        mapping @4[_] via Timeout
        mapping heartbeatChan[_] via UnbufferedChannel
        mapping leader[_] via ID
        mapping terms[_] via ID;
    
    fair process (heartbeat \in Heartbeats) == instance Heartbeat(ref mailboxes, heartbeatChan, leader, terms, timers)
        mapping mailboxes[_] via FIFOQueues
        mapping heartbeatChan[_] via UnbufferedChannel
        mapping leader[_] via ID
        mapping terms[_] via ID
        mapping timers[_] via Timer;

    fair process (client \in Clients) == instance Client(ref valueStream)
        mapping valueStream[_] via UnbufferedChannel;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm Raft {
    variables valueStream = [p \in Servers |-> [value |-> NULL]], learnedChan = [l \in Servers |-> [value |-> NULL]], heartbeatChan = [s \in Servers |-> [value |-> NULL]], leader = [s \in Servers |-> FALSE], terms = [s \in Servers |-> NULL], timers = [s \in Heartbeats |-> 2], mailboxes = [id \in Servers |-> <<>>], timeoutRead, networkWrite, networkWrite0, networkWrite1, valuesRead, appliedWrite, appliedWrite0, networkWrite2, appliedWrite1, networkWrite3, networkRead, iAmTheLeaderWrite, iAmTheLeaderWrite0, ifResult, appliedWrite2, appliedWrite3, ifResult0, networkWrite4, termWrite, iAmTheLeaderWrite1, termWrite0, iAmTheLeaderWrite2, termWrite1, iAmTheLeaderWrite3, termWrite2, networkWrite5, iAmTheLeaderWrite4, termWrite3, networkWrite6, iAmTheLeaderWrite5, termWrite4, networkWrite7, appliedWrite4, iAmTheLeaderWrite6, termWrite5, iAmTheLeaderWrite7, networkWrite8, appliedWrite5, termWrite6, networkWrite9, appliedWrite6, iAmTheLeaderWrite8, termWrite7, iAmTheLeaderRead, timerRead, termRead, networkWrite10, networkWrite11, networkWrite12, networkWrite13, networkWrite14, streamWrite, streamWrite0;
    define {
        Servers == (1) .. (N)
        Heartbeats == ((N) + (1)) .. ((N) * (2))
        Clients == (((N) * (2)) + (1)) .. ((N) * (3))
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0
    }
    fair process (server \in Servers)
    variables appliedLocal = [s \in (1) .. (Slots) |-> [value |-> NULL]], timeoutLocal = TRUE, currentTerm = 0, votedFor = NULL, log = <<>>, state = Follower, commitIndex = 0, lastApplied = 0, nextIndex, matchIndex, iterator, votes = [t \in (0) .. (Terms) |-> {}], msg, response, msgs;
    {
        NodeLoop:
            if (TRUE) {
                TimeoutCheck:
                    either {
                        timeoutRead := FALSE;
                    } or {
                        timeoutRead := TRUE;
                    };
                    if (((state) # (Leader)) /\ (timeoutRead)) {
                        state := Candidate;
                        currentTerm := (currentTerm) + (1);
                        votes[currentTerm] := {self};
                        votedFor := self;
                        iterator := 1;
                        SendReqVotes:
                            if ((iterator) <= (Cardinality(Servers))) {
                                await (Len(mailboxes[iterator])) < (BUFFER_SIZE);
                                networkWrite := [mailboxes EXCEPT ![iterator] = Append(mailboxes[iterator], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log)), commit |-> NULL])];
                                iterator := (iterator) + (1);
                                networkWrite0 := networkWrite;
                                mailboxes := networkWrite0;
                                goto SendReqVotes;
                            } else {
                                networkWrite0 := mailboxes;
                                mailboxes := networkWrite0;
                            };
                    
                    } else {
                        networkWrite1 := mailboxes;
                        mailboxes := networkWrite1;
                    };
                
                LeaderCheck:
                    if ((state) = (Leader)) {
                        await ((valueStream[self]).value) # (NULL);
                        with (v0 = valueStream[self]) {
                            valueStream[self].value := NULL;
                            valuesRead := v0;
                        };
                        with (value = valuesRead) {
                            log := Append(log, [val |-> (value).value, term |-> currentTerm]);
                        };
                        matchIndex[self] := Len(log);
                        nextIndex[self] := (Len(log)) + (1);
                        AdvanceIndex:
                            if ((((Cardinality({i \in Servers : (matchIndex[i]) > (commitIndex)})) * (2)) > (Cardinality(Servers))) /\ ((Term(log, (commitIndex) + (1))) = (currentTerm))) {
                                commitIndex := (commitIndex) + (1);
                                goto AdvanceIndex;
                            };
                        
                        ApplyCommited:
                            if ((lastApplied) < (commitIndex)) {
                                lastApplied := (lastApplied) + (1);
                                await ((appliedLocal[self]).value) = (NULL);
                                appliedWrite := [appliedLocal EXCEPT ![self] = [value |-> (log[lastApplied]).val]];
                                appliedWrite0 := appliedWrite;
                                appliedLocal := appliedWrite0;
                                goto ApplyCommited;
                            } else {
                                iterator := 1;
                                appliedWrite0 := appliedLocal;
                                appliedLocal := appliedWrite0;
                            };
                        
                        SendAppendEntries:
                            if ((iterator) <= (Cardinality(Servers))) {
                                await (Len(mailboxes[iterator])) < (BUFFER_SIZE);
                                networkWrite := [mailboxes EXCEPT ![iterator] = Append(mailboxes[iterator], [sender |-> self, type |-> AppendEntries, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[iterator], Len(log)), prevIndex |-> (nextIndex[iterator]) - (1), prevTerm |-> Term(log, (nextIndex[iterator]) - (1)), commit |-> commitIndex])];
                                iterator := (iterator) + (1);
                                networkWrite2 := networkWrite;
                                mailboxes := networkWrite2;
                                goto SendAppendEntries;
                            } else {
                                networkWrite2 := mailboxes;
                                mailboxes := networkWrite2;
                            };
                    
                    } else {
                        appliedWrite1 := appliedLocal;
                        networkWrite3 := mailboxes;
                        mailboxes := networkWrite3;
                        appliedLocal := appliedWrite1;
                    };
                
                RecvMsg:
                    with (msgs0 = mailboxes[self]) {
                        networkWrite := [mailboxes EXCEPT ![self] = <<>>];
                        networkRead := msgs0;
                    };
                    msgs := networkRead;
                    mailboxes := networkWrite;
                
                ProcessMsgs:
                    if ((Len(msgs)) > (0)) {
                        GetMsg:
                            msg := Head(msgs);
                            msgs := Tail(msgs);
                        
                        CheckMsgTerm:
                            if (((msg).term) > (currentTerm)) {
                                iAmTheLeaderWrite := [leader EXCEPT ![self] = FALSE];
                                state := Follower;
                                currentTerm := (msg).term;
                                votedFor := NULL;
                                iAmTheLeaderWrite0 := iAmTheLeaderWrite;
                                leader := iAmTheLeaderWrite0;
                            } else {
                                iAmTheLeaderWrite0 := leader;
                                leader := iAmTheLeaderWrite0;
                            };
                        
                        MsgSwitch:
                            if (((msg).type) = (AppendEntries)) {
                                response := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL];
                                if ((((msg).term) >= (currentTerm)) /\ (((((msg).prevIndex) > (0)) /\ ((Len(log)) < ((msg).prevIndex))) \/ ((Term(log, (msg).prevIndex)) # ((msg).prevTerm)))) {
                                    assert (state) # (Leader);
                                    log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                                } else {
                                    if ((((msg).term) >= (currentTerm)) /\ ((Len(log)) = ((msg).prevIndex))) {
                                        log := (log) \o ((msg).entries);
                                        AEValid:
                                            response := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> NULL, commit |-> NULL];
                                    
                                    };
                                };
                                AESendResponse:
                                    await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], response)];
                                    if (((msg).commit) > (commitIndex)) {
                                        if (((msg).commit) < (Len(log))) {
                                            ifResult := (msg).commit;
                                        } else {
                                            ifResult := Len(log);
                                        };
                                        commitIndex := ifResult;
                                        mailboxes := networkWrite;
                                        AEApplyCommitted:
                                            if ((lastApplied) < (commitIndex)) {
                                                lastApplied := (lastApplied) + (1);
                                                await ((appliedLocal[self]).value) = (NULL);
                                                appliedWrite := [appliedLocal EXCEPT ![self] = [value |-> (log[lastApplied]).val]];
                                                appliedWrite2 := appliedWrite;
                                                appliedLocal := appliedWrite2;
                                                goto AEApplyCommitted;
                                            } else {
                                                appliedWrite2 := appliedLocal;
                                                appliedLocal := appliedWrite2;
                                                goto ProcessMsgs;
                                            };
                                    
                                    } else {
                                        appliedWrite3 := appliedLocal;
                                        mailboxes := networkWrite;
                                        appliedLocal := appliedWrite3;
                                        goto ProcessMsgs;
                                    };
                            
                            } else {
                                if (((msg).type) = (RequestVote)) {
                                    response := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL];
                                    if (((((votedFor) = (NULL)) \/ ((votedFor) = ((msg).sender))) /\ (((msg).term) >= (currentTerm))) /\ ((((msg).prevTerm) > (Term(log, Len(log)))) \/ ((((msg).prevTerm) = (Term(log, Len(log)))) /\ (((msg).prevIndex) >= (Len(log)))))) {
                                        RVValid:
                                            response.granted := TRUE;
                                            votedFor := (msg).sender;
                                    
                                    };
                                    RVSendResponse:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], response)];
                                        mailboxes := networkWrite;
                                        goto ProcessMsgs;
                                
                                } else {
                                    if (((((msg).type) = (AppendEntriesResponse)) /\ (((msg).term) = (currentTerm))) /\ ((state) = (Leader))) {
                                        if ((msg).granted) {
                                            nextIndex[msg.sender] := ((msg).prevIndex) + (1);
                                            matchIndex[msg.sender] := (msg).prevIndex;
                                            networkWrite4 := mailboxes;
                                            networkWrite5 := networkWrite4;
                                            iAmTheLeaderWrite4 := leader;
                                            termWrite3 := terms;
                                            networkWrite6 := networkWrite5;
                                            iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                            termWrite4 := termWrite3;
                                            networkWrite7 := networkWrite6;
                                            appliedWrite4 := appliedLocal;
                                            iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                            termWrite5 := termWrite4;
                                            mailboxes := networkWrite7;
                                            appliedLocal := appliedWrite4;
                                            leader := iAmTheLeaderWrite6;
                                            terms := termWrite5;
                                            goto ProcessMsgs;
                                        } else {
                                            if (((nextIndex[(msg).sender]) - (1)) > (1)) {
                                                ifResult0 := (nextIndex[(msg).sender]) - (1);
                                            } else {
                                                ifResult0 := 1;
                                            };
                                            nextIndex[msg.sender] := ifResult0;
                                            RetryAppendEntry:
                                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[(msg).sender], Len(log)), prevIndex |-> (nextIndex[(msg).sender]) - (1), prevTerm |-> Term(log, (nextIndex[(msg).sender]) - (1)), commit |-> commitIndex])];
                                                mailboxes := networkWrite;
                                                goto ProcessMsgs;
                                        
                                        };
                                    } else {
                                        if (((((msg).type) = (RequestVoteResponse)) /\ (((msg).term) = (currentTerm))) /\ ((state) = (Candidate))) {
                                            if ((msg).granted) {
                                                votes[msg.term] := (votes[(msg).term]) \union ({(msg).sender});
                                                if (((Cardinality(votes[(msg).term])) * (2)) > (Cardinality(Servers))) {
                                                    state := Leader;
                                                    matchIndex := [s3 \in Servers |-> 0];
                                                    nextIndex := [s4 \in Servers |-> 1];
                                                    iAmTheLeaderWrite := [leader EXCEPT ![self] = TRUE];
                                                    termWrite := [terms EXCEPT ![self] = currentTerm];
                                                    iAmTheLeaderWrite1 := iAmTheLeaderWrite;
                                                    termWrite0 := termWrite;
                                                    iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                                    termWrite1 := termWrite0;
                                                    iAmTheLeaderWrite3 := iAmTheLeaderWrite2;
                                                    termWrite2 := termWrite1;
                                                    networkWrite5 := mailboxes;
                                                    iAmTheLeaderWrite4 := iAmTheLeaderWrite3;
                                                    termWrite3 := termWrite2;
                                                    networkWrite6 := networkWrite5;
                                                    iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                                    termWrite4 := termWrite3;
                                                    networkWrite7 := networkWrite6;
                                                    appliedWrite4 := appliedLocal;
                                                    iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                                    termWrite5 := termWrite4;
                                                    mailboxes := networkWrite7;
                                                    appliedLocal := appliedWrite4;
                                                    leader := iAmTheLeaderWrite6;
                                                    terms := termWrite5;
                                                    goto ProcessMsgs;
                                                } else {
                                                    iAmTheLeaderWrite1 := leader;
                                                    termWrite0 := terms;
                                                    iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                                    termWrite1 := termWrite0;
                                                    iAmTheLeaderWrite3 := iAmTheLeaderWrite2;
                                                    termWrite2 := termWrite1;
                                                    networkWrite5 := mailboxes;
                                                    iAmTheLeaderWrite4 := iAmTheLeaderWrite3;
                                                    termWrite3 := termWrite2;
                                                    networkWrite6 := networkWrite5;
                                                    iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                                    termWrite4 := termWrite3;
                                                    networkWrite7 := networkWrite6;
                                                    appliedWrite4 := appliedLocal;
                                                    iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                                    termWrite5 := termWrite4;
                                                    mailboxes := networkWrite7;
                                                    appliedLocal := appliedWrite4;
                                                    leader := iAmTheLeaderWrite6;
                                                    terms := termWrite5;
                                                    goto ProcessMsgs;
                                                };
                                            } else {
                                                iAmTheLeaderWrite2 := leader;
                                                termWrite1 := terms;
                                                iAmTheLeaderWrite3 := iAmTheLeaderWrite2;
                                                termWrite2 := termWrite1;
                                                networkWrite5 := mailboxes;
                                                iAmTheLeaderWrite4 := iAmTheLeaderWrite3;
                                                termWrite3 := termWrite2;
                                                networkWrite6 := networkWrite5;
                                                iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                                termWrite4 := termWrite3;
                                                networkWrite7 := networkWrite6;
                                                appliedWrite4 := appliedLocal;
                                                iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                                termWrite5 := termWrite4;
                                                mailboxes := networkWrite7;
                                                appliedLocal := appliedWrite4;
                                                leader := iAmTheLeaderWrite6;
                                                terms := termWrite5;
                                                goto ProcessMsgs;
                                            };
                                        } else {
                                            iAmTheLeaderWrite3 := leader;
                                            termWrite2 := terms;
                                            networkWrite5 := mailboxes;
                                            iAmTheLeaderWrite4 := iAmTheLeaderWrite3;
                                            termWrite3 := termWrite2;
                                            networkWrite6 := networkWrite5;
                                            iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                            termWrite4 := termWrite3;
                                            networkWrite7 := networkWrite6;
                                            appliedWrite4 := appliedLocal;
                                            iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                            termWrite5 := termWrite4;
                                            mailboxes := networkWrite7;
                                            appliedLocal := appliedWrite4;
                                            leader := iAmTheLeaderWrite6;
                                            terms := termWrite5;
                                            goto ProcessMsgs;
                                        };
                                    };
                                };
                            };
                    
                    } else {
                        iAmTheLeaderWrite7 := leader;
                        networkWrite8 := mailboxes;
                        appliedWrite5 := appliedLocal;
                        termWrite6 := terms;
                        mailboxes := networkWrite8;
                        appliedLocal := appliedWrite5;
                        leader := iAmTheLeaderWrite7;
                        terms := termWrite6;
                        goto NodeLoop;
                    };
            
            } else {
                networkWrite9 := mailboxes;
                appliedWrite6 := appliedLocal;
                iAmTheLeaderWrite8 := leader;
                termWrite7 := terms;
                mailboxes := networkWrite9;
                appliedLocal := appliedWrite6;
                leader := iAmTheLeaderWrite8;
                terms := termWrite7;
            };
    
    }
    fair process (heartbeat \in Heartbeats)
    variables index, cterm;
    {
        HBLoop:
            if (TRUE) {
                CheckHeartBeat:
                    iAmTheLeaderRead := leader[(self) - (N)];
                    await iAmTheLeaderRead;
                
                SendHeartBeatLoop:
                    iAmTheLeaderRead := leader[(self) - (N)];
                    if (iAmTheLeaderRead) {
                        timerRead := TRUE;
                        if (timerRead) {
                            index := 1;
                            termRead := terms[(self) - (N)];
                            cterm := termRead;
                            SendHeartBeats:
                                if ((index) <= (Cardinality(Servers))) {
                                    await (Len(mailboxes[index])) < (BUFFER_SIZE);
                                    networkWrite10 := [mailboxes EXCEPT ![index] = Append(mailboxes[index], [sender |-> (self) - (N), type |-> AppendEntries, term |-> cterm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> 0, commit |-> NULL])];
                                    index := (index) + (1);
                                    networkWrite11 := networkWrite10;
                                    mailboxes := networkWrite11;
                                    goto SendHeartBeats;
                                } else {
                                    networkWrite11 := mailboxes;
                                    mailboxes := networkWrite11;
                                    goto SendHeartBeatLoop;
                                };
                        
                        } else {
                            networkWrite12 := mailboxes;
                            networkWrite13 := networkWrite12;
                            mailboxes := networkWrite13;
                            goto SendHeartBeatLoop;
                        };
                    } else {
                        networkWrite13 := mailboxes;
                        mailboxes := networkWrite13;
                        goto HBLoop;
                    };
            
            } else {
                networkWrite14 := mailboxes;
                mailboxes := networkWrite14;
            };
    
    }
    fair process (client \in Clients)
    variables next = 0;
    {
        ClientLoop:
            if (TRUE) {
                WriteValue:
                    await ((valueStream[(self) - ((2) * (N))]).value) = (NULL);
                    streamWrite := [valueStream EXCEPT ![(self) - ((2) * (N))] = [value |-> next]];
                    next := (next) + (1);
                    valueStream := streamWrite;
                    goto ClientLoop;
            
            } else {
                streamWrite0 := valueStream;
                valueStream := streamWrite0;
            };
    
    }
}
\* END PLUSCAL TRANSLATION

******************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES valueStream, learnedChan, heartbeatChan, leader, terms, timers, 
          mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
          valuesRead, appliedWrite, appliedWrite0, networkWrite2, 
          appliedWrite1, networkWrite3, networkRead, iAmTheLeaderWrite, 
          iAmTheLeaderWrite0, ifResult, appliedWrite2, appliedWrite3, 
          ifResult0, networkWrite4, termWrite, iAmTheLeaderWrite1, termWrite0, 
          iAmTheLeaderWrite2, termWrite1, iAmTheLeaderWrite3, termWrite2, 
          networkWrite5, iAmTheLeaderWrite4, termWrite3, networkWrite6, 
          iAmTheLeaderWrite5, termWrite4, networkWrite7, appliedWrite4, 
          iAmTheLeaderWrite6, termWrite5, iAmTheLeaderWrite7, networkWrite8, 
          appliedWrite5, termWrite6, networkWrite9, appliedWrite6, 
          iAmTheLeaderWrite8, termWrite7, iAmTheLeaderRead, timerRead, 
          termRead, networkWrite10, networkWrite11, networkWrite12, 
          networkWrite13, networkWrite14, streamWrite, streamWrite0, pc

(* define statement *)
Servers == (1) .. (N)
Heartbeats == ((N) + (1)) .. ((N) * (2))
Clients == (((N) * (2)) + (1)) .. ((N) * (3))
RequestVote == 0
RequestVoteResponse == 1
AppendEntries == 2
AppendEntriesResponse == 3
Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0

VARIABLES appliedLocal, timeoutLocal, currentTerm, votedFor, log, state, 
          commitIndex, lastApplied, nextIndex, matchIndex, iterator, votes, 
          msg, response, msgs, index, cterm, next

vars == << valueStream, learnedChan, heartbeatChan, leader, terms, timers, 
           mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
           valuesRead, appliedWrite, appliedWrite0, networkWrite2, 
           appliedWrite1, networkWrite3, networkRead, iAmTheLeaderWrite, 
           iAmTheLeaderWrite0, ifResult, appliedWrite2, appliedWrite3, 
           ifResult0, networkWrite4, termWrite, iAmTheLeaderWrite1, 
           termWrite0, iAmTheLeaderWrite2, termWrite1, iAmTheLeaderWrite3, 
           termWrite2, networkWrite5, iAmTheLeaderWrite4, termWrite3, 
           networkWrite6, iAmTheLeaderWrite5, termWrite4, networkWrite7, 
           appliedWrite4, iAmTheLeaderWrite6, termWrite5, iAmTheLeaderWrite7, 
           networkWrite8, appliedWrite5, termWrite6, networkWrite9, 
           appliedWrite6, iAmTheLeaderWrite8, termWrite7, iAmTheLeaderRead, 
           timerRead, termRead, networkWrite10, networkWrite11, 
           networkWrite12, networkWrite13, networkWrite14, streamWrite, 
           streamWrite0, pc, appliedLocal, timeoutLocal, currentTerm, 
           votedFor, log, state, commitIndex, lastApplied, nextIndex, 
           matchIndex, iterator, votes, msg, response, msgs, index, cterm, 
           next >>

ProcSet == (Servers) \cup (Heartbeats) \cup (Clients)

Init == (* Global variables *)
        /\ valueStream = [p \in Servers |-> [value |-> NULL]]
        /\ learnedChan = [l \in Servers |-> [value |-> NULL]]
        /\ heartbeatChan = [s \in Servers |-> [value |-> NULL]]
        /\ leader = [s \in Servers |-> FALSE]
        /\ terms = [s \in Servers |-> NULL]
        /\ timers = [s \in Heartbeats |-> 2]
        /\ mailboxes = [id \in Servers |-> <<>>]
        /\ timeoutRead = defaultInitValue
        /\ networkWrite = defaultInitValue
        /\ networkWrite0 = defaultInitValue
        /\ networkWrite1 = defaultInitValue
        /\ valuesRead = defaultInitValue
        /\ appliedWrite = defaultInitValue
        /\ appliedWrite0 = defaultInitValue
        /\ networkWrite2 = defaultInitValue
        /\ appliedWrite1 = defaultInitValue
        /\ networkWrite3 = defaultInitValue
        /\ networkRead = defaultInitValue
        /\ iAmTheLeaderWrite = defaultInitValue
        /\ iAmTheLeaderWrite0 = defaultInitValue
        /\ ifResult = defaultInitValue
        /\ appliedWrite2 = defaultInitValue
        /\ appliedWrite3 = defaultInitValue
        /\ ifResult0 = defaultInitValue
        /\ networkWrite4 = defaultInitValue
        /\ termWrite = defaultInitValue
        /\ iAmTheLeaderWrite1 = defaultInitValue
        /\ termWrite0 = defaultInitValue
        /\ iAmTheLeaderWrite2 = defaultInitValue
        /\ termWrite1 = defaultInitValue
        /\ iAmTheLeaderWrite3 = defaultInitValue
        /\ termWrite2 = defaultInitValue
        /\ networkWrite5 = defaultInitValue
        /\ iAmTheLeaderWrite4 = defaultInitValue
        /\ termWrite3 = defaultInitValue
        /\ networkWrite6 = defaultInitValue
        /\ iAmTheLeaderWrite5 = defaultInitValue
        /\ termWrite4 = defaultInitValue
        /\ networkWrite7 = defaultInitValue
        /\ appliedWrite4 = defaultInitValue
        /\ iAmTheLeaderWrite6 = defaultInitValue
        /\ termWrite5 = defaultInitValue
        /\ iAmTheLeaderWrite7 = defaultInitValue
        /\ networkWrite8 = defaultInitValue
        /\ appliedWrite5 = defaultInitValue
        /\ termWrite6 = defaultInitValue
        /\ networkWrite9 = defaultInitValue
        /\ appliedWrite6 = defaultInitValue
        /\ iAmTheLeaderWrite8 = defaultInitValue
        /\ termWrite7 = defaultInitValue
        /\ iAmTheLeaderRead = defaultInitValue
        /\ timerRead = defaultInitValue
        /\ termRead = defaultInitValue
        /\ networkWrite10 = defaultInitValue
        /\ networkWrite11 = defaultInitValue
        /\ networkWrite12 = defaultInitValue
        /\ networkWrite13 = defaultInitValue
        /\ networkWrite14 = defaultInitValue
        /\ streamWrite = defaultInitValue
        /\ streamWrite0 = defaultInitValue
        (* Process server *)
        /\ appliedLocal = [self \in Servers |-> [s \in (1) .. (Slots) |-> [value |-> NULL]]]
        /\ timeoutLocal = [self \in Servers |-> TRUE]
        /\ currentTerm = [self \in Servers |-> 0]
        /\ votedFor = [self \in Servers |-> NULL]
        /\ log = [self \in Servers |-> <<>>]
        /\ state = [self \in Servers |-> Follower]
        /\ commitIndex = [self \in Servers |-> 0]
        /\ lastApplied = [self \in Servers |-> 0]
        /\ nextIndex = [self \in Servers |-> defaultInitValue]
        /\ matchIndex = [self \in Servers |-> defaultInitValue]
        /\ iterator = [self \in Servers |-> defaultInitValue]
        /\ votes = [self \in Servers |-> [t \in (0) .. (Terms) |-> {}]]
        /\ msg = [self \in Servers |-> defaultInitValue]
        /\ response = [self \in Servers |-> defaultInitValue]
        /\ msgs = [self \in Servers |-> defaultInitValue]
        (* Process heartbeat *)
        /\ index = [self \in Heartbeats |-> defaultInitValue]
        /\ cterm = [self \in Heartbeats |-> defaultInitValue]
        (* Process client *)
        /\ next = [self \in Clients |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "NodeLoop"
                                        [] self \in Heartbeats -> "HBLoop"
                                        [] self \in Clients -> "ClientLoop"]

NodeLoop(self) == /\ pc[self] = "NodeLoop"
                  /\ IF TRUE
                        THEN /\ pc' = [pc EXCEPT ![self] = "TimeoutCheck"]
                             /\ UNCHANGED << leader, terms, mailboxes, 
                                             networkWrite9, appliedWrite6, 
                                             iAmTheLeaderWrite8, termWrite7, 
                                             appliedLocal >>
                        ELSE /\ networkWrite9' = mailboxes
                             /\ appliedWrite6' = appliedLocal[self]
                             /\ iAmTheLeaderWrite8' = leader
                             /\ termWrite7' = terms
                             /\ mailboxes' = networkWrite9'
                             /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                             /\ leader' = iAmTheLeaderWrite8'
                             /\ terms' = termWrite7'
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                  timers, timeoutRead, networkWrite, 
                                  networkWrite0, networkWrite1, valuesRead, 
                                  appliedWrite, appliedWrite0, networkWrite2, 
                                  appliedWrite1, networkWrite3, networkRead, 
                                  iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                  ifResult, appliedWrite2, appliedWrite3, 
                                  ifResult0, networkWrite4, termWrite, 
                                  iAmTheLeaderWrite1, termWrite0, 
                                  iAmTheLeaderWrite2, termWrite1, 
                                  iAmTheLeaderWrite3, termWrite2, 
                                  networkWrite5, iAmTheLeaderWrite4, 
                                  termWrite3, networkWrite6, 
                                  iAmTheLeaderWrite5, termWrite4, 
                                  networkWrite7, appliedWrite4, 
                                  iAmTheLeaderWrite6, termWrite5, 
                                  iAmTheLeaderWrite7, networkWrite8, 
                                  appliedWrite5, termWrite6, iAmTheLeaderRead, 
                                  timerRead, termRead, networkWrite10, 
                                  networkWrite11, networkWrite12, 
                                  networkWrite13, networkWrite14, streamWrite, 
                                  streamWrite0, timeoutLocal, currentTerm, 
                                  votedFor, log, state, commitIndex, 
                                  lastApplied, nextIndex, matchIndex, iterator, 
                                  votes, msg, response, msgs, index, cterm, 
                                  next >>

TimeoutCheck(self) == /\ pc[self] = "TimeoutCheck"
                      /\ \/ /\ timeoutRead' = FALSE
                         \/ /\ timeoutRead' = TRUE
                      /\ IF ((state[self]) # (Leader)) /\ (timeoutRead')
                            THEN /\ state' = [state EXCEPT ![self] = Candidate]
                                 /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                                 /\ votes' = [votes EXCEPT ![self][currentTerm'[self]] = {self}]
                                 /\ votedFor' = [votedFor EXCEPT ![self] = self]
                                 /\ iterator' = [iterator EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "SendReqVotes"]
                                 /\ UNCHANGED << mailboxes, networkWrite1 >>
                            ELSE /\ networkWrite1' = mailboxes
                                 /\ mailboxes' = networkWrite1'
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderCheck"]
                                 /\ UNCHANGED << currentTerm, votedFor, state, 
                                                 iterator, votes >>
                      /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                      leader, terms, timers, networkWrite, 
                                      networkWrite0, valuesRead, appliedWrite, 
                                      appliedWrite0, networkWrite2, 
                                      appliedWrite1, networkWrite3, 
                                      networkRead, iAmTheLeaderWrite, 
                                      iAmTheLeaderWrite0, ifResult, 
                                      appliedWrite2, appliedWrite3, ifResult0, 
                                      networkWrite4, termWrite, 
                                      iAmTheLeaderWrite1, termWrite0, 
                                      iAmTheLeaderWrite2, termWrite1, 
                                      iAmTheLeaderWrite3, termWrite2, 
                                      networkWrite5, iAmTheLeaderWrite4, 
                                      termWrite3, networkWrite6, 
                                      iAmTheLeaderWrite5, termWrite4, 
                                      networkWrite7, appliedWrite4, 
                                      iAmTheLeaderWrite6, termWrite5, 
                                      iAmTheLeaderWrite7, networkWrite8, 
                                      appliedWrite5, termWrite6, networkWrite9, 
                                      appliedWrite6, iAmTheLeaderWrite8, 
                                      termWrite7, iAmTheLeaderRead, timerRead, 
                                      termRead, networkWrite10, networkWrite11, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, streamWrite, 
                                      streamWrite0, appliedLocal, timeoutLocal, 
                                      log, commitIndex, lastApplied, nextIndex, 
                                      matchIndex, msg, response, msgs, index, 
                                      cterm, next >>

SendReqVotes(self) == /\ pc[self] = "SendReqVotes"
                      /\ IF (iterator[self]) <= (Cardinality(Servers))
                            THEN /\ (Len(mailboxes[iterator[self]])) < (BUFFER_SIZE)
                                 /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = Append(mailboxes[iterator[self]], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self])), commit |-> NULL])]
                                 /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                 /\ networkWrite0' = networkWrite'
                                 /\ mailboxes' = networkWrite0'
                                 /\ pc' = [pc EXCEPT ![self] = "SendReqVotes"]
                            ELSE /\ networkWrite0' = mailboxes
                                 /\ mailboxes' = networkWrite0'
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderCheck"]
                                 /\ UNCHANGED << networkWrite, iterator >>
                      /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                      leader, terms, timers, timeoutRead, 
                                      networkWrite1, valuesRead, appliedWrite, 
                                      appliedWrite0, networkWrite2, 
                                      appliedWrite1, networkWrite3, 
                                      networkRead, iAmTheLeaderWrite, 
                                      iAmTheLeaderWrite0, ifResult, 
                                      appliedWrite2, appliedWrite3, ifResult0, 
                                      networkWrite4, termWrite, 
                                      iAmTheLeaderWrite1, termWrite0, 
                                      iAmTheLeaderWrite2, termWrite1, 
                                      iAmTheLeaderWrite3, termWrite2, 
                                      networkWrite5, iAmTheLeaderWrite4, 
                                      termWrite3, networkWrite6, 
                                      iAmTheLeaderWrite5, termWrite4, 
                                      networkWrite7, appliedWrite4, 
                                      iAmTheLeaderWrite6, termWrite5, 
                                      iAmTheLeaderWrite7, networkWrite8, 
                                      appliedWrite5, termWrite6, networkWrite9, 
                                      appliedWrite6, iAmTheLeaderWrite8, 
                                      termWrite7, iAmTheLeaderRead, timerRead, 
                                      termRead, networkWrite10, networkWrite11, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, streamWrite, 
                                      streamWrite0, appliedLocal, timeoutLocal, 
                                      currentTerm, votedFor, log, state, 
                                      commitIndex, lastApplied, nextIndex, 
                                      matchIndex, votes, msg, response, msgs, 
                                      index, cterm, next >>

LeaderCheck(self) == /\ pc[self] = "LeaderCheck"
                     /\ IF (state[self]) = (Leader)
                           THEN /\ ((valueStream[self]).value) # (NULL)
                                /\ LET v0 == valueStream[self] IN
                                     /\ valueStream' = [valueStream EXCEPT ![self].value = NULL]
                                     /\ valuesRead' = v0
                                /\ LET value == valuesRead' IN
                                     log' = [log EXCEPT ![self] = Append(log[self], [val |-> (value).value, term |-> currentTerm[self]])]
                                /\ matchIndex' = [matchIndex EXCEPT ![self][self] = Len(log'[self])]
                                /\ nextIndex' = [nextIndex EXCEPT ![self][self] = (Len(log'[self])) + (1)]
                                /\ pc' = [pc EXCEPT ![self] = "AdvanceIndex"]
                                /\ UNCHANGED << mailboxes, appliedWrite1, 
                                                networkWrite3, appliedLocal >>
                           ELSE /\ appliedWrite1' = appliedLocal[self]
                                /\ networkWrite3' = mailboxes
                                /\ mailboxes' = networkWrite3'
                                /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite1']
                                /\ pc' = [pc EXCEPT ![self] = "RecvMsg"]
                                /\ UNCHANGED << valueStream, valuesRead, log, 
                                                nextIndex, matchIndex >>
                     /\ UNCHANGED << learnedChan, heartbeatChan, leader, terms, 
                                     timers, timeoutRead, networkWrite, 
                                     networkWrite0, networkWrite1, 
                                     appliedWrite, appliedWrite0, 
                                     networkWrite2, networkRead, 
                                     iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                     ifResult, appliedWrite2, appliedWrite3, 
                                     ifResult0, networkWrite4, termWrite, 
                                     iAmTheLeaderWrite1, termWrite0, 
                                     iAmTheLeaderWrite2, termWrite1, 
                                     iAmTheLeaderWrite3, termWrite2, 
                                     networkWrite5, iAmTheLeaderWrite4, 
                                     termWrite3, networkWrite6, 
                                     iAmTheLeaderWrite5, termWrite4, 
                                     networkWrite7, appliedWrite4, 
                                     iAmTheLeaderWrite6, termWrite5, 
                                     iAmTheLeaderWrite7, networkWrite8, 
                                     appliedWrite5, termWrite6, networkWrite9, 
                                     appliedWrite6, iAmTheLeaderWrite8, 
                                     termWrite7, iAmTheLeaderRead, timerRead, 
                                     termRead, networkWrite10, networkWrite11, 
                                     networkWrite12, networkWrite13, 
                                     networkWrite14, streamWrite, streamWrite0, 
                                     timeoutLocal, currentTerm, votedFor, 
                                     state, commitIndex, lastApplied, iterator, 
                                     votes, msg, response, msgs, index, cterm, 
                                     next >>

AdvanceIndex(self) == /\ pc[self] = "AdvanceIndex"
                      /\ IF (((Cardinality({i \in Servers : (matchIndex[self][i]) > (commitIndex[self])})) * (2)) > (Cardinality(Servers))) /\ ((Term(log[self], (commitIndex[self]) + (1))) = (currentTerm[self]))
                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (commitIndex[self]) + (1)]
                                 /\ pc' = [pc EXCEPT ![self] = "AdvanceIndex"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ApplyCommited"]
                                 /\ UNCHANGED commitIndex
                      /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                      leader, terms, timers, mailboxes, 
                                      timeoutRead, networkWrite, networkWrite0, 
                                      networkWrite1, valuesRead, appliedWrite, 
                                      appliedWrite0, networkWrite2, 
                                      appliedWrite1, networkWrite3, 
                                      networkRead, iAmTheLeaderWrite, 
                                      iAmTheLeaderWrite0, ifResult, 
                                      appliedWrite2, appliedWrite3, ifResult0, 
                                      networkWrite4, termWrite, 
                                      iAmTheLeaderWrite1, termWrite0, 
                                      iAmTheLeaderWrite2, termWrite1, 
                                      iAmTheLeaderWrite3, termWrite2, 
                                      networkWrite5, iAmTheLeaderWrite4, 
                                      termWrite3, networkWrite6, 
                                      iAmTheLeaderWrite5, termWrite4, 
                                      networkWrite7, appliedWrite4, 
                                      iAmTheLeaderWrite6, termWrite5, 
                                      iAmTheLeaderWrite7, networkWrite8, 
                                      appliedWrite5, termWrite6, networkWrite9, 
                                      appliedWrite6, iAmTheLeaderWrite8, 
                                      termWrite7, iAmTheLeaderRead, timerRead, 
                                      termRead, networkWrite10, networkWrite11, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, streamWrite, 
                                      streamWrite0, appliedLocal, timeoutLocal, 
                                      currentTerm, votedFor, log, state, 
                                      lastApplied, nextIndex, matchIndex, 
                                      iterator, votes, msg, response, msgs, 
                                      index, cterm, next >>

ApplyCommited(self) == /\ pc[self] = "ApplyCommited"
                       /\ IF (lastApplied[self]) < (commitIndex[self])
                             THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                                  /\ ((appliedLocal[self][self]).value) = (NULL)
                                  /\ appliedWrite' = [appliedLocal[self] EXCEPT ![self] = [value |-> (log[self][lastApplied'[self]]).val]]
                                  /\ appliedWrite0' = appliedWrite'
                                  /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                                  /\ pc' = [pc EXCEPT ![self] = "ApplyCommited"]
                                  /\ UNCHANGED iterator
                             ELSE /\ iterator' = [iterator EXCEPT ![self] = 1]
                                  /\ appliedWrite0' = appliedLocal[self]
                                  /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                                  /\ pc' = [pc EXCEPT ![self] = "SendAppendEntries"]
                                  /\ UNCHANGED << appliedWrite, lastApplied >>
                       /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                       leader, terms, timers, mailboxes, 
                                       timeoutRead, networkWrite, 
                                       networkWrite0, networkWrite1, 
                                       valuesRead, networkWrite2, 
                                       appliedWrite1, networkWrite3, 
                                       networkRead, iAmTheLeaderWrite, 
                                       iAmTheLeaderWrite0, ifResult, 
                                       appliedWrite2, appliedWrite3, ifResult0, 
                                       networkWrite4, termWrite, 
                                       iAmTheLeaderWrite1, termWrite0, 
                                       iAmTheLeaderWrite2, termWrite1, 
                                       iAmTheLeaderWrite3, termWrite2, 
                                       networkWrite5, iAmTheLeaderWrite4, 
                                       termWrite3, networkWrite6, 
                                       iAmTheLeaderWrite5, termWrite4, 
                                       networkWrite7, appliedWrite4, 
                                       iAmTheLeaderWrite6, termWrite5, 
                                       iAmTheLeaderWrite7, networkWrite8, 
                                       appliedWrite5, termWrite6, 
                                       networkWrite9, appliedWrite6, 
                                       iAmTheLeaderWrite8, termWrite7, 
                                       iAmTheLeaderRead, timerRead, termRead, 
                                       networkWrite10, networkWrite11, 
                                       networkWrite12, networkWrite13, 
                                       networkWrite14, streamWrite, 
                                       streamWrite0, timeoutLocal, currentTerm, 
                                       votedFor, log, state, commitIndex, 
                                       nextIndex, matchIndex, votes, msg, 
                                       response, msgs, index, cterm, next >>

SendAppendEntries(self) == /\ pc[self] = "SendAppendEntries"
                           /\ IF (iterator[self]) <= (Cardinality(Servers))
                                 THEN /\ (Len(mailboxes[iterator[self]])) < (BUFFER_SIZE)
                                      /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = Append(mailboxes[iterator[self]], [sender |-> self, type |-> AppendEntries, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][iterator[self]], Len(log[self])), prevIndex |-> (nextIndex[self][iterator[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][iterator[self]]) - (1)), commit |-> commitIndex[self]])]
                                      /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                      /\ networkWrite2' = networkWrite'
                                      /\ mailboxes' = networkWrite2'
                                      /\ pc' = [pc EXCEPT ![self] = "SendAppendEntries"]
                                 ELSE /\ networkWrite2' = mailboxes
                                      /\ mailboxes' = networkWrite2'
                                      /\ pc' = [pc EXCEPT ![self] = "RecvMsg"]
                                      /\ UNCHANGED << networkWrite, iterator >>
                           /\ UNCHANGED << valueStream, learnedChan, 
                                           heartbeatChan, leader, terms, 
                                           timers, timeoutRead, networkWrite0, 
                                           networkWrite1, valuesRead, 
                                           appliedWrite, appliedWrite0, 
                                           appliedWrite1, networkWrite3, 
                                           networkRead, iAmTheLeaderWrite, 
                                           iAmTheLeaderWrite0, ifResult, 
                                           appliedWrite2, appliedWrite3, 
                                           ifResult0, networkWrite4, termWrite, 
                                           iAmTheLeaderWrite1, termWrite0, 
                                           iAmTheLeaderWrite2, termWrite1, 
                                           iAmTheLeaderWrite3, termWrite2, 
                                           networkWrite5, iAmTheLeaderWrite4, 
                                           termWrite3, networkWrite6, 
                                           iAmTheLeaderWrite5, termWrite4, 
                                           networkWrite7, appliedWrite4, 
                                           iAmTheLeaderWrite6, termWrite5, 
                                           iAmTheLeaderWrite7, networkWrite8, 
                                           appliedWrite5, termWrite6, 
                                           networkWrite9, appliedWrite6, 
                                           iAmTheLeaderWrite8, termWrite7, 
                                           iAmTheLeaderRead, timerRead, 
                                           termRead, networkWrite10, 
                                           networkWrite11, networkWrite12, 
                                           networkWrite13, networkWrite14, 
                                           streamWrite, streamWrite0, 
                                           appliedLocal, timeoutLocal, 
                                           currentTerm, votedFor, log, state, 
                                           commitIndex, lastApplied, nextIndex, 
                                           matchIndex, votes, msg, response, 
                                           msgs, index, cterm, next >>

RecvMsg(self) == /\ pc[self] = "RecvMsg"
                 /\ LET msgs0 == mailboxes[self] IN
                      /\ networkWrite' = [mailboxes EXCEPT ![self] = <<>>]
                      /\ networkRead' = msgs0
                 /\ msgs' = [msgs EXCEPT ![self] = networkRead']
                 /\ mailboxes' = networkWrite'
                 /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                 /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                 leader, terms, timers, timeoutRead, 
                                 networkWrite0, networkWrite1, valuesRead, 
                                 appliedWrite, appliedWrite0, networkWrite2, 
                                 appliedWrite1, networkWrite3, 
                                 iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                 ifResult, appliedWrite2, appliedWrite3, 
                                 ifResult0, networkWrite4, termWrite, 
                                 iAmTheLeaderWrite1, termWrite0, 
                                 iAmTheLeaderWrite2, termWrite1, 
                                 iAmTheLeaderWrite3, termWrite2, networkWrite5, 
                                 iAmTheLeaderWrite4, termWrite3, networkWrite6, 
                                 iAmTheLeaderWrite5, termWrite4, networkWrite7, 
                                 appliedWrite4, iAmTheLeaderWrite6, termWrite5, 
                                 iAmTheLeaderWrite7, networkWrite8, 
                                 appliedWrite5, termWrite6, networkWrite9, 
                                 appliedWrite6, iAmTheLeaderWrite8, termWrite7, 
                                 iAmTheLeaderRead, timerRead, termRead, 
                                 networkWrite10, networkWrite11, 
                                 networkWrite12, networkWrite13, 
                                 networkWrite14, streamWrite, streamWrite0, 
                                 appliedLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg, response, index, cterm, next >>

ProcessMsgs(self) == /\ pc[self] = "ProcessMsgs"
                     /\ IF (Len(msgs[self])) > (0)
                           THEN /\ pc' = [pc EXCEPT ![self] = "GetMsg"]
                                /\ UNCHANGED << leader, terms, mailboxes, 
                                                iAmTheLeaderWrite7, 
                                                networkWrite8, appliedWrite5, 
                                                termWrite6, appliedLocal >>
                           ELSE /\ iAmTheLeaderWrite7' = leader
                                /\ networkWrite8' = mailboxes
                                /\ appliedWrite5' = appliedLocal[self]
                                /\ termWrite6' = terms
                                /\ mailboxes' = networkWrite8'
                                /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite5']
                                /\ leader' = iAmTheLeaderWrite7'
                                /\ terms' = termWrite6'
                                /\ pc' = [pc EXCEPT ![self] = "NodeLoop"]
                     /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                     timers, timeoutRead, networkWrite, 
                                     networkWrite0, networkWrite1, valuesRead, 
                                     appliedWrite, appliedWrite0, 
                                     networkWrite2, appliedWrite1, 
                                     networkWrite3, networkRead, 
                                     iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                     ifResult, appliedWrite2, appliedWrite3, 
                                     ifResult0, networkWrite4, termWrite, 
                                     iAmTheLeaderWrite1, termWrite0, 
                                     iAmTheLeaderWrite2, termWrite1, 
                                     iAmTheLeaderWrite3, termWrite2, 
                                     networkWrite5, iAmTheLeaderWrite4, 
                                     termWrite3, networkWrite6, 
                                     iAmTheLeaderWrite5, termWrite4, 
                                     networkWrite7, appliedWrite4, 
                                     iAmTheLeaderWrite6, termWrite5, 
                                     networkWrite9, appliedWrite6, 
                                     iAmTheLeaderWrite8, termWrite7, 
                                     iAmTheLeaderRead, timerRead, termRead, 
                                     networkWrite10, networkWrite11, 
                                     networkWrite12, networkWrite13, 
                                     networkWrite14, streamWrite, streamWrite0, 
                                     timeoutLocal, currentTerm, votedFor, log, 
                                     state, commitIndex, lastApplied, 
                                     nextIndex, matchIndex, iterator, votes, 
                                     msg, response, msgs, index, cterm, next >>

GetMsg(self) == /\ pc[self] = "GetMsg"
                /\ msg' = [msg EXCEPT ![self] = Head(msgs[self])]
                /\ msgs' = [msgs EXCEPT ![self] = Tail(msgs[self])]
                /\ pc' = [pc EXCEPT ![self] = "CheckMsgTerm"]
                /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                leader, terms, timers, mailboxes, timeoutRead, 
                                networkWrite, networkWrite0, networkWrite1, 
                                valuesRead, appliedWrite, appliedWrite0, 
                                networkWrite2, appliedWrite1, networkWrite3, 
                                networkRead, iAmTheLeaderWrite, 
                                iAmTheLeaderWrite0, ifResult, appliedWrite2, 
                                appliedWrite3, ifResult0, networkWrite4, 
                                termWrite, iAmTheLeaderWrite1, termWrite0, 
                                iAmTheLeaderWrite2, termWrite1, 
                                iAmTheLeaderWrite3, termWrite2, networkWrite5, 
                                iAmTheLeaderWrite4, termWrite3, networkWrite6, 
                                iAmTheLeaderWrite5, termWrite4, networkWrite7, 
                                appliedWrite4, iAmTheLeaderWrite6, termWrite5, 
                                iAmTheLeaderWrite7, networkWrite8, 
                                appliedWrite5, termWrite6, networkWrite9, 
                                appliedWrite6, iAmTheLeaderWrite8, termWrite7, 
                                iAmTheLeaderRead, timerRead, termRead, 
                                networkWrite10, networkWrite11, networkWrite12, 
                                networkWrite13, networkWrite14, streamWrite, 
                                streamWrite0, appliedLocal, timeoutLocal, 
                                currentTerm, votedFor, log, state, commitIndex, 
                                lastApplied, nextIndex, matchIndex, iterator, 
                                votes, response, index, cterm, next >>

CheckMsgTerm(self) == /\ pc[self] = "CheckMsgTerm"
                      /\ IF ((msg[self]).term) > (currentTerm[self])
                            THEN /\ iAmTheLeaderWrite' = [leader EXCEPT ![self] = FALSE]
                                 /\ state' = [state EXCEPT ![self] = Follower]
                                 /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
                                 /\ votedFor' = [votedFor EXCEPT ![self] = NULL]
                                 /\ iAmTheLeaderWrite0' = iAmTheLeaderWrite'
                                 /\ leader' = iAmTheLeaderWrite0'
                            ELSE /\ iAmTheLeaderWrite0' = leader
                                 /\ leader' = iAmTheLeaderWrite0'
                                 /\ UNCHANGED << iAmTheLeaderWrite, 
                                                 currentTerm, votedFor, state >>
                      /\ pc' = [pc EXCEPT ![self] = "MsgSwitch"]
                      /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                      terms, timers, mailboxes, timeoutRead, 
                                      networkWrite, networkWrite0, 
                                      networkWrite1, valuesRead, appliedWrite, 
                                      appliedWrite0, networkWrite2, 
                                      appliedWrite1, networkWrite3, 
                                      networkRead, ifResult, appliedWrite2, 
                                      appliedWrite3, ifResult0, networkWrite4, 
                                      termWrite, iAmTheLeaderWrite1, 
                                      termWrite0, iAmTheLeaderWrite2, 
                                      termWrite1, iAmTheLeaderWrite3, 
                                      termWrite2, networkWrite5, 
                                      iAmTheLeaderWrite4, termWrite3, 
                                      networkWrite6, iAmTheLeaderWrite5, 
                                      termWrite4, networkWrite7, appliedWrite4, 
                                      iAmTheLeaderWrite6, termWrite5, 
                                      iAmTheLeaderWrite7, networkWrite8, 
                                      appliedWrite5, termWrite6, networkWrite9, 
                                      appliedWrite6, iAmTheLeaderWrite8, 
                                      termWrite7, iAmTheLeaderRead, timerRead, 
                                      termRead, networkWrite10, networkWrite11, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, streamWrite, 
                                      streamWrite0, appliedLocal, timeoutLocal, 
                                      log, commitIndex, lastApplied, nextIndex, 
                                      matchIndex, iterator, votes, msg, 
                                      response, msgs, index, cterm, next >>

MsgSwitch(self) == /\ pc[self] = "MsgSwitch"
                   /\ IF ((msg[self]).type) = (AppendEntries)
                         THEN /\ response' = [response EXCEPT ![self] = [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL]]
                              /\ IF (((msg[self]).term) >= (currentTerm[self])) /\ (((((msg[self]).prevIndex) > (0)) /\ ((Len(log[self])) < ((msg[self]).prevIndex))) \/ ((Term(log[self], (msg[self]).prevIndex)) # ((msg[self]).prevTerm)))
                                    THEN /\ Assert((state[self]) # (Leader), 
                                                   "Failure of assertion at line 504, column 37.")
                                         /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg[self]).prevIndex) - (1))]
                                         /\ pc' = [pc EXCEPT ![self] = "AESendResponse"]
                                    ELSE /\ IF (((msg[self]).term) >= (currentTerm[self])) /\ ((Len(log[self])) = ((msg[self]).prevIndex))
                                               THEN /\ log' = [log EXCEPT ![self] = (log[self]) \o ((msg[self]).entries)]
                                                    /\ pc' = [pc EXCEPT ![self] = "AEValid"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "AESendResponse"]
                                                    /\ log' = log
                              /\ UNCHANGED << leader, terms, mailboxes, 
                                              iAmTheLeaderWrite, ifResult0, 
                                              networkWrite4, termWrite, 
                                              iAmTheLeaderWrite1, termWrite0, 
                                              iAmTheLeaderWrite2, termWrite1, 
                                              iAmTheLeaderWrite3, termWrite2, 
                                              networkWrite5, 
                                              iAmTheLeaderWrite4, termWrite3, 
                                              networkWrite6, 
                                              iAmTheLeaderWrite5, termWrite4, 
                                              networkWrite7, appliedWrite4, 
                                              iAmTheLeaderWrite6, termWrite5, 
                                              appliedLocal, state, nextIndex, 
                                              matchIndex, votes >>
                         ELSE /\ IF ((msg[self]).type) = (RequestVote)
                                    THEN /\ response' = [response EXCEPT ![self] = [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> NULL, commit |-> NULL]]
                                         /\ IF ((((votedFor[self]) = (NULL)) \/ ((votedFor[self]) = ((msg[self]).sender))) /\ (((msg[self]).term) >= (currentTerm[self]))) /\ ((((msg[self]).prevTerm) > (Term(log[self], Len(log[self])))) \/ ((((msg[self]).prevTerm) = (Term(log[self], Len(log[self])))) /\ (((msg[self]).prevIndex) >= (Len(log[self])))))
                                               THEN /\ pc' = [pc EXCEPT ![self] = "RVValid"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "RVSendResponse"]
                                         /\ UNCHANGED << leader, terms, 
                                                         mailboxes, 
                                                         iAmTheLeaderWrite, 
                                                         ifResult0, 
                                                         networkWrite4, 
                                                         termWrite, 
                                                         iAmTheLeaderWrite1, 
                                                         termWrite0, 
                                                         iAmTheLeaderWrite2, 
                                                         termWrite1, 
                                                         iAmTheLeaderWrite3, 
                                                         termWrite2, 
                                                         networkWrite5, 
                                                         iAmTheLeaderWrite4, 
                                                         termWrite3, 
                                                         networkWrite6, 
                                                         iAmTheLeaderWrite5, 
                                                         termWrite4, 
                                                         networkWrite7, 
                                                         appliedWrite4, 
                                                         iAmTheLeaderWrite6, 
                                                         termWrite5, 
                                                         appliedLocal, state, 
                                                         nextIndex, matchIndex, 
                                                         votes >>
                                    ELSE /\ IF ((((msg[self]).type) = (AppendEntriesResponse)) /\ (((msg[self]).term) = (currentTerm[self]))) /\ ((state[self]) = (Leader))
                                               THEN /\ IF (msg[self]).granted
                                                          THEN /\ nextIndex' = [nextIndex EXCEPT ![self][msg[self].sender] = ((msg[self]).prevIndex) + (1)]
                                                               /\ matchIndex' = [matchIndex EXCEPT ![self][msg[self].sender] = (msg[self]).prevIndex]
                                                               /\ networkWrite4' = mailboxes
                                                               /\ networkWrite5' = networkWrite4'
                                                               /\ iAmTheLeaderWrite4' = leader
                                                               /\ termWrite3' = terms
                                                               /\ networkWrite6' = networkWrite5'
                                                               /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                               /\ termWrite4' = termWrite3'
                                                               /\ networkWrite7' = networkWrite6'
                                                               /\ appliedWrite4' = appliedLocal[self]
                                                               /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                               /\ termWrite5' = termWrite4'
                                                               /\ mailboxes' = networkWrite7'
                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                               /\ leader' = iAmTheLeaderWrite6'
                                                               /\ terms' = termWrite5'
                                                               /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                                               /\ UNCHANGED ifResult0
                                                          ELSE /\ IF ((nextIndex[self][(msg[self]).sender]) - (1)) > (1)
                                                                     THEN /\ ifResult0' = (nextIndex[self][(msg[self]).sender]) - (1)
                                                                     ELSE /\ ifResult0' = 1
                                                               /\ nextIndex' = [nextIndex EXCEPT ![self][msg[self].sender] = ifResult0']
                                                               /\ pc' = [pc EXCEPT ![self] = "RetryAppendEntry"]
                                                               /\ UNCHANGED << leader, 
                                                                               terms, 
                                                                               mailboxes, 
                                                                               networkWrite4, 
                                                                               networkWrite5, 
                                                                               iAmTheLeaderWrite4, 
                                                                               termWrite3, 
                                                                               networkWrite6, 
                                                                               iAmTheLeaderWrite5, 
                                                                               termWrite4, 
                                                                               networkWrite7, 
                                                                               appliedWrite4, 
                                                                               iAmTheLeaderWrite6, 
                                                                               termWrite5, 
                                                                               appliedLocal, 
                                                                               matchIndex >>
                                                    /\ UNCHANGED << iAmTheLeaderWrite, 
                                                                    termWrite, 
                                                                    iAmTheLeaderWrite1, 
                                                                    termWrite0, 
                                                                    iAmTheLeaderWrite2, 
                                                                    termWrite1, 
                                                                    iAmTheLeaderWrite3, 
                                                                    termWrite2, 
                                                                    state, 
                                                                    votes >>
                                               ELSE /\ IF ((((msg[self]).type) = (RequestVoteResponse)) /\ (((msg[self]).term) = (currentTerm[self]))) /\ ((state[self]) = (Candidate))
                                                          THEN /\ IF (msg[self]).granted
                                                                     THEN /\ votes' = [votes EXCEPT ![self][msg[self].term] = (votes[self][(msg[self]).term]) \union ({(msg[self]).sender})]
                                                                          /\ IF ((Cardinality(votes'[self][(msg[self]).term])) * (2)) > (Cardinality(Servers))
                                                                                THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                     /\ matchIndex' = [matchIndex EXCEPT ![self] = [s3 \in Servers |-> 0]]
                                                                                     /\ nextIndex' = [nextIndex EXCEPT ![self] = [s4 \in Servers |-> 1]]
                                                                                     /\ iAmTheLeaderWrite' = [leader EXCEPT ![self] = TRUE]
                                                                                     /\ termWrite' = [terms EXCEPT ![self] = currentTerm[self]]
                                                                                     /\ iAmTheLeaderWrite1' = iAmTheLeaderWrite'
                                                                                     /\ termWrite0' = termWrite'
                                                                                     /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                                                     /\ termWrite1' = termWrite0'
                                                                                     /\ iAmTheLeaderWrite3' = iAmTheLeaderWrite2'
                                                                                     /\ termWrite2' = termWrite1'
                                                                                     /\ networkWrite5' = mailboxes
                                                                                     /\ iAmTheLeaderWrite4' = iAmTheLeaderWrite3'
                                                                                     /\ termWrite3' = termWrite2'
                                                                                     /\ networkWrite6' = networkWrite5'
                                                                                     /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                                                     /\ termWrite4' = termWrite3'
                                                                                     /\ networkWrite7' = networkWrite6'
                                                                                     /\ appliedWrite4' = appliedLocal[self]
                                                                                     /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                                                     /\ termWrite5' = termWrite4'
                                                                                     /\ mailboxes' = networkWrite7'
                                                                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                                     /\ leader' = iAmTheLeaderWrite6'
                                                                                     /\ terms' = termWrite5'
                                                                                     /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                                                                ELSE /\ iAmTheLeaderWrite1' = leader
                                                                                     /\ termWrite0' = terms
                                                                                     /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                                                     /\ termWrite1' = termWrite0'
                                                                                     /\ iAmTheLeaderWrite3' = iAmTheLeaderWrite2'
                                                                                     /\ termWrite2' = termWrite1'
                                                                                     /\ networkWrite5' = mailboxes
                                                                                     /\ iAmTheLeaderWrite4' = iAmTheLeaderWrite3'
                                                                                     /\ termWrite3' = termWrite2'
                                                                                     /\ networkWrite6' = networkWrite5'
                                                                                     /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                                                     /\ termWrite4' = termWrite3'
                                                                                     /\ networkWrite7' = networkWrite6'
                                                                                     /\ appliedWrite4' = appliedLocal[self]
                                                                                     /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                                                     /\ termWrite5' = termWrite4'
                                                                                     /\ mailboxes' = networkWrite7'
                                                                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                                     /\ leader' = iAmTheLeaderWrite6'
                                                                                     /\ terms' = termWrite5'
                                                                                     /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                                                                     /\ UNCHANGED << iAmTheLeaderWrite, 
                                                                                                     termWrite, 
                                                                                                     state, 
                                                                                                     nextIndex, 
                                                                                                     matchIndex >>
                                                                     ELSE /\ iAmTheLeaderWrite2' = leader
                                                                          /\ termWrite1' = terms
                                                                          /\ iAmTheLeaderWrite3' = iAmTheLeaderWrite2'
                                                                          /\ termWrite2' = termWrite1'
                                                                          /\ networkWrite5' = mailboxes
                                                                          /\ iAmTheLeaderWrite4' = iAmTheLeaderWrite3'
                                                                          /\ termWrite3' = termWrite2'
                                                                          /\ networkWrite6' = networkWrite5'
                                                                          /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                                          /\ termWrite4' = termWrite3'
                                                                          /\ networkWrite7' = networkWrite6'
                                                                          /\ appliedWrite4' = appliedLocal[self]
                                                                          /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                                          /\ termWrite5' = termWrite4'
                                                                          /\ mailboxes' = networkWrite7'
                                                                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                          /\ leader' = iAmTheLeaderWrite6'
                                                                          /\ terms' = termWrite5'
                                                                          /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                                                          /\ UNCHANGED << iAmTheLeaderWrite, 
                                                                                          termWrite, 
                                                                                          iAmTheLeaderWrite1, 
                                                                                          termWrite0, 
                                                                                          state, 
                                                                                          nextIndex, 
                                                                                          matchIndex, 
                                                                                          votes >>
                                                          ELSE /\ iAmTheLeaderWrite3' = leader
                                                               /\ termWrite2' = terms
                                                               /\ networkWrite5' = mailboxes
                                                               /\ iAmTheLeaderWrite4' = iAmTheLeaderWrite3'
                                                               /\ termWrite3' = termWrite2'
                                                               /\ networkWrite6' = networkWrite5'
                                                               /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                               /\ termWrite4' = termWrite3'
                                                               /\ networkWrite7' = networkWrite6'
                                                               /\ appliedWrite4' = appliedLocal[self]
                                                               /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                               /\ termWrite5' = termWrite4'
                                                               /\ mailboxes' = networkWrite7'
                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                               /\ leader' = iAmTheLeaderWrite6'
                                                               /\ terms' = termWrite5'
                                                               /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                                               /\ UNCHANGED << iAmTheLeaderWrite, 
                                                                               termWrite, 
                                                                               iAmTheLeaderWrite1, 
                                                                               termWrite0, 
                                                                               iAmTheLeaderWrite2, 
                                                                               termWrite1, 
                                                                               state, 
                                                                               nextIndex, 
                                                                               matchIndex, 
                                                                               votes >>
                                                    /\ UNCHANGED << ifResult0, 
                                                                    networkWrite4 >>
                                         /\ UNCHANGED response
                              /\ log' = log
                   /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                   timers, timeoutRead, networkWrite, 
                                   networkWrite0, networkWrite1, valuesRead, 
                                   appliedWrite, appliedWrite0, networkWrite2, 
                                   appliedWrite1, networkWrite3, networkRead, 
                                   iAmTheLeaderWrite0, ifResult, appliedWrite2, 
                                   appliedWrite3, iAmTheLeaderWrite7, 
                                   networkWrite8, appliedWrite5, termWrite6, 
                                   networkWrite9, appliedWrite6, 
                                   iAmTheLeaderWrite8, termWrite7, 
                                   iAmTheLeaderRead, timerRead, termRead, 
                                   networkWrite10, networkWrite11, 
                                   networkWrite12, networkWrite13, 
                                   networkWrite14, streamWrite, streamWrite0, 
                                   timeoutLocal, currentTerm, votedFor, 
                                   commitIndex, lastApplied, iterator, msg, 
                                   msgs, index, cterm, next >>

AESendResponse(self) == /\ pc[self] = "AESendResponse"
                        /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                        /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], response[self])]
                        /\ IF ((msg[self]).commit) > (commitIndex[self])
                              THEN /\ IF ((msg[self]).commit) < (Len(log[self]))
                                         THEN /\ ifResult' = (msg[self]).commit
                                         ELSE /\ ifResult' = Len(log[self])
                                   /\ commitIndex' = [commitIndex EXCEPT ![self] = ifResult']
                                   /\ mailboxes' = networkWrite'
                                   /\ pc' = [pc EXCEPT ![self] = "AEApplyCommitted"]
                                   /\ UNCHANGED << appliedWrite3, appliedLocal >>
                              ELSE /\ appliedWrite3' = appliedLocal[self]
                                   /\ mailboxes' = networkWrite'
                                   /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite3']
                                   /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                   /\ UNCHANGED << ifResult, commitIndex >>
                        /\ UNCHANGED << valueStream, learnedChan, 
                                        heartbeatChan, leader, terms, timers, 
                                        timeoutRead, networkWrite0, 
                                        networkWrite1, valuesRead, 
                                        appliedWrite, appliedWrite0, 
                                        networkWrite2, appliedWrite1, 
                                        networkWrite3, networkRead, 
                                        iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                        appliedWrite2, ifResult0, 
                                        networkWrite4, termWrite, 
                                        iAmTheLeaderWrite1, termWrite0, 
                                        iAmTheLeaderWrite2, termWrite1, 
                                        iAmTheLeaderWrite3, termWrite2, 
                                        networkWrite5, iAmTheLeaderWrite4, 
                                        termWrite3, networkWrite6, 
                                        iAmTheLeaderWrite5, termWrite4, 
                                        networkWrite7, appliedWrite4, 
                                        iAmTheLeaderWrite6, termWrite5, 
                                        iAmTheLeaderWrite7, networkWrite8, 
                                        appliedWrite5, termWrite6, 
                                        networkWrite9, appliedWrite6, 
                                        iAmTheLeaderWrite8, termWrite7, 
                                        iAmTheLeaderRead, timerRead, termRead, 
                                        networkWrite10, networkWrite11, 
                                        networkWrite12, networkWrite13, 
                                        networkWrite14, streamWrite, 
                                        streamWrite0, timeoutLocal, 
                                        currentTerm, votedFor, log, state, 
                                        lastApplied, nextIndex, matchIndex, 
                                        iterator, votes, msg, response, msgs, 
                                        index, cterm, next >>

AEApplyCommitted(self) == /\ pc[self] = "AEApplyCommitted"
                          /\ IF (lastApplied[self]) < (commitIndex[self])
                                THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                                     /\ ((appliedLocal[self][self]).value) = (NULL)
                                     /\ appliedWrite' = [appliedLocal[self] EXCEPT ![self] = [value |-> (log[self][lastApplied'[self]]).val]]
                                     /\ appliedWrite2' = appliedWrite'
                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                                     /\ pc' = [pc EXCEPT ![self] = "AEApplyCommitted"]
                                ELSE /\ appliedWrite2' = appliedLocal[self]
                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                                     /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                                     /\ UNCHANGED << appliedWrite, lastApplied >>
                          /\ UNCHANGED << valueStream, learnedChan, 
                                          heartbeatChan, leader, terms, timers, 
                                          mailboxes, timeoutRead, networkWrite, 
                                          networkWrite0, networkWrite1, 
                                          valuesRead, appliedWrite0, 
                                          networkWrite2, appliedWrite1, 
                                          networkWrite3, networkRead, 
                                          iAmTheLeaderWrite, 
                                          iAmTheLeaderWrite0, ifResult, 
                                          appliedWrite3, ifResult0, 
                                          networkWrite4, termWrite, 
                                          iAmTheLeaderWrite1, termWrite0, 
                                          iAmTheLeaderWrite2, termWrite1, 
                                          iAmTheLeaderWrite3, termWrite2, 
                                          networkWrite5, iAmTheLeaderWrite4, 
                                          termWrite3, networkWrite6, 
                                          iAmTheLeaderWrite5, termWrite4, 
                                          networkWrite7, appliedWrite4, 
                                          iAmTheLeaderWrite6, termWrite5, 
                                          iAmTheLeaderWrite7, networkWrite8, 
                                          appliedWrite5, termWrite6, 
                                          networkWrite9, appliedWrite6, 
                                          iAmTheLeaderWrite8, termWrite7, 
                                          iAmTheLeaderRead, timerRead, 
                                          termRead, networkWrite10, 
                                          networkWrite11, networkWrite12, 
                                          networkWrite13, networkWrite14, 
                                          streamWrite, streamWrite0, 
                                          timeoutLocal, currentTerm, votedFor, 
                                          log, state, commitIndex, nextIndex, 
                                          matchIndex, iterator, votes, msg, 
                                          response, msgs, index, cterm, next >>

AEValid(self) == /\ pc[self] = "AEValid"
                 /\ response' = [response EXCEPT ![self] = [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> NULL, commit |-> NULL]]
                 /\ pc' = [pc EXCEPT ![self] = "AESendResponse"]
                 /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                 leader, terms, timers, mailboxes, timeoutRead, 
                                 networkWrite, networkWrite0, networkWrite1, 
                                 valuesRead, appliedWrite, appliedWrite0, 
                                 networkWrite2, appliedWrite1, networkWrite3, 
                                 networkRead, iAmTheLeaderWrite, 
                                 iAmTheLeaderWrite0, ifResult, appliedWrite2, 
                                 appliedWrite3, ifResult0, networkWrite4, 
                                 termWrite, iAmTheLeaderWrite1, termWrite0, 
                                 iAmTheLeaderWrite2, termWrite1, 
                                 iAmTheLeaderWrite3, termWrite2, networkWrite5, 
                                 iAmTheLeaderWrite4, termWrite3, networkWrite6, 
                                 iAmTheLeaderWrite5, termWrite4, networkWrite7, 
                                 appliedWrite4, iAmTheLeaderWrite6, termWrite5, 
                                 iAmTheLeaderWrite7, networkWrite8, 
                                 appliedWrite5, termWrite6, networkWrite9, 
                                 appliedWrite6, iAmTheLeaderWrite8, termWrite7, 
                                 iAmTheLeaderRead, timerRead, termRead, 
                                 networkWrite10, networkWrite11, 
                                 networkWrite12, networkWrite13, 
                                 networkWrite14, streamWrite, streamWrite0, 
                                 appliedLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg, msgs, index, cterm, next >>

RVSendResponse(self) == /\ pc[self] = "RVSendResponse"
                        /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                        /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], response[self])]
                        /\ mailboxes' = networkWrite'
                        /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                        /\ UNCHANGED << valueStream, learnedChan, 
                                        heartbeatChan, leader, terms, timers, 
                                        timeoutRead, networkWrite0, 
                                        networkWrite1, valuesRead, 
                                        appliedWrite, appliedWrite0, 
                                        networkWrite2, appliedWrite1, 
                                        networkWrite3, networkRead, 
                                        iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                        ifResult, appliedWrite2, appliedWrite3, 
                                        ifResult0, networkWrite4, termWrite, 
                                        iAmTheLeaderWrite1, termWrite0, 
                                        iAmTheLeaderWrite2, termWrite1, 
                                        iAmTheLeaderWrite3, termWrite2, 
                                        networkWrite5, iAmTheLeaderWrite4, 
                                        termWrite3, networkWrite6, 
                                        iAmTheLeaderWrite5, termWrite4, 
                                        networkWrite7, appliedWrite4, 
                                        iAmTheLeaderWrite6, termWrite5, 
                                        iAmTheLeaderWrite7, networkWrite8, 
                                        appliedWrite5, termWrite6, 
                                        networkWrite9, appliedWrite6, 
                                        iAmTheLeaderWrite8, termWrite7, 
                                        iAmTheLeaderRead, timerRead, termRead, 
                                        networkWrite10, networkWrite11, 
                                        networkWrite12, networkWrite13, 
                                        networkWrite14, streamWrite, 
                                        streamWrite0, appliedLocal, 
                                        timeoutLocal, currentTerm, votedFor, 
                                        log, state, commitIndex, lastApplied, 
                                        nextIndex, matchIndex, iterator, votes, 
                                        msg, response, msgs, index, cterm, 
                                        next >>

RVValid(self) == /\ pc[self] = "RVValid"
                 /\ response' = [response EXCEPT ![self].granted = TRUE]
                 /\ votedFor' = [votedFor EXCEPT ![self] = (msg[self]).sender]
                 /\ pc' = [pc EXCEPT ![self] = "RVSendResponse"]
                 /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                 leader, terms, timers, mailboxes, timeoutRead, 
                                 networkWrite, networkWrite0, networkWrite1, 
                                 valuesRead, appliedWrite, appliedWrite0, 
                                 networkWrite2, appliedWrite1, networkWrite3, 
                                 networkRead, iAmTheLeaderWrite, 
                                 iAmTheLeaderWrite0, ifResult, appliedWrite2, 
                                 appliedWrite3, ifResult0, networkWrite4, 
                                 termWrite, iAmTheLeaderWrite1, termWrite0, 
                                 iAmTheLeaderWrite2, termWrite1, 
                                 iAmTheLeaderWrite3, termWrite2, networkWrite5, 
                                 iAmTheLeaderWrite4, termWrite3, networkWrite6, 
                                 iAmTheLeaderWrite5, termWrite4, networkWrite7, 
                                 appliedWrite4, iAmTheLeaderWrite6, termWrite5, 
                                 iAmTheLeaderWrite7, networkWrite8, 
                                 appliedWrite5, termWrite6, networkWrite9, 
                                 appliedWrite6, iAmTheLeaderWrite8, termWrite7, 
                                 iAmTheLeaderRead, timerRead, termRead, 
                                 networkWrite10, networkWrite11, 
                                 networkWrite12, networkWrite13, 
                                 networkWrite14, streamWrite, streamWrite0, 
                                 appliedLocal, timeoutLocal, currentTerm, log, 
                                 state, commitIndex, lastApplied, nextIndex, 
                                 matchIndex, iterator, votes, msg, msgs, index, 
                                 cterm, next >>

RetryAppendEntry(self) == /\ pc[self] = "RetryAppendEntry"
                          /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                          /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), commit |-> commitIndex[self]])]
                          /\ mailboxes' = networkWrite'
                          /\ pc' = [pc EXCEPT ![self] = "ProcessMsgs"]
                          /\ UNCHANGED << valueStream, learnedChan, 
                                          heartbeatChan, leader, terms, timers, 
                                          timeoutRead, networkWrite0, 
                                          networkWrite1, valuesRead, 
                                          appliedWrite, appliedWrite0, 
                                          networkWrite2, appliedWrite1, 
                                          networkWrite3, networkRead, 
                                          iAmTheLeaderWrite, 
                                          iAmTheLeaderWrite0, ifResult, 
                                          appliedWrite2, appliedWrite3, 
                                          ifResult0, networkWrite4, termWrite, 
                                          iAmTheLeaderWrite1, termWrite0, 
                                          iAmTheLeaderWrite2, termWrite1, 
                                          iAmTheLeaderWrite3, termWrite2, 
                                          networkWrite5, iAmTheLeaderWrite4, 
                                          termWrite3, networkWrite6, 
                                          iAmTheLeaderWrite5, termWrite4, 
                                          networkWrite7, appliedWrite4, 
                                          iAmTheLeaderWrite6, termWrite5, 
                                          iAmTheLeaderWrite7, networkWrite8, 
                                          appliedWrite5, termWrite6, 
                                          networkWrite9, appliedWrite6, 
                                          iAmTheLeaderWrite8, termWrite7, 
                                          iAmTheLeaderRead, timerRead, 
                                          termRead, networkWrite10, 
                                          networkWrite11, networkWrite12, 
                                          networkWrite13, networkWrite14, 
                                          streamWrite, streamWrite0, 
                                          appliedLocal, timeoutLocal, 
                                          currentTerm, votedFor, log, state, 
                                          commitIndex, lastApplied, nextIndex, 
                                          matchIndex, iterator, votes, msg, 
                                          response, msgs, index, cterm, next >>

server(self) == NodeLoop(self) \/ TimeoutCheck(self) \/ SendReqVotes(self)
                   \/ LeaderCheck(self) \/ AdvanceIndex(self)
                   \/ ApplyCommited(self) \/ SendAppendEntries(self)
                   \/ RecvMsg(self) \/ ProcessMsgs(self) \/ GetMsg(self)
                   \/ CheckMsgTerm(self) \/ MsgSwitch(self)
                   \/ AESendResponse(self) \/ AEApplyCommitted(self)
                   \/ AEValid(self) \/ RVSendResponse(self)
                   \/ RVValid(self) \/ RetryAppendEntry(self)

HBLoop(self) == /\ pc[self] = "HBLoop"
                /\ IF TRUE
                      THEN /\ pc' = [pc EXCEPT ![self] = "CheckHeartBeat"]
                           /\ UNCHANGED << mailboxes, networkWrite14 >>
                      ELSE /\ networkWrite14' = mailboxes
                           /\ mailboxes' = networkWrite14'
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << valueStream, learnedChan, heartbeatChan, 
                                leader, terms, timers, timeoutRead, 
                                networkWrite, networkWrite0, networkWrite1, 
                                valuesRead, appliedWrite, appliedWrite0, 
                                networkWrite2, appliedWrite1, networkWrite3, 
                                networkRead, iAmTheLeaderWrite, 
                                iAmTheLeaderWrite0, ifResult, appliedWrite2, 
                                appliedWrite3, ifResult0, networkWrite4, 
                                termWrite, iAmTheLeaderWrite1, termWrite0, 
                                iAmTheLeaderWrite2, termWrite1, 
                                iAmTheLeaderWrite3, termWrite2, networkWrite5, 
                                iAmTheLeaderWrite4, termWrite3, networkWrite6, 
                                iAmTheLeaderWrite5, termWrite4, networkWrite7, 
                                appliedWrite4, iAmTheLeaderWrite6, termWrite5, 
                                iAmTheLeaderWrite7, networkWrite8, 
                                appliedWrite5, termWrite6, networkWrite9, 
                                appliedWrite6, iAmTheLeaderWrite8, termWrite7, 
                                iAmTheLeaderRead, timerRead, termRead, 
                                networkWrite10, networkWrite11, networkWrite12, 
                                networkWrite13, streamWrite, streamWrite0, 
                                appliedLocal, timeoutLocal, currentTerm, 
                                votedFor, log, state, commitIndex, lastApplied, 
                                nextIndex, matchIndex, iterator, votes, msg, 
                                response, msgs, index, cterm, next >>

CheckHeartBeat(self) == /\ pc[self] = "CheckHeartBeat"
                        /\ iAmTheLeaderRead' = leader[(self) - (N)]
                        /\ iAmTheLeaderRead'
                        /\ pc' = [pc EXCEPT ![self] = "SendHeartBeatLoop"]
                        /\ UNCHANGED << valueStream, learnedChan, 
                                        heartbeatChan, leader, terms, timers, 
                                        mailboxes, timeoutRead, networkWrite, 
                                        networkWrite0, networkWrite1, 
                                        valuesRead, appliedWrite, 
                                        appliedWrite0, networkWrite2, 
                                        appliedWrite1, networkWrite3, 
                                        networkRead, iAmTheLeaderWrite, 
                                        iAmTheLeaderWrite0, ifResult, 
                                        appliedWrite2, appliedWrite3, 
                                        ifResult0, networkWrite4, termWrite, 
                                        iAmTheLeaderWrite1, termWrite0, 
                                        iAmTheLeaderWrite2, termWrite1, 
                                        iAmTheLeaderWrite3, termWrite2, 
                                        networkWrite5, iAmTheLeaderWrite4, 
                                        termWrite3, networkWrite6, 
                                        iAmTheLeaderWrite5, termWrite4, 
                                        networkWrite7, appliedWrite4, 
                                        iAmTheLeaderWrite6, termWrite5, 
                                        iAmTheLeaderWrite7, networkWrite8, 
                                        appliedWrite5, termWrite6, 
                                        networkWrite9, appliedWrite6, 
                                        iAmTheLeaderWrite8, termWrite7, 
                                        timerRead, termRead, networkWrite10, 
                                        networkWrite11, networkWrite12, 
                                        networkWrite13, networkWrite14, 
                                        streamWrite, streamWrite0, 
                                        appliedLocal, timeoutLocal, 
                                        currentTerm, votedFor, log, state, 
                                        commitIndex, lastApplied, nextIndex, 
                                        matchIndex, iterator, votes, msg, 
                                        response, msgs, index, cterm, next >>

SendHeartBeatLoop(self) == /\ pc[self] = "SendHeartBeatLoop"
                           /\ iAmTheLeaderRead' = leader[(self) - (N)]
                           /\ IF iAmTheLeaderRead'
                                 THEN /\ timerRead' = TRUE
                                      /\ IF timerRead'
                                            THEN /\ index' = [index EXCEPT ![self] = 1]
                                                 /\ termRead' = terms[(self) - (N)]
                                                 /\ cterm' = [cterm EXCEPT ![self] = termRead']
                                                 /\ pc' = [pc EXCEPT ![self] = "SendHeartBeats"]
                                                 /\ UNCHANGED << mailboxes, 
                                                                 networkWrite12, 
                                                                 networkWrite13 >>
                                            ELSE /\ networkWrite12' = mailboxes
                                                 /\ networkWrite13' = networkWrite12'
                                                 /\ mailboxes' = networkWrite13'
                                                 /\ pc' = [pc EXCEPT ![self] = "SendHeartBeatLoop"]
                                                 /\ UNCHANGED << termRead, 
                                                                 index, cterm >>
                                 ELSE /\ networkWrite13' = mailboxes
                                      /\ mailboxes' = networkWrite13'
                                      /\ pc' = [pc EXCEPT ![self] = "HBLoop"]
                                      /\ UNCHANGED << timerRead, termRead, 
                                                      networkWrite12, index, 
                                                      cterm >>
                           /\ UNCHANGED << valueStream, learnedChan, 
                                           heartbeatChan, leader, terms, 
                                           timers, timeoutRead, networkWrite, 
                                           networkWrite0, networkWrite1, 
                                           valuesRead, appliedWrite, 
                                           appliedWrite0, networkWrite2, 
                                           appliedWrite1, networkWrite3, 
                                           networkRead, iAmTheLeaderWrite, 
                                           iAmTheLeaderWrite0, ifResult, 
                                           appliedWrite2, appliedWrite3, 
                                           ifResult0, networkWrite4, termWrite, 
                                           iAmTheLeaderWrite1, termWrite0, 
                                           iAmTheLeaderWrite2, termWrite1, 
                                           iAmTheLeaderWrite3, termWrite2, 
                                           networkWrite5, iAmTheLeaderWrite4, 
                                           termWrite3, networkWrite6, 
                                           iAmTheLeaderWrite5, termWrite4, 
                                           networkWrite7, appliedWrite4, 
                                           iAmTheLeaderWrite6, termWrite5, 
                                           iAmTheLeaderWrite7, networkWrite8, 
                                           appliedWrite5, termWrite6, 
                                           networkWrite9, appliedWrite6, 
                                           iAmTheLeaderWrite8, termWrite7, 
                                           networkWrite10, networkWrite11, 
                                           networkWrite14, streamWrite, 
                                           streamWrite0, appliedLocal, 
                                           timeoutLocal, currentTerm, votedFor, 
                                           log, state, commitIndex, 
                                           lastApplied, nextIndex, matchIndex, 
                                           iterator, votes, msg, response, 
                                           msgs, next >>

SendHeartBeats(self) == /\ pc[self] = "SendHeartBeats"
                        /\ IF (index[self]) <= (Cardinality(Servers))
                              THEN /\ (Len(mailboxes[index[self]])) < (BUFFER_SIZE)
                                   /\ networkWrite10' = [mailboxes EXCEPT ![index[self]] = Append(mailboxes[index[self]], [sender |-> (self) - (N), type |-> AppendEntries, term |-> cterm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> NULL, prevTerm |-> 0, commit |-> NULL])]
                                   /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                                   /\ networkWrite11' = networkWrite10'
                                   /\ mailboxes' = networkWrite11'
                                   /\ pc' = [pc EXCEPT ![self] = "SendHeartBeats"]
                              ELSE /\ networkWrite11' = mailboxes
                                   /\ mailboxes' = networkWrite11'
                                   /\ pc' = [pc EXCEPT ![self] = "SendHeartBeatLoop"]
                                   /\ UNCHANGED << networkWrite10, index >>
                        /\ UNCHANGED << valueStream, learnedChan, 
                                        heartbeatChan, leader, terms, timers, 
                                        timeoutRead, networkWrite, 
                                        networkWrite0, networkWrite1, 
                                        valuesRead, appliedWrite, 
                                        appliedWrite0, networkWrite2, 
                                        appliedWrite1, networkWrite3, 
                                        networkRead, iAmTheLeaderWrite, 
                                        iAmTheLeaderWrite0, ifResult, 
                                        appliedWrite2, appliedWrite3, 
                                        ifResult0, networkWrite4, termWrite, 
                                        iAmTheLeaderWrite1, termWrite0, 
                                        iAmTheLeaderWrite2, termWrite1, 
                                        iAmTheLeaderWrite3, termWrite2, 
                                        networkWrite5, iAmTheLeaderWrite4, 
                                        termWrite3, networkWrite6, 
                                        iAmTheLeaderWrite5, termWrite4, 
                                        networkWrite7, appliedWrite4, 
                                        iAmTheLeaderWrite6, termWrite5, 
                                        iAmTheLeaderWrite7, networkWrite8, 
                                        appliedWrite5, termWrite6, 
                                        networkWrite9, appliedWrite6, 
                                        iAmTheLeaderWrite8, termWrite7, 
                                        iAmTheLeaderRead, timerRead, termRead, 
                                        networkWrite12, networkWrite13, 
                                        networkWrite14, streamWrite, 
                                        streamWrite0, appliedLocal, 
                                        timeoutLocal, currentTerm, votedFor, 
                                        log, state, commitIndex, lastApplied, 
                                        nextIndex, matchIndex, iterator, votes, 
                                        msg, response, msgs, cterm, next >>

heartbeat(self) == HBLoop(self) \/ CheckHeartBeat(self)
                      \/ SendHeartBeatLoop(self) \/ SendHeartBeats(self)

ClientLoop(self) == /\ pc[self] = "ClientLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "WriteValue"]
                               /\ UNCHANGED << valueStream, streamWrite0 >>
                          ELSE /\ streamWrite0' = valueStream
                               /\ valueStream' = streamWrite0'
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << learnedChan, heartbeatChan, leader, terms, 
                                    timers, mailboxes, timeoutRead, 
                                    networkWrite, networkWrite0, networkWrite1, 
                                    valuesRead, appliedWrite, appliedWrite0, 
                                    networkWrite2, appliedWrite1, 
                                    networkWrite3, networkRead, 
                                    iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                    ifResult, appliedWrite2, appliedWrite3, 
                                    ifResult0, networkWrite4, termWrite, 
                                    iAmTheLeaderWrite1, termWrite0, 
                                    iAmTheLeaderWrite2, termWrite1, 
                                    iAmTheLeaderWrite3, termWrite2, 
                                    networkWrite5, iAmTheLeaderWrite4, 
                                    termWrite3, networkWrite6, 
                                    iAmTheLeaderWrite5, termWrite4, 
                                    networkWrite7, appliedWrite4, 
                                    iAmTheLeaderWrite6, termWrite5, 
                                    iAmTheLeaderWrite7, networkWrite8, 
                                    appliedWrite5, termWrite6, networkWrite9, 
                                    appliedWrite6, iAmTheLeaderWrite8, 
                                    termWrite7, iAmTheLeaderRead, timerRead, 
                                    termRead, networkWrite10, networkWrite11, 
                                    networkWrite12, networkWrite13, 
                                    networkWrite14, streamWrite, appliedLocal, 
                                    timeoutLocal, currentTerm, votedFor, log, 
                                    state, commitIndex, lastApplied, nextIndex, 
                                    matchIndex, iterator, votes, msg, response, 
                                    msgs, index, cterm, next >>

WriteValue(self) == /\ pc[self] = "WriteValue"
                    /\ ((valueStream[(self) - ((2) * (N))]).value) = (NULL)
                    /\ streamWrite' = [valueStream EXCEPT ![(self) - ((2) * (N))] = [value |-> next[self]]]
                    /\ next' = [next EXCEPT ![self] = (next[self]) + (1)]
                    /\ valueStream' = streamWrite'
                    /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                    /\ UNCHANGED << learnedChan, heartbeatChan, leader, terms, 
                                    timers, mailboxes, timeoutRead, 
                                    networkWrite, networkWrite0, networkWrite1, 
                                    valuesRead, appliedWrite, appliedWrite0, 
                                    networkWrite2, appliedWrite1, 
                                    networkWrite3, networkRead, 
                                    iAmTheLeaderWrite, iAmTheLeaderWrite0, 
                                    ifResult, appliedWrite2, appliedWrite3, 
                                    ifResult0, networkWrite4, termWrite, 
                                    iAmTheLeaderWrite1, termWrite0, 
                                    iAmTheLeaderWrite2, termWrite1, 
                                    iAmTheLeaderWrite3, termWrite2, 
                                    networkWrite5, iAmTheLeaderWrite4, 
                                    termWrite3, networkWrite6, 
                                    iAmTheLeaderWrite5, termWrite4, 
                                    networkWrite7, appliedWrite4, 
                                    iAmTheLeaderWrite6, termWrite5, 
                                    iAmTheLeaderWrite7, networkWrite8, 
                                    appliedWrite5, termWrite6, networkWrite9, 
                                    appliedWrite6, iAmTheLeaderWrite8, 
                                    termWrite7, iAmTheLeaderRead, timerRead, 
                                    termRead, networkWrite10, networkWrite11, 
                                    networkWrite12, networkWrite13, 
                                    networkWrite14, streamWrite0, appliedLocal, 
                                    timeoutLocal, currentTerm, votedFor, log, 
                                    state, commitIndex, lastApplied, nextIndex, 
                                    matchIndex, iterator, votes, msg, response, 
                                    msgs, index, cterm >>

client(self) == ClientLoop(self) \/ WriteValue(self)

Next == (\E self \in Servers: server(self))
           \/ (\E self \in Heartbeats: heartbeat(self))
           \/ (\E self \in Clients: client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))
        /\ \A self \in Heartbeats : WF_vars(heartbeat(self))
        /\ \A self \in Clients : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Properties (from figure 3 on pg 6)
(*
- Election Safety: at most one leader can be elected in a given term.
- Leader Append-Only: a leader never overwrites or deletes entries in its log; it only appends new entries.
- Log Matching: if two logs contain an entry with the same index and term, then the logs are identical in all entries up through the given index.
- Leader Completeness: if a log entry is committed in a given term, then that entry will be present in the logs of the leaders for all higher-numbered terms.
- State Machine Safety: if a server has applied a log entry at a given index to its state machine, no other server will ever apply a different log entry for the same index.
*)
                                
ElectionSafety == \A i,j \in Servers :
                   (currentTerm[i] = currentTerm[j] /\ i # j) => state[i] # Leader \/ state[j] # Leader

\* Handled by assertion in code whenever log entries are being overwritten/deleted
LeaderAppendOnly == TRUE

LogMatching == \A i,j \in Servers :
                \A k \in 1..((IF Len(log[i]) < Len(log[j]) THEN Len(log[i]) ELSE Len(log[j]))-1):
                  log[i][k] = log[j][k] => \A l \in 1..k : log[i][l] = log[j][l]

LeaderCompleteness == \A i,j \in Servers:
                       state[j] = Leader => 
                        (Len(log[j]) >= commitIndex[i]
                        /\ \A k \in 1..commitIndex[i]: (log[j][k] = log[i][k]) \/ currentTerm[j] <= log[i][k].term)

StateMachineSafety == \A i,j \in Servers :
                            \A k \in 1..(IF lastApplied[i] < lastApplied[j] THEN lastApplied[i] ELSE lastApplied[j]):
                                appliedLocal[i][k] = appliedLocal[j][k]

\* Other properties (for sanity checking)
\*AppliedCorrect == \A n \in Servers, s \in 1..Slots : learnedChan[n][s].value # NULL

EventuallyLearned == \E s \in Servers : <>(Len(log[s])>0)

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
