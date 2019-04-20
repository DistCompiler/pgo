/--------------------------------- MODULE raft ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Terms
CONSTANTS Slots
CONSTANTS N
CONSTANTS BUFFER_SIZE
CONSTANTS Follower
CONSTANTS Candidate
CONSTANTS Leader
ASSUME Follower # Candidate /\ Candidate # Leader /\ Follower # Leader

\* A reserved value.
CONSTANTS Nil

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
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log,index) == (IF index > 0 /\ Len(log) >= index /\ Len(log) > 0 THEN log[index].term ELSE 0)
    }
    
    \* Invokes a RequestVote RPC on every Node
    macro SendRequestVotes(network, cterm, candidateId, lastLogIndex, lastLogTerm, idx) {
        while (idx <= Cardinality(Servers)) {
            \* granted and entries are unused, but Nil wouldn't type check
            network[idx] := [sender |-> candidateId, type |-> RequestVote, term |-> cterm, granted |-> FALSE, entries |-> <<>>,
                             prevIndex |-> lastLogIndex, prevTerm |-> lastLogTerm, commit |-> Nil];

            idx := idx + 1;
        };
    }
    
    \* Invokes an AppendEntries RPC on every Node (can serve to make progress or just as a heartbeat from the leader)
    macro SendAppendEntries(network, cterm, candidateId, nextIndex, matchIndex, log, leaderCommit, idx) {
        while (idx <= Cardinality(Servers)) {
            \* granted is unused, but Nil wouldn't type check
            network[idx] := [sender |-> candidateId, type |-> AppendEntries, term |-> cterm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)),
                             prevIndex |-> nextIndex[idx]-1, prevTerm |-> Term(log, nextIndex[idx]-1), commit |-> leaderCommit];
            
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
            either { yield Append($variable, $value); } or { yield <<$value>> \o $variable; };
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
    
    \* Maintains a simple log (used to abstract out the state machine from the spec)
    mapping macro Log {
        read {
            assert(FALSE);
        }
  
        write {
            yield $variable \union {$value};
        }
    }
    
    \* Non-deterministic timeout (abstracted out of the implementation so proper timeouts can be implemented)
    mapping macro Timeout {
        read {
            either { yield FALSE; } or { yield TRUE; };
        }
  
        write { assert(FALSE); }
    }
    
    \* Reads from the list of input values
    mapping macro Input {
        read {
            with (msg = Head($variable)) {
                $variable := Tail($variable);
                yield msg;
            };
        }
        
        write { assert(FALSE); }
    }
    
    archetype Node(ref network, ref applied, values, timeout)
    \* Every variable should be name correspondingly with those described on page 5 of the Ongaro paper
    variable currentTerm = 0,
             votedFor = Nil,
             log = <<>>,
             state = Follower,
             commitIndex = 0,
             lastApplied = 0,
             nextIndex,
             matchIndex,
             iterator,
             votes = [t \in 0..Terms |-> {}],
             msg,
             msgs; {
MainLoop:while (TRUE) {
TimeoutCheck: if (state # Leader /\ timeout) { \* Election timeout, become candidate
            state := Candidate;
            \* Increment term
            currentTerm := currentTerm + 1;
            \* Vote for self
            votes[currentTerm] := {self};
            votedFor := self;
            iterator := 1;
SendReqVotes:   SendRequestVotes(network, currentTerm, self, Len(log), Term(log, Len(log)), iterator);
        };

LeaderCheck: if (state = Leader) { \* I am the leader for the currentTerm
            \* Make progress (append to the log)
            log := Append(log, [val |-> values, term |-> currentTerm]);
            matchIndex[self] := Len(log);
            nextIndex[self] := Len(log)+1;
            \* Can we commit more entries?
AdvanceIndex: while (Cardinality({i \in Servers: matchIndex[i] > commitIndex})*2 > Cardinality(Servers) /\ Term(log, commitIndex+1) = currentTerm) {
                commitIndex := commitIndex + 1;
            };
            \* Apply newly commited values
ApplyCommited: while(lastApplied < commitIndex) {
                lastApplied := lastApplied + 1;
                applied[lastApplied] := log[lastApplied];
            };
            \* Make AppendEntries RPC calls to every other node (as a heartbeat and to notify them of new entries)
            iterator := 1;
SendAppendEntries: SendAppendEntries(network, currentTerm, self, nextIndex, matchIndex, log, commitIndex, iterator);
        };
      
        \* Handle messages (TODO: it would be preferable performance-wise to handle every outstanding message)
RecvMsg: msgs := network[self];

W1:     while (Len(msgs) > 0) {
W2:         msg := Head(msgs);
            msgs := Tail(msgs);
CheckMsgTerm: if (msg.term > currentTerm) { \* If hearing of a later term, someone else must be the leader for that term
                state := Follower;
                currentTerm := msg.term;
            };
        
        \* Implements RPC request and response logic in figure 5
MsgSwitch: if (msg.type = AppendEntries) {
            if (msg.term < currentTerm) { \* Reject stale request
AEStale:        network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif ((msg.prevIndex > 0 /\ Len(log) < msg.prevIndex) \/ Term(log, msg.prevIndex) # msg.prevTerm) {
                \* Following entries don't have matching terms
                assert(state # Leader);
                \* Delete entries that don't match
                log := SubSeq(log,1,msg.prevIndex-1);
AENotMatching:  network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif (Len(log) = msg.prevIndex) {
                \* Append new entries
                log := log \o msg.entries;
AEValid:        network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> msg.prevIndex + Len(msg.entries), prevTerm |-> Nil, commit |-> Nil];
            };

AEUpdateCommited: if (msg.commit > commitIndex) { \* Maybe we can commit more entries
                commitIndex := IF msg.commit < Len(log) THEN msg.commit ELSE Len(log);
AEApplyCommitted: while(lastApplied < commitIndex) {
                    lastApplied := lastApplied + 1;
                    applied[lastApplied] := log[lastApplied];
                };
            };
        } elseif (msg.type = RequestVote) { 
            if (msg.term < currentTerm) { \* Reject stale requests
RVStale:        network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif ((votedFor = Nil \/ votedFor = msg.sender)
                     /\ (msg.prevTerm > Term(log, Len(log))
                         \/ (msg.prevTerm = Term(log, Len(log)) /\ msg.prevIndex >= Len(log)))) { \* Candidate's log is at least as up-to-date as ours, and we haven't voted for someone else
RVValid:        network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
                votedFor := msg.sender;
                currentTerm := msg.term;
            } else { \* The candidate's log either isn't as up-to-date as ours, or we already voted for someone else
RVInvalid:      network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            }
        } elseif (msg.type = AppendEntriesResponse /\ msg.term = currentTerm /\ state = Leader) {
            if (msg.granted) { \* They successfully added all entries! Update index we have recorded for them
                nextIndex[msg.sender] := msg.prevIndex + 1;
                matchIndex[msg.sender] := msg.prevIndex;
            } else {
                \* The append was rejected, try again with the previous index
                nextIndex[msg.sender] := IF nextIndex[msg.sender] - 1 > 1 THEN nextIndex[msg.sender] - 1 ELSE 1;
RetryAppendEntry: network[msg.sender] := [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[msg.sender], Len(log)),
                                        prevIndex |-> nextIndex[msg.sender]-1, prevTerm |-> Term(log, nextIndex[msg.sender]-1), commit |-> commitIndex];
            };
        } elseif (msg.type = RequestVoteResponse /\ msg.term = currentTerm /\ state = Candidate) {
            if (msg.granted) { \* This server has received an additional vote
                votes[msg.term] := votes[msg.term] \union {msg.sender};
                if (Cardinality(votes[msg.term])*2 > Cardinality(Servers)) {
                    \* Voters form a quorum!
                    state := Leader;
                    \* Re-initialize volatile state
                    matchIndex := [s3 \in Servers |-> 0];
                    nextIndex := [s4 \in Servers |-> 1];
                    \* Techniquely should send initial empty AppendEntries as a heartbeat, but this is unnecessary for model-checking
                };
            };
        };
      };
      };
    }

    variables
        mailboxes = [id \in Servers |-> <<>>];

    fair process (server \in Servers) == instance Node(ref mailboxes, [s \in 0..Slots |-> {}], <<1,2,3,4,5>>, TRUE)
        mapping mailboxes[_] via FIFOQueues
        mapping @2[_] via Log
        mapping @3 via Input
        mapping @4 via Timeout;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm Raft {
    variables mailboxes = [id \in Servers |-> <<>>], timeoutRead, networkWrite, networkWrite0, networkWrite1, networkWrite2, valuesRead, valuesWrite, appliedWrite, appliedWrite0, networkWrite3, networkWrite4, valuesWrite0, appliedWrite1, networkWrite5, networkRead, networkWrite6, networkWrite7, networkWrite8, networkWrite9, networkWrite10, networkWrite11, ifResult, appliedWrite2, appliedWrite3, networkWrite12, networkWrite13, networkWrite14, networkWrite15, networkWrite16, ifResult0, networkWrite17, networkWrite18, networkWrite19, networkWrite20, networkWrite21, appliedWrite4, networkWrite22, appliedWrite5, networkWrite23, valuesWrite1, appliedWrite6;
    define {
        Servers == (1) .. (N)
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0
    }
    fair process (server \in Servers)
    variables appliedLocal = [s \in (0) .. (Slots) |-> {}], valuesLocal = <<1, 2, 3, 4, 5>>, timeoutLocal = TRUE, currentTerm = 0, votedFor = Nil, log = <<>>, state = Follower, commitIndex = 0, lastApplied = 0, nextIndex, matchIndex, iterator, votes = [t \in (0) .. (Terms) |-> {}], msg, msgs;
    {
        MainLoop:
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
                                either {
                                    networkWrite := [mailboxes EXCEPT ![iterator] = Append(mailboxes[iterator], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log)), commit |-> Nil])];
                                    networkWrite0 := networkWrite;
                                } or {
                                    networkWrite := [mailboxes EXCEPT ![iterator] = (<<[sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log)), commit |-> Nil]>>) \o (mailboxes[iterator])];
                                    networkWrite0 := networkWrite;
                                };
                                iterator := (iterator) + (1);
                                networkWrite1 := networkWrite0;
                                mailboxes := networkWrite1;
                                goto SendReqVotes;
                            } else {
                                networkWrite1 := mailboxes;
                                mailboxes := networkWrite1;
                            };
                    
                    } else {
                        networkWrite2 := mailboxes;
                        mailboxes := networkWrite2;
                    };
                
                LeaderCheck:
                    if ((state) = (Leader)) {
                        with (msg0 = Head(valuesLocal)) {
                            valuesWrite := Tail(valuesLocal);
                            valuesRead := msg0;
                        };
                        log := Append(log, [val |-> valuesRead, term |-> currentTerm]);
                        matchIndex[self] := Len(log);
                        nextIndex[self] := (Len(log)) + (1);
                        valuesLocal := valuesWrite;
                        AdvanceIndex:
                            if ((((Cardinality({i \in Servers : (matchIndex[i]) > (commitIndex)})) * (2)) > (Cardinality(Servers))) /\ ((Term(log, (commitIndex) + (1))) = (currentTerm))) {
                                commitIndex := (commitIndex) + (1);
                                goto AdvanceIndex;
                            };
                        
                        ApplyCommited:
                            if ((lastApplied) < (commitIndex)) {
                                lastApplied := (lastApplied) + (1);
                                appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
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
                                either {
                                    networkWrite := [mailboxes EXCEPT ![iterator] = Append(mailboxes[iterator], [sender |-> self, type |-> AppendEntries, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[iterator], Len(log)), prevIndex |-> (nextIndex[iterator]) - (1), prevTerm |-> Term(log, (nextIndex[iterator]) - (1)), commit |-> commitIndex])];
                                    networkWrite3 := networkWrite;
                                } or {
                                    networkWrite := [mailboxes EXCEPT ![iterator] = (<<[sender |-> self, type |-> AppendEntries, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[iterator], Len(log)), prevIndex |-> (nextIndex[iterator]) - (1), prevTerm |-> Term(log, (nextIndex[iterator]) - (1)), commit |-> commitIndex]>>) \o (mailboxes[iterator])];
                                    networkWrite3 := networkWrite;
                                };
                                iterator := (iterator) + (1);
                                networkWrite4 := networkWrite3;
                                mailboxes := networkWrite4;
                                goto SendAppendEntries;
                            } else {
                                networkWrite4 := mailboxes;
                                mailboxes := networkWrite4;
                            };
                    
                    } else {
                        valuesWrite0 := valuesLocal;
                        appliedWrite1 := appliedLocal;
                        networkWrite5 := mailboxes;
                        mailboxes := networkWrite5;
                        appliedLocal := appliedWrite1;
                        valuesLocal := valuesWrite0;
                    };
                
                RecvMsg:
                    with (msgs0 = mailboxes[self]) {
                        networkWrite := [mailboxes EXCEPT ![self] = <<>>];
                        networkRead := msgs0;
                    };
                    msgs := networkRead;
                    mailboxes := networkWrite;
                
                W1:
                    if ((Len(msgs)) > (0)) {
                        W2:
                            msg := Head(msgs);
                            msgs := Tail(msgs);
                        
                        CheckMsgTerm:
                            if (((msg).term) > (currentTerm)) {
                                state := Follower;
                                currentTerm := (msg).term;
                            };
                        
                        MsgSwitch:
                            if (((msg).type) = (AppendEntries)) {
                                if (((msg).term) < (currentTerm)) {
                                    AEStale:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        either {
                                            networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                            networkWrite6 := networkWrite;
                                            mailboxes := networkWrite6;
                                        } or {
                                            networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                            networkWrite6 := networkWrite;
                                            mailboxes := networkWrite6;
                                        };
                                
                                } else {
                                    if (((((msg).prevIndex) > (0)) /\ ((Len(log)) < ((msg).prevIndex))) \/ ((Term(log, (msg).prevIndex)) # ((msg).prevTerm))) {
                                        assert (state) # (Leader);
                                        log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                                        AENotMatching:
                                            await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                            either {
                                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                                networkWrite7 := networkWrite;
                                                mailboxes := networkWrite7;
                                            } or {
                                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                                networkWrite7 := networkWrite;
                                                mailboxes := networkWrite7;
                                            };
                                    
                                    } else {
                                        if ((Len(log)) = ((msg).prevIndex)) {
                                            log := (log) \o ((msg).entries);
                                            AEValid:
                                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                                either {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg).prevIndex) + (Len((msg).entries)), prevTerm |-> Nil, commit |-> Nil])];
                                                    networkWrite8 := networkWrite;
                                                    mailboxes := networkWrite8;
                                                } or {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg).prevIndex) + (Len((msg).entries)), prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                                    networkWrite8 := networkWrite;
                                                    mailboxes := networkWrite8;
                                                };
                                        
                                        } else {
                                            networkWrite9 := mailboxes;
                                            networkWrite10 := networkWrite9;
                                            networkWrite11 := networkWrite10;
                                            mailboxes := networkWrite11;
                                        };
                                    };
                                };
                                AEUpdateCommited:
                                    if (((msg).commit) > (commitIndex)) {
                                        if (((msg).commit) < (Len(log))) {
                                            ifResult := (msg).commit;
                                        } else {
                                            ifResult := Len(log);
                                        };
                                        commitIndex := ifResult;
                                        AEApplyCommitted:
                                            if ((lastApplied) < (commitIndex)) {
                                                lastApplied := (lastApplied) + (1);
                                                appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
                                                appliedWrite2 := appliedWrite;
                                                appliedLocal := appliedWrite2;
                                                goto AEApplyCommitted;
                                            } else {
                                                appliedWrite2 := appliedLocal;
                                                appliedLocal := appliedWrite2;
                                                goto W1;
                                            };
                                    
                                    } else {
                                        appliedWrite3 := appliedLocal;
                                        appliedLocal := appliedWrite3;
                                        goto W1;
                                    };
                            
                            } else {
                                if (((msg).type) = (RequestVote)) {
                                    if (((msg).term) < (currentTerm)) {
                                        RVStale:
                                            await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                            either {
                                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                                networkWrite12 := networkWrite;
                                            } or {
                                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                                networkWrite12 := networkWrite;
                                            };
                                            mailboxes := networkWrite12;
                                            goto W1;
                                    
                                    } else {
                                        if ((((votedFor) = (Nil)) \/ ((votedFor) = ((msg).sender))) /\ ((((msg).prevTerm) > (Term(log, Len(log)))) \/ ((((msg).prevTerm) = (Term(log, Len(log)))) /\ (((msg).prevIndex) >= (Len(log)))))) {
                                            RVValid:
                                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                                either {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                                    networkWrite13 := networkWrite;
                                                } or {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                                    networkWrite13 := networkWrite;
                                                };
                                                votedFor := (msg).sender;
                                                currentTerm := (msg).term;
                                                mailboxes := networkWrite13;
                                                goto W1;
                                        
                                        } else {
                                            RVInvalid:
                                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                                either {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                                    networkWrite14 := networkWrite;
                                                } or {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg).sender])];
                                                    networkWrite14 := networkWrite;
                                                };
                                                mailboxes := networkWrite14;
                                                goto W1;
                                        
                                        };
                                    };
                                } else {
                                    if (((((msg).type) = (AppendEntriesResponse)) /\ (((msg).term) = (currentTerm))) /\ ((state) = (Leader))) {
                                        if ((msg).granted) {
                                            nextIndex[(msg).sender] := ((msg).prevIndex) + (1);
                                            matchIndex[(msg).sender] := (msg).prevIndex;
                                            networkWrite18 := mailboxes;
                                            networkWrite19 := networkWrite18;
                                            networkWrite20 := networkWrite19;
                                            networkWrite21 := networkWrite20;
                                            appliedWrite4 := appliedLocal;
                                            mailboxes := networkWrite21;
                                            appliedLocal := appliedWrite4;
                                            goto W1;
                                        } else {
                                            if (((nextIndex[(msg).sender]) - (1)) > (1)) {
                                                ifResult0 := (nextIndex[(msg).sender]) - (1);
                                            } else {
                                                ifResult0 := 1;
                                            };
                                            nextIndex[(msg).sender] := ifResult0;
                                            RetryAppendEntry:
                                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                                either {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[(msg).sender], Len(log)), prevIndex |-> (nextIndex[(msg).sender]) - (1), prevTerm |-> Term(log, (nextIndex[(msg).sender]) - (1)), commit |-> commitIndex])];
                                                    networkWrite17 := networkWrite;
                                                } or {
                                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = (<<[sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[(msg).sender], Len(log)), prevIndex |-> (nextIndex[(msg).sender]) - (1), prevTerm |-> Term(log, (nextIndex[(msg).sender]) - (1)), commit |-> commitIndex]>>) \o (mailboxes[(msg).sender])];
                                                    networkWrite17 := networkWrite;
                                                };
                                                mailboxes := networkWrite17;
                                                goto W1;
                                        
                                        };
                                    } else {
                                        if (((((msg).type) = (RequestVoteResponse)) /\ (((msg).term) = (currentTerm))) /\ ((state) = (Candidate))) {
                                            if ((msg).granted) {
                                                votes[(msg).term] := (votes[(msg).term]) \union ({(msg).sender});
                                                if (((Cardinality(votes[(msg).term])) * (2)) > (Cardinality(Servers))) {
                                                    state := Leader;
                                                    matchIndex := [s3 \in Servers |-> 0];
                                                    nextIndex := [s4 \in Servers |-> 1];
                                                    networkWrite19 := mailboxes;
                                                    networkWrite20 := networkWrite19;
                                                    networkWrite21 := networkWrite20;
                                                    appliedWrite4 := appliedLocal;
                                                    mailboxes := networkWrite21;
                                                    appliedLocal := appliedWrite4;
                                                    goto W1;
                                                } else {
                                                    networkWrite19 := mailboxes;
                                                    networkWrite20 := networkWrite19;
                                                    networkWrite21 := networkWrite20;
                                                    appliedWrite4 := appliedLocal;
                                                    mailboxes := networkWrite21;
                                                    appliedLocal := appliedWrite4;
                                                    goto W1;
                                                };
                                            } else {
                                                networkWrite19 := mailboxes;
                                                networkWrite20 := networkWrite19;
                                                networkWrite21 := networkWrite20;
                                                appliedWrite4 := appliedLocal;
                                                mailboxes := networkWrite21;
                                                appliedLocal := appliedWrite4;
                                                goto W1;
                                            };
                                        } else {
                                            networkWrite19 := mailboxes;
                                            networkWrite20 := networkWrite19;
                                            networkWrite21 := networkWrite20;
                                            appliedWrite4 := appliedLocal;
                                            mailboxes := networkWrite21;
                                            appliedLocal := appliedWrite4;
                                            goto W1;
                                        };
                                    };
                                };
                            };
                    
                    } else {
                        networkWrite22 := mailboxes;
                        appliedWrite5 := appliedLocal;
                        mailboxes := networkWrite22;
                        appliedLocal := appliedWrite5;
                        goto MainLoop;
                    };
            
            } else {
                networkWrite23 := mailboxes;
                valuesWrite1 := valuesLocal;
                appliedWrite6 := appliedLocal;
                mailboxes := networkWrite23;
                appliedLocal := appliedWrite6;
                valuesLocal := valuesWrite1;
            };
    
    }
}
\* END PLUSCAL TRANSLATION

******************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
          networkWrite2, valuesRead, valuesWrite, appliedWrite, appliedWrite0, 
          networkWrite3, networkWrite4, valuesWrite0, appliedWrite1, 
          networkWrite5, networkRead, networkWrite6, networkWrite7, 
          networkWrite8, networkWrite9, networkWrite10, networkWrite11, 
          ifResult, appliedWrite2, appliedWrite3, networkWrite12, 
          networkWrite13, networkWrite14, networkWrite15, networkWrite16, 
          ifResult0, networkWrite17, networkWrite18, networkWrite19, 
          networkWrite20, networkWrite21, appliedWrite4, networkWrite22, 
          appliedWrite5, networkWrite23, valuesWrite1, appliedWrite6, pc

(* define statement *)
Servers == (1) .. (N)
RequestVote == 0
RequestVoteResponse == 1
AppendEntries == 2
AppendEntriesResponse == 3
Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0

VARIABLES appliedLocal, valuesLocal, timeoutLocal, currentTerm, votedFor, log, 
          state, commitIndex, lastApplied, nextIndex, matchIndex, iterator, 
          votes, msg, msgs

vars == << mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
           networkWrite2, valuesRead, valuesWrite, appliedWrite, 
           appliedWrite0, networkWrite3, networkWrite4, valuesWrite0, 
           appliedWrite1, networkWrite5, networkRead, networkWrite6, 
           networkWrite7, networkWrite8, networkWrite9, networkWrite10, 
           networkWrite11, ifResult, appliedWrite2, appliedWrite3, 
           networkWrite12, networkWrite13, networkWrite14, networkWrite15, 
           networkWrite16, ifResult0, networkWrite17, networkWrite18, 
           networkWrite19, networkWrite20, networkWrite21, appliedWrite4, 
           networkWrite22, appliedWrite5, networkWrite23, valuesWrite1, 
           appliedWrite6, pc, appliedLocal, valuesLocal, timeoutLocal, 
           currentTerm, votedFor, log, state, commitIndex, lastApplied, 
           nextIndex, matchIndex, iterator, votes, msg, msgs >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ mailboxes = [id \in Servers |-> <<>>]
        /\ timeoutRead = defaultInitValue
        /\ networkWrite = defaultInitValue
        /\ networkWrite0 = defaultInitValue
        /\ networkWrite1 = defaultInitValue
        /\ networkWrite2 = defaultInitValue
        /\ valuesRead = defaultInitValue
        /\ valuesWrite = defaultInitValue
        /\ appliedWrite = defaultInitValue
        /\ appliedWrite0 = defaultInitValue
        /\ networkWrite3 = defaultInitValue
        /\ networkWrite4 = defaultInitValue
        /\ valuesWrite0 = defaultInitValue
        /\ appliedWrite1 = defaultInitValue
        /\ networkWrite5 = defaultInitValue
        /\ networkRead = defaultInitValue
        /\ networkWrite6 = defaultInitValue
        /\ networkWrite7 = defaultInitValue
        /\ networkWrite8 = defaultInitValue
        /\ networkWrite9 = defaultInitValue
        /\ networkWrite10 = defaultInitValue
        /\ networkWrite11 = defaultInitValue
        /\ ifResult = defaultInitValue
        /\ appliedWrite2 = defaultInitValue
        /\ appliedWrite3 = defaultInitValue
        /\ networkWrite12 = defaultInitValue
        /\ networkWrite13 = defaultInitValue
        /\ networkWrite14 = defaultInitValue
        /\ networkWrite15 = defaultInitValue
        /\ networkWrite16 = defaultInitValue
        /\ ifResult0 = defaultInitValue
        /\ networkWrite17 = defaultInitValue
        /\ networkWrite18 = defaultInitValue
        /\ networkWrite19 = defaultInitValue
        /\ networkWrite20 = defaultInitValue
        /\ networkWrite21 = defaultInitValue
        /\ appliedWrite4 = defaultInitValue
        /\ networkWrite22 = defaultInitValue
        /\ appliedWrite5 = defaultInitValue
        /\ networkWrite23 = defaultInitValue
        /\ valuesWrite1 = defaultInitValue
        /\ appliedWrite6 = defaultInitValue
        (* Process server *)
        /\ appliedLocal = [self \in Servers |-> [s \in (0) .. (Slots) |-> {}]]
        /\ valuesLocal = [self \in Servers |-> <<1, 2, 3, 4, 5>>]
        /\ timeoutLocal = [self \in Servers |-> TRUE]
        /\ currentTerm = [self \in Servers |-> 0]
        /\ votedFor = [self \in Servers |-> Nil]
        /\ log = [self \in Servers |-> <<>>]
        /\ state = [self \in Servers |-> Follower]
        /\ commitIndex = [self \in Servers |-> 0]
        /\ lastApplied = [self \in Servers |-> 0]
        /\ nextIndex = [self \in Servers |-> defaultInitValue]
        /\ matchIndex = [self \in Servers |-> defaultInitValue]
        /\ iterator = [self \in Servers |-> defaultInitValue]
        /\ votes = [self \in Servers |-> [t \in (0) .. (Terms) |-> {}]]
        /\ msg = [self \in Servers |-> defaultInitValue]
        /\ msgs = [self \in Servers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF TRUE
                        THEN /\ pc' = [pc EXCEPT ![self] = "TimeoutCheck"]
                             /\ UNCHANGED << mailboxes, networkWrite23, 
                                             valuesWrite1, appliedWrite6, 
                                             appliedLocal, valuesLocal >>
                        ELSE /\ networkWrite23' = mailboxes
                             /\ valuesWrite1' = valuesLocal[self]
                             /\ appliedWrite6' = appliedLocal[self]
                             /\ mailboxes' = networkWrite23'
                             /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                             /\ valuesLocal' = [valuesLocal EXCEPT ![self] = valuesWrite1']
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                                  networkWrite1, networkWrite2, valuesRead, 
                                  valuesWrite, appliedWrite, appliedWrite0, 
                                  networkWrite3, networkWrite4, valuesWrite0, 
                                  appliedWrite1, networkWrite5, networkRead, 
                                  networkWrite6, networkWrite7, networkWrite8, 
                                  networkWrite9, networkWrite10, 
                                  networkWrite11, ifResult, appliedWrite2, 
                                  appliedWrite3, networkWrite12, 
                                  networkWrite13, networkWrite14, 
                                  networkWrite15, networkWrite16, ifResult0, 
                                  networkWrite17, networkWrite18, 
                                  networkWrite19, networkWrite20, 
                                  networkWrite21, appliedWrite4, 
                                  networkWrite22, appliedWrite5, timeoutLocal, 
                                  currentTerm, votedFor, log, state, 
                                  commitIndex, lastApplied, nextIndex, 
                                  matchIndex, iterator, votes, msg, msgs >>

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
                                 /\ UNCHANGED << mailboxes, networkWrite2 >>
                            ELSE /\ networkWrite2' = mailboxes
                                 /\ mailboxes' = networkWrite2'
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderCheck"]
                                 /\ UNCHANGED << currentTerm, votedFor, state, 
                                                 iterator, votes >>
                      /\ UNCHANGED << networkWrite, networkWrite0, 
                                      networkWrite1, valuesRead, valuesWrite, 
                                      appliedWrite, appliedWrite0, 
                                      networkWrite3, networkWrite4, 
                                      valuesWrite0, appliedWrite1, 
                                      networkWrite5, networkRead, 
                                      networkWrite6, networkWrite7, 
                                      networkWrite8, networkWrite9, 
                                      networkWrite10, networkWrite11, ifResult, 
                                      appliedWrite2, appliedWrite3, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, networkWrite15, 
                                      networkWrite16, ifResult0, 
                                      networkWrite17, networkWrite18, 
                                      networkWrite19, networkWrite20, 
                                      networkWrite21, appliedWrite4, 
                                      networkWrite22, appliedWrite5, 
                                      networkWrite23, valuesWrite1, 
                                      appliedWrite6, appliedLocal, valuesLocal, 
                                      timeoutLocal, log, commitIndex, 
                                      lastApplied, nextIndex, matchIndex, msg, 
                                      msgs >>

SendReqVotes(self) == /\ pc[self] = "SendReqVotes"
                      /\ IF (iterator[self]) <= (Cardinality(Servers))
                            THEN /\ (Len(mailboxes[iterator[self]])) < (BUFFER_SIZE)
                                 /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = Append(mailboxes[iterator[self]], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self])), commit |-> Nil])]
                                       /\ networkWrite0' = networkWrite'
                                    \/ /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = (<<[sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self])), commit |-> Nil]>>) \o (mailboxes[iterator[self]])]
                                       /\ networkWrite0' = networkWrite'
                                 /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                 /\ networkWrite1' = networkWrite0'
                                 /\ mailboxes' = networkWrite1'
                                 /\ pc' = [pc EXCEPT ![self] = "SendReqVotes"]
                            ELSE /\ networkWrite1' = mailboxes
                                 /\ mailboxes' = networkWrite1'
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderCheck"]
                                 /\ UNCHANGED << networkWrite, networkWrite0, 
                                                 iterator >>
                      /\ UNCHANGED << timeoutRead, networkWrite2, valuesRead, 
                                      valuesWrite, appliedWrite, appliedWrite0, 
                                      networkWrite3, networkWrite4, 
                                      valuesWrite0, appliedWrite1, 
                                      networkWrite5, networkRead, 
                                      networkWrite6, networkWrite7, 
                                      networkWrite8, networkWrite9, 
                                      networkWrite10, networkWrite11, ifResult, 
                                      appliedWrite2, appliedWrite3, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, networkWrite15, 
                                      networkWrite16, ifResult0, 
                                      networkWrite17, networkWrite18, 
                                      networkWrite19, networkWrite20, 
                                      networkWrite21, appliedWrite4, 
                                      networkWrite22, appliedWrite5, 
                                      networkWrite23, valuesWrite1, 
                                      appliedWrite6, appliedLocal, valuesLocal, 
                                      timeoutLocal, currentTerm, votedFor, log, 
                                      state, commitIndex, lastApplied, 
                                      nextIndex, matchIndex, votes, msg, msgs >>

LeaderCheck(self) == /\ pc[self] = "LeaderCheck"
                     /\ IF (state[self]) = (Leader)
                           THEN /\ LET msg0 == Head(valuesLocal[self]) IN
                                     /\ valuesWrite' = Tail(valuesLocal[self])
                                     /\ valuesRead' = msg0
                                /\ log' = [log EXCEPT ![self] = Append(log[self], [val |-> valuesRead', term |-> currentTerm[self]])]
                                /\ matchIndex' = [matchIndex EXCEPT ![self][self] = Len(log'[self])]
                                /\ nextIndex' = [nextIndex EXCEPT ![self][self] = (Len(log'[self])) + (1)]
                                /\ valuesLocal' = [valuesLocal EXCEPT ![self] = valuesWrite']
                                /\ pc' = [pc EXCEPT ![self] = "AdvanceIndex"]
                                /\ UNCHANGED << mailboxes, valuesWrite0, 
                                                appliedWrite1, networkWrite5, 
                                                appliedLocal >>
                           ELSE /\ valuesWrite0' = valuesLocal[self]
                                /\ appliedWrite1' = appliedLocal[self]
                                /\ networkWrite5' = mailboxes
                                /\ mailboxes' = networkWrite5'
                                /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite1']
                                /\ valuesLocal' = [valuesLocal EXCEPT ![self] = valuesWrite0']
                                /\ pc' = [pc EXCEPT ![self] = "RecvMsg"]
                                /\ UNCHANGED << valuesRead, valuesWrite, log, 
                                                nextIndex, matchIndex >>
                     /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                                     networkWrite1, networkWrite2, 
                                     appliedWrite, appliedWrite0, 
                                     networkWrite3, networkWrite4, networkRead, 
                                     networkWrite6, networkWrite7, 
                                     networkWrite8, networkWrite9, 
                                     networkWrite10, networkWrite11, ifResult, 
                                     appliedWrite2, appliedWrite3, 
                                     networkWrite12, networkWrite13, 
                                     networkWrite14, networkWrite15, 
                                     networkWrite16, ifResult0, networkWrite17, 
                                     networkWrite18, networkWrite19, 
                                     networkWrite20, networkWrite21, 
                                     appliedWrite4, networkWrite22, 
                                     appliedWrite5, networkWrite23, 
                                     valuesWrite1, appliedWrite6, timeoutLocal, 
                                     currentTerm, votedFor, state, commitIndex, 
                                     lastApplied, iterator, votes, msg, msgs >>

AdvanceIndex(self) == /\ pc[self] = "AdvanceIndex"
                      /\ IF (((Cardinality({i \in Servers : (matchIndex[self][i]) > (commitIndex[self])})) * (2)) > (Cardinality(Servers))) /\ ((Term(log[self], (commitIndex[self]) + (1))) = (currentTerm[self]))
                            THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (commitIndex[self]) + (1)]
                                 /\ pc' = [pc EXCEPT ![self] = "AdvanceIndex"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ApplyCommited"]
                                 /\ UNCHANGED commitIndex
                      /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                                      networkWrite0, networkWrite1, 
                                      networkWrite2, valuesRead, valuesWrite, 
                                      appliedWrite, appliedWrite0, 
                                      networkWrite3, networkWrite4, 
                                      valuesWrite0, appliedWrite1, 
                                      networkWrite5, networkRead, 
                                      networkWrite6, networkWrite7, 
                                      networkWrite8, networkWrite9, 
                                      networkWrite10, networkWrite11, ifResult, 
                                      appliedWrite2, appliedWrite3, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, networkWrite15, 
                                      networkWrite16, ifResult0, 
                                      networkWrite17, networkWrite18, 
                                      networkWrite19, networkWrite20, 
                                      networkWrite21, appliedWrite4, 
                                      networkWrite22, appliedWrite5, 
                                      networkWrite23, valuesWrite1, 
                                      appliedWrite6, appliedLocal, valuesLocal, 
                                      timeoutLocal, currentTerm, votedFor, log, 
                                      state, lastApplied, nextIndex, 
                                      matchIndex, iterator, votes, msg, msgs >>

ApplyCommited(self) == /\ pc[self] = "ApplyCommited"
                       /\ IF (lastApplied[self]) < (commitIndex[self])
                             THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                                  /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied'[self]] = (appliedLocal[self][lastApplied'[self]]) \union ({log[self][lastApplied'[self]]})]
                                  /\ appliedWrite0' = appliedWrite'
                                  /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                                  /\ pc' = [pc EXCEPT ![self] = "ApplyCommited"]
                                  /\ UNCHANGED iterator
                             ELSE /\ iterator' = [iterator EXCEPT ![self] = 1]
                                  /\ appliedWrite0' = appliedLocal[self]
                                  /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                                  /\ pc' = [pc EXCEPT ![self] = "SendAppendEntries"]
                                  /\ UNCHANGED << appliedWrite, lastApplied >>
                       /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                                       networkWrite0, networkWrite1, 
                                       networkWrite2, valuesRead, valuesWrite, 
                                       networkWrite3, networkWrite4, 
                                       valuesWrite0, appliedWrite1, 
                                       networkWrite5, networkRead, 
                                       networkWrite6, networkWrite7, 
                                       networkWrite8, networkWrite9, 
                                       networkWrite10, networkWrite11, 
                                       ifResult, appliedWrite2, appliedWrite3, 
                                       networkWrite12, networkWrite13, 
                                       networkWrite14, networkWrite15, 
                                       networkWrite16, ifResult0, 
                                       networkWrite17, networkWrite18, 
                                       networkWrite19, networkWrite20, 
                                       networkWrite21, appliedWrite4, 
                                       networkWrite22, appliedWrite5, 
                                       networkWrite23, valuesWrite1, 
                                       appliedWrite6, valuesLocal, 
                                       timeoutLocal, currentTerm, votedFor, 
                                       log, state, commitIndex, nextIndex, 
                                       matchIndex, votes, msg, msgs >>

SendAppendEntries(self) == /\ pc[self] = "SendAppendEntries"
                           /\ IF (iterator[self]) <= (Cardinality(Servers))
                                 THEN /\ (Len(mailboxes[iterator[self]])) < (BUFFER_SIZE)
                                      /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = Append(mailboxes[iterator[self]], [sender |-> self, type |-> AppendEntries, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][iterator[self]], Len(log[self])), prevIndex |-> (nextIndex[self][iterator[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][iterator[self]]) - (1)), commit |-> commitIndex[self]])]
                                            /\ networkWrite3' = networkWrite'
                                         \/ /\ networkWrite' = [mailboxes EXCEPT ![iterator[self]] = (<<[sender |-> self, type |-> AppendEntries, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][iterator[self]], Len(log[self])), prevIndex |-> (nextIndex[self][iterator[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][iterator[self]]) - (1)), commit |-> commitIndex[self]]>>) \o (mailboxes[iterator[self]])]
                                            /\ networkWrite3' = networkWrite'
                                      /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                      /\ networkWrite4' = networkWrite3'
                                      /\ mailboxes' = networkWrite4'
                                      /\ pc' = [pc EXCEPT ![self] = "SendAppendEntries"]
                                 ELSE /\ networkWrite4' = mailboxes
                                      /\ mailboxes' = networkWrite4'
                                      /\ pc' = [pc EXCEPT ![self] = "RecvMsg"]
                                      /\ UNCHANGED << networkWrite, 
                                                      networkWrite3, iterator >>
                           /\ UNCHANGED << timeoutRead, networkWrite0, 
                                           networkWrite1, networkWrite2, 
                                           valuesRead, valuesWrite, 
                                           appliedWrite, appliedWrite0, 
                                           valuesWrite0, appliedWrite1, 
                                           networkWrite5, networkRead, 
                                           networkWrite6, networkWrite7, 
                                           networkWrite8, networkWrite9, 
                                           networkWrite10, networkWrite11, 
                                           ifResult, appliedWrite2, 
                                           appliedWrite3, networkWrite12, 
                                           networkWrite13, networkWrite14, 
                                           networkWrite15, networkWrite16, 
                                           ifResult0, networkWrite17, 
                                           networkWrite18, networkWrite19, 
                                           networkWrite20, networkWrite21, 
                                           appliedWrite4, networkWrite22, 
                                           appliedWrite5, networkWrite23, 
                                           valuesWrite1, appliedWrite6, 
                                           appliedLocal, valuesLocal, 
                                           timeoutLocal, currentTerm, votedFor, 
                                           log, state, commitIndex, 
                                           lastApplied, nextIndex, matchIndex, 
                                           votes, msg, msgs >>

RecvMsg(self) == /\ pc[self] = "RecvMsg"
                 /\ LET msgs0 == mailboxes[self] IN
                      /\ networkWrite' = [mailboxes EXCEPT ![self] = <<>>]
                      /\ networkRead' = msgs0
                 /\ msgs' = [msgs EXCEPT ![self] = networkRead']
                 /\ mailboxes' = networkWrite'
                 /\ pc' = [pc EXCEPT ![self] = "W1"]
                 /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                 networkWrite2, valuesRead, valuesWrite, 
                                 appliedWrite, appliedWrite0, networkWrite3, 
                                 networkWrite4, valuesWrite0, appliedWrite1, 
                                 networkWrite5, networkWrite6, networkWrite7, 
                                 networkWrite8, networkWrite9, networkWrite10, 
                                 networkWrite11, ifResult, appliedWrite2, 
                                 appliedWrite3, networkWrite12, networkWrite13, 
                                 networkWrite14, networkWrite15, 
                                 networkWrite16, ifResult0, networkWrite17, 
                                 networkWrite18, networkWrite19, 
                                 networkWrite20, networkWrite21, appliedWrite4, 
                                 networkWrite22, appliedWrite5, networkWrite23, 
                                 valuesWrite1, appliedWrite6, appliedLocal, 
                                 valuesLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg >>

W1(self) == /\ pc[self] = "W1"
            /\ IF (Len(msgs[self])) > (0)
                  THEN /\ pc' = [pc EXCEPT ![self] = "W2"]
                       /\ UNCHANGED << mailboxes, networkWrite22, 
                                       appliedWrite5, appliedLocal >>
                  ELSE /\ networkWrite22' = mailboxes
                       /\ appliedWrite5' = appliedLocal[self]
                       /\ mailboxes' = networkWrite22'
                       /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite5']
                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
            /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                            networkWrite1, networkWrite2, valuesRead, 
                            valuesWrite, appliedWrite, appliedWrite0, 
                            networkWrite3, networkWrite4, valuesWrite0, 
                            appliedWrite1, networkWrite5, networkRead, 
                            networkWrite6, networkWrite7, networkWrite8, 
                            networkWrite9, networkWrite10, networkWrite11, 
                            ifResult, appliedWrite2, appliedWrite3, 
                            networkWrite12, networkWrite13, networkWrite14, 
                            networkWrite15, networkWrite16, ifResult0, 
                            networkWrite17, networkWrite18, networkWrite19, 
                            networkWrite20, networkWrite21, appliedWrite4, 
                            networkWrite23, valuesWrite1, appliedWrite6, 
                            valuesLocal, timeoutLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, nextIndex, 
                            matchIndex, iterator, votes, msg, msgs >>

W2(self) == /\ pc[self] = "W2"
            /\ msg' = [msg EXCEPT ![self] = Head(msgs[self])]
            /\ msgs' = [msgs EXCEPT ![self] = Tail(msgs[self])]
            /\ pc' = [pc EXCEPT ![self] = "CheckMsgTerm"]
            /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                            networkWrite0, networkWrite1, networkWrite2, 
                            valuesRead, valuesWrite, appliedWrite, 
                            appliedWrite0, networkWrite3, networkWrite4, 
                            valuesWrite0, appliedWrite1, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, networkWrite9, networkWrite10, 
                            networkWrite11, ifResult, appliedWrite2, 
                            appliedWrite3, networkWrite12, networkWrite13, 
                            networkWrite14, networkWrite15, networkWrite16, 
                            ifResult0, networkWrite17, networkWrite18, 
                            networkWrite19, networkWrite20, networkWrite21, 
                            appliedWrite4, networkWrite22, appliedWrite5, 
                            networkWrite23, valuesWrite1, appliedWrite6, 
                            appliedLocal, valuesLocal, timeoutLocal, 
                            currentTerm, votedFor, log, state, commitIndex, 
                            lastApplied, nextIndex, matchIndex, iterator, 
                            votes >>

CheckMsgTerm(self) == /\ pc[self] = "CheckMsgTerm"
                      /\ IF ((msg[self]).term) > (currentTerm[self])
                            THEN /\ state' = [state EXCEPT ![self] = Follower]
                                 /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << currentTerm, state >>
                      /\ pc' = [pc EXCEPT ![self] = "MsgSwitch"]
                      /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                                      networkWrite0, networkWrite1, 
                                      networkWrite2, valuesRead, valuesWrite, 
                                      appliedWrite, appliedWrite0, 
                                      networkWrite3, networkWrite4, 
                                      valuesWrite0, appliedWrite1, 
                                      networkWrite5, networkRead, 
                                      networkWrite6, networkWrite7, 
                                      networkWrite8, networkWrite9, 
                                      networkWrite10, networkWrite11, ifResult, 
                                      appliedWrite2, appliedWrite3, 
                                      networkWrite12, networkWrite13, 
                                      networkWrite14, networkWrite15, 
                                      networkWrite16, ifResult0, 
                                      networkWrite17, networkWrite18, 
                                      networkWrite19, networkWrite20, 
                                      networkWrite21, appliedWrite4, 
                                      networkWrite22, appliedWrite5, 
                                      networkWrite23, valuesWrite1, 
                                      appliedWrite6, appliedLocal, valuesLocal, 
                                      timeoutLocal, votedFor, log, commitIndex, 
                                      lastApplied, nextIndex, matchIndex, 
                                      iterator, votes, msg, msgs >>

MsgSwitch(self) == /\ pc[self] = "MsgSwitch"
                   /\ IF ((msg[self]).type) = (AppendEntries)
                         THEN /\ IF ((msg[self]).term) < (currentTerm[self])
                                    THEN /\ pc' = [pc EXCEPT ![self] = "AEStale"]
                                         /\ UNCHANGED << mailboxes, 
                                                         networkWrite9, 
                                                         networkWrite10, 
                                                         networkWrite11, log >>
                                    ELSE /\ IF ((((msg[self]).prevIndex) > (0)) /\ ((Len(log[self])) < ((msg[self]).prevIndex))) \/ ((Term(log[self], (msg[self]).prevIndex)) # ((msg[self]).prevTerm))
                                               THEN /\ Assert((state[self]) # (Leader), 
                                                              "Failure of assertion at line 412, column 41.")
                                                    /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg[self]).prevIndex) - (1))]
                                                    /\ pc' = [pc EXCEPT ![self] = "AENotMatching"]
                                                    /\ UNCHANGED << mailboxes, 
                                                                    networkWrite9, 
                                                                    networkWrite10, 
                                                                    networkWrite11 >>
                                               ELSE /\ IF (Len(log[self])) = ((msg[self]).prevIndex)
                                                          THEN /\ log' = [log EXCEPT ![self] = (log[self]) \o ((msg[self]).entries)]
                                                               /\ pc' = [pc EXCEPT ![self] = "AEValid"]
                                                               /\ UNCHANGED << mailboxes, 
                                                                               networkWrite9, 
                                                                               networkWrite10, 
                                                                               networkWrite11 >>
                                                          ELSE /\ networkWrite9' = mailboxes
                                                               /\ networkWrite10' = networkWrite9'
                                                               /\ networkWrite11' = networkWrite10'
                                                               /\ mailboxes' = networkWrite11'
                                                               /\ pc' = [pc EXCEPT ![self] = "AEUpdateCommited"]
                                                               /\ log' = log
                              /\ UNCHANGED << ifResult0, networkWrite18, 
                                              networkWrite19, networkWrite20, 
                                              networkWrite21, appliedWrite4, 
                                              appliedLocal, state, nextIndex, 
                                              matchIndex, votes >>
                         ELSE /\ IF ((msg[self]).type) = (RequestVote)
                                    THEN /\ IF ((msg[self]).term) < (currentTerm[self])
                                               THEN /\ pc' = [pc EXCEPT ![self] = "RVStale"]
                                               ELSE /\ IF (((votedFor[self]) = (Nil)) \/ ((votedFor[self]) = ((msg[self]).sender))) /\ ((((msg[self]).prevTerm) > (Term(log[self], Len(log[self])))) \/ ((((msg[self]).prevTerm) = (Term(log[self], Len(log[self])))) /\ (((msg[self]).prevIndex) >= (Len(log[self])))))
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "RVValid"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "RVInvalid"]
                                         /\ UNCHANGED << mailboxes, ifResult0, 
                                                         networkWrite18, 
                                                         networkWrite19, 
                                                         networkWrite20, 
                                                         networkWrite21, 
                                                         appliedWrite4, 
                                                         appliedLocal, state, 
                                                         nextIndex, matchIndex, 
                                                         votes >>
                                    ELSE /\ IF ((((msg[self]).type) = (AppendEntriesResponse)) /\ (((msg[self]).term) = (currentTerm[self]))) /\ ((state[self]) = (Leader))
                                               THEN /\ IF (msg[self]).granted
                                                          THEN /\ nextIndex' = [nextIndex EXCEPT ![self][(msg[self]).sender] = ((msg[self]).prevIndex) + (1)]
                                                               /\ matchIndex' = [matchIndex EXCEPT ![self][(msg[self]).sender] = (msg[self]).prevIndex]
                                                               /\ networkWrite18' = mailboxes
                                                               /\ networkWrite19' = networkWrite18'
                                                               /\ networkWrite20' = networkWrite19'
                                                               /\ networkWrite21' = networkWrite20'
                                                               /\ appliedWrite4' = appliedLocal[self]
                                                               /\ mailboxes' = networkWrite21'
                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                               /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                               /\ UNCHANGED ifResult0
                                                          ELSE /\ IF ((nextIndex[self][(msg[self]).sender]) - (1)) > (1)
                                                                     THEN /\ ifResult0' = (nextIndex[self][(msg[self]).sender]) - (1)
                                                                     ELSE /\ ifResult0' = 1
                                                               /\ nextIndex' = [nextIndex EXCEPT ![self][(msg[self]).sender] = ifResult0']
                                                               /\ pc' = [pc EXCEPT ![self] = "RetryAppendEntry"]
                                                               /\ UNCHANGED << mailboxes, 
                                                                               networkWrite18, 
                                                                               networkWrite19, 
                                                                               networkWrite20, 
                                                                               networkWrite21, 
                                                                               appliedWrite4, 
                                                                               appliedLocal, 
                                                                               matchIndex >>
                                                    /\ UNCHANGED << state, 
                                                                    votes >>
                                               ELSE /\ IF ((((msg[self]).type) = (RequestVoteResponse)) /\ (((msg[self]).term) = (currentTerm[self]))) /\ ((state[self]) = (Candidate))
                                                          THEN /\ IF (msg[self]).granted
                                                                     THEN /\ votes' = [votes EXCEPT ![self][(msg[self]).term] = (votes[self][(msg[self]).term]) \union ({(msg[self]).sender})]
                                                                          /\ IF ((Cardinality(votes'[self][(msg[self]).term])) * (2)) > (Cardinality(Servers))
                                                                                THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                                     /\ matchIndex' = [matchIndex EXCEPT ![self] = [s3 \in Servers |-> 0]]
                                                                                     /\ nextIndex' = [nextIndex EXCEPT ![self] = [s4 \in Servers |-> 1]]
                                                                                     /\ networkWrite19' = mailboxes
                                                                                     /\ networkWrite20' = networkWrite19'
                                                                                     /\ networkWrite21' = networkWrite20'
                                                                                     /\ appliedWrite4' = appliedLocal[self]
                                                                                     /\ mailboxes' = networkWrite21'
                                                                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                                     /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                                                ELSE /\ networkWrite19' = mailboxes
                                                                                     /\ networkWrite20' = networkWrite19'
                                                                                     /\ networkWrite21' = networkWrite20'
                                                                                     /\ appliedWrite4' = appliedLocal[self]
                                                                                     /\ mailboxes' = networkWrite21'
                                                                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                                     /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                                                     /\ UNCHANGED << state, 
                                                                                                     nextIndex, 
                                                                                                     matchIndex >>
                                                                     ELSE /\ networkWrite19' = mailboxes
                                                                          /\ networkWrite20' = networkWrite19'
                                                                          /\ networkWrite21' = networkWrite20'
                                                                          /\ appliedWrite4' = appliedLocal[self]
                                                                          /\ mailboxes' = networkWrite21'
                                                                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                                          /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                                          /\ UNCHANGED << state, 
                                                                                          nextIndex, 
                                                                                          matchIndex, 
                                                                                          votes >>
                                                          ELSE /\ networkWrite19' = mailboxes
                                                               /\ networkWrite20' = networkWrite19'
                                                               /\ networkWrite21' = networkWrite20'
                                                               /\ appliedWrite4' = appliedLocal[self]
                                                               /\ mailboxes' = networkWrite21'
                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite4']
                                                               /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                               /\ UNCHANGED << state, 
                                                                               nextIndex, 
                                                                               matchIndex, 
                                                                               votes >>
                                                    /\ UNCHANGED << ifResult0, 
                                                                    networkWrite18 >>
                              /\ UNCHANGED << networkWrite9, networkWrite10, 
                                              networkWrite11, log >>
                   /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                                   networkWrite1, networkWrite2, valuesRead, 
                                   valuesWrite, appliedWrite, appliedWrite0, 
                                   networkWrite3, networkWrite4, valuesWrite0, 
                                   appliedWrite1, networkWrite5, networkRead, 
                                   networkWrite6, networkWrite7, networkWrite8, 
                                   ifResult, appliedWrite2, appliedWrite3, 
                                   networkWrite12, networkWrite13, 
                                   networkWrite14, networkWrite15, 
                                   networkWrite16, networkWrite17, 
                                   networkWrite22, appliedWrite5, 
                                   networkWrite23, valuesWrite1, appliedWrite6, 
                                   valuesLocal, timeoutLocal, currentTerm, 
                                   votedFor, commitIndex, lastApplied, 
                                   iterator, msg, msgs >>

AEUpdateCommited(self) == /\ pc[self] = "AEUpdateCommited"
                          /\ IF ((msg[self]).commit) > (commitIndex[self])
                                THEN /\ IF ((msg[self]).commit) < (Len(log[self]))
                                           THEN /\ ifResult' = (msg[self]).commit
                                           ELSE /\ ifResult' = Len(log[self])
                                     /\ commitIndex' = [commitIndex EXCEPT ![self] = ifResult']
                                     /\ pc' = [pc EXCEPT ![self] = "AEApplyCommitted"]
                                     /\ UNCHANGED << appliedWrite3, 
                                                     appliedLocal >>
                                ELSE /\ appliedWrite3' = appliedLocal[self]
                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite3']
                                     /\ pc' = [pc EXCEPT ![self] = "W1"]
                                     /\ UNCHANGED << ifResult, commitIndex >>
                          /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                                          networkWrite0, networkWrite1, 
                                          networkWrite2, valuesRead, 
                                          valuesWrite, appliedWrite, 
                                          appliedWrite0, networkWrite3, 
                                          networkWrite4, valuesWrite0, 
                                          appliedWrite1, networkWrite5, 
                                          networkRead, networkWrite6, 
                                          networkWrite7, networkWrite8, 
                                          networkWrite9, networkWrite10, 
                                          networkWrite11, appliedWrite2, 
                                          networkWrite12, networkWrite13, 
                                          networkWrite14, networkWrite15, 
                                          networkWrite16, ifResult0, 
                                          networkWrite17, networkWrite18, 
                                          networkWrite19, networkWrite20, 
                                          networkWrite21, appliedWrite4, 
                                          networkWrite22, appliedWrite5, 
                                          networkWrite23, valuesWrite1, 
                                          appliedWrite6, valuesLocal, 
                                          timeoutLocal, currentTerm, votedFor, 
                                          log, state, lastApplied, nextIndex, 
                                          matchIndex, iterator, votes, msg, 
                                          msgs >>

AEApplyCommitted(self) == /\ pc[self] = "AEApplyCommitted"
                          /\ IF (lastApplied[self]) < (commitIndex[self])
                                THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                                     /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied'[self]] = (appliedLocal[self][lastApplied'[self]]) \union ({log[self][lastApplied'[self]]})]
                                     /\ appliedWrite2' = appliedWrite'
                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                                     /\ pc' = [pc EXCEPT ![self] = "AEApplyCommitted"]
                                ELSE /\ appliedWrite2' = appliedLocal[self]
                                     /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                                     /\ pc' = [pc EXCEPT ![self] = "W1"]
                                     /\ UNCHANGED << appliedWrite, lastApplied >>
                          /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                                          networkWrite0, networkWrite1, 
                                          networkWrite2, valuesRead, 
                                          valuesWrite, appliedWrite0, 
                                          networkWrite3, networkWrite4, 
                                          valuesWrite0, appliedWrite1, 
                                          networkWrite5, networkRead, 
                                          networkWrite6, networkWrite7, 
                                          networkWrite8, networkWrite9, 
                                          networkWrite10, networkWrite11, 
                                          ifResult, appliedWrite3, 
                                          networkWrite12, networkWrite13, 
                                          networkWrite14, networkWrite15, 
                                          networkWrite16, ifResult0, 
                                          networkWrite17, networkWrite18, 
                                          networkWrite19, networkWrite20, 
                                          networkWrite21, appliedWrite4, 
                                          networkWrite22, appliedWrite5, 
                                          networkWrite23, valuesWrite1, 
                                          appliedWrite6, valuesLocal, 
                                          timeoutLocal, currentTerm, votedFor, 
                                          log, state, commitIndex, nextIndex, 
                                          matchIndex, iterator, votes, msg, 
                                          msgs >>

AEStale(self) == /\ pc[self] = "AEStale"
                 /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                 /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
                       /\ networkWrite6' = networkWrite'
                       /\ mailboxes' = networkWrite6'
                    \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                       /\ networkWrite6' = networkWrite'
                       /\ mailboxes' = networkWrite6'
                 /\ pc' = [pc EXCEPT ![self] = "AEUpdateCommited"]
                 /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                 networkWrite2, valuesRead, valuesWrite, 
                                 appliedWrite, appliedWrite0, networkWrite3, 
                                 networkWrite4, valuesWrite0, appliedWrite1, 
                                 networkWrite5, networkRead, networkWrite7, 
                                 networkWrite8, networkWrite9, networkWrite10, 
                                 networkWrite11, ifResult, appliedWrite2, 
                                 appliedWrite3, networkWrite12, networkWrite13, 
                                 networkWrite14, networkWrite15, 
                                 networkWrite16, ifResult0, networkWrite17, 
                                 networkWrite18, networkWrite19, 
                                 networkWrite20, networkWrite21, appliedWrite4, 
                                 networkWrite22, appliedWrite5, networkWrite23, 
                                 valuesWrite1, appliedWrite6, appliedLocal, 
                                 valuesLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg, msgs >>

AENotMatching(self) == /\ pc[self] = "AENotMatching"
                       /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                       /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
                             /\ networkWrite7' = networkWrite'
                             /\ mailboxes' = networkWrite7'
                          \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                             /\ networkWrite7' = networkWrite'
                             /\ mailboxes' = networkWrite7'
                       /\ pc' = [pc EXCEPT ![self] = "AEUpdateCommited"]
                       /\ UNCHANGED << timeoutRead, networkWrite0, 
                                       networkWrite1, networkWrite2, 
                                       valuesRead, valuesWrite, appliedWrite, 
                                       appliedWrite0, networkWrite3, 
                                       networkWrite4, valuesWrite0, 
                                       appliedWrite1, networkWrite5, 
                                       networkRead, networkWrite6, 
                                       networkWrite8, networkWrite9, 
                                       networkWrite10, networkWrite11, 
                                       ifResult, appliedWrite2, appliedWrite3, 
                                       networkWrite12, networkWrite13, 
                                       networkWrite14, networkWrite15, 
                                       networkWrite16, ifResult0, 
                                       networkWrite17, networkWrite18, 
                                       networkWrite19, networkWrite20, 
                                       networkWrite21, appliedWrite4, 
                                       networkWrite22, appliedWrite5, 
                                       networkWrite23, valuesWrite1, 
                                       appliedWrite6, appliedLocal, 
                                       valuesLocal, timeoutLocal, currentTerm, 
                                       votedFor, log, state, commitIndex, 
                                       lastApplied, nextIndex, matchIndex, 
                                       iterator, votes, msg, msgs >>

AEValid(self) == /\ pc[self] = "AEValid"
                 /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                 /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg[self]).prevIndex) + (Len((msg[self]).entries)), prevTerm |-> Nil, commit |-> Nil])]
                       /\ networkWrite8' = networkWrite'
                       /\ mailboxes' = networkWrite8'
                    \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg[self]).prevIndex) + (Len((msg[self]).entries)), prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                       /\ networkWrite8' = networkWrite'
                       /\ mailboxes' = networkWrite8'
                 /\ pc' = [pc EXCEPT ![self] = "AEUpdateCommited"]
                 /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                 networkWrite2, valuesRead, valuesWrite, 
                                 appliedWrite, appliedWrite0, networkWrite3, 
                                 networkWrite4, valuesWrite0, appliedWrite1, 
                                 networkWrite5, networkRead, networkWrite6, 
                                 networkWrite7, networkWrite9, networkWrite10, 
                                 networkWrite11, ifResult, appliedWrite2, 
                                 appliedWrite3, networkWrite12, networkWrite13, 
                                 networkWrite14, networkWrite15, 
                                 networkWrite16, ifResult0, networkWrite17, 
                                 networkWrite18, networkWrite19, 
                                 networkWrite20, networkWrite21, appliedWrite4, 
                                 networkWrite22, appliedWrite5, networkWrite23, 
                                 valuesWrite1, appliedWrite6, appliedLocal, 
                                 valuesLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg, msgs >>

RVStale(self) == /\ pc[self] = "RVStale"
                 /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                 /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
                       /\ networkWrite12' = networkWrite'
                    \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                       /\ networkWrite12' = networkWrite'
                 /\ mailboxes' = networkWrite12'
                 /\ pc' = [pc EXCEPT ![self] = "W1"]
                 /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                 networkWrite2, valuesRead, valuesWrite, 
                                 appliedWrite, appliedWrite0, networkWrite3, 
                                 networkWrite4, valuesWrite0, appliedWrite1, 
                                 networkWrite5, networkRead, networkWrite6, 
                                 networkWrite7, networkWrite8, networkWrite9, 
                                 networkWrite10, networkWrite11, ifResult, 
                                 appliedWrite2, appliedWrite3, networkWrite13, 
                                 networkWrite14, networkWrite15, 
                                 networkWrite16, ifResult0, networkWrite17, 
                                 networkWrite18, networkWrite19, 
                                 networkWrite20, networkWrite21, appliedWrite4, 
                                 networkWrite22, appliedWrite5, networkWrite23, 
                                 valuesWrite1, appliedWrite6, appliedLocal, 
                                 valuesLocal, timeoutLocal, currentTerm, 
                                 votedFor, log, state, commitIndex, 
                                 lastApplied, nextIndex, matchIndex, iterator, 
                                 votes, msg, msgs >>

RVValid(self) == /\ pc[self] = "RVValid"
                 /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                 /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
                       /\ networkWrite13' = networkWrite'
                    \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                       /\ networkWrite13' = networkWrite'
                 /\ votedFor' = [votedFor EXCEPT ![self] = (msg[self]).sender]
                 /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
                 /\ mailboxes' = networkWrite13'
                 /\ pc' = [pc EXCEPT ![self] = "W1"]
                 /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                 networkWrite2, valuesRead, valuesWrite, 
                                 appliedWrite, appliedWrite0, networkWrite3, 
                                 networkWrite4, valuesWrite0, appliedWrite1, 
                                 networkWrite5, networkRead, networkWrite6, 
                                 networkWrite7, networkWrite8, networkWrite9, 
                                 networkWrite10, networkWrite11, ifResult, 
                                 appliedWrite2, appliedWrite3, networkWrite12, 
                                 networkWrite14, networkWrite15, 
                                 networkWrite16, ifResult0, networkWrite17, 
                                 networkWrite18, networkWrite19, 
                                 networkWrite20, networkWrite21, appliedWrite4, 
                                 networkWrite22, appliedWrite5, networkWrite23, 
                                 valuesWrite1, appliedWrite6, appliedLocal, 
                                 valuesLocal, timeoutLocal, log, state, 
                                 commitIndex, lastApplied, nextIndex, 
                                 matchIndex, iterator, votes, msg, msgs >>

RVInvalid(self) == /\ pc[self] = "RVInvalid"
                   /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                   /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
                         /\ networkWrite14' = networkWrite'
                      \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil]>>) \o (mailboxes[(msg[self]).sender])]
                         /\ networkWrite14' = networkWrite'
                   /\ mailboxes' = networkWrite14'
                   /\ pc' = [pc EXCEPT ![self] = "W1"]
                   /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                                   networkWrite2, valuesRead, valuesWrite, 
                                   appliedWrite, appliedWrite0, networkWrite3, 
                                   networkWrite4, valuesWrite0, appliedWrite1, 
                                   networkWrite5, networkRead, networkWrite6, 
                                   networkWrite7, networkWrite8, networkWrite9, 
                                   networkWrite10, networkWrite11, ifResult, 
                                   appliedWrite2, appliedWrite3, 
                                   networkWrite12, networkWrite13, 
                                   networkWrite15, networkWrite16, ifResult0, 
                                   networkWrite17, networkWrite18, 
                                   networkWrite19, networkWrite20, 
                                   networkWrite21, appliedWrite4, 
                                   networkWrite22, appliedWrite5, 
                                   networkWrite23, valuesWrite1, appliedWrite6, 
                                   appliedLocal, valuesLocal, timeoutLocal, 
                                   currentTerm, votedFor, log, state, 
                                   commitIndex, lastApplied, nextIndex, 
                                   matchIndex, iterator, votes, msg, msgs >>

RetryAppendEntry(self) == /\ pc[self] = "RetryAppendEntry"
                          /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
                          /\ \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), commit |-> commitIndex[self]])]
                                /\ networkWrite17' = networkWrite'
                             \/ /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = (<<[sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), commit |-> commitIndex[self]]>>) \o (mailboxes[(msg[self]).sender])]
                                /\ networkWrite17' = networkWrite'
                          /\ mailboxes' = networkWrite17'
                          /\ pc' = [pc EXCEPT ![self] = "W1"]
                          /\ UNCHANGED << timeoutRead, networkWrite0, 
                                          networkWrite1, networkWrite2, 
                                          valuesRead, valuesWrite, 
                                          appliedWrite, appliedWrite0, 
                                          networkWrite3, networkWrite4, 
                                          valuesWrite0, appliedWrite1, 
                                          networkWrite5, networkRead, 
                                          networkWrite6, networkWrite7, 
                                          networkWrite8, networkWrite9, 
                                          networkWrite10, networkWrite11, 
                                          ifResult, appliedWrite2, 
                                          appliedWrite3, networkWrite12, 
                                          networkWrite13, networkWrite14, 
                                          networkWrite15, networkWrite16, 
                                          ifResult0, networkWrite18, 
                                          networkWrite19, networkWrite20, 
                                          networkWrite21, appliedWrite4, 
                                          networkWrite22, appliedWrite5, 
                                          networkWrite23, valuesWrite1, 
                                          appliedWrite6, appliedLocal, 
                                          valuesLocal, timeoutLocal, 
                                          currentTerm, votedFor, log, state, 
                                          commitIndex, lastApplied, nextIndex, 
                                          matchIndex, iterator, votes, msg, 
                                          msgs >>

server(self) == MainLoop(self) \/ TimeoutCheck(self) \/ SendReqVotes(self)
                   \/ LeaderCheck(self) \/ AdvanceIndex(self)
                   \/ ApplyCommited(self) \/ SendAppendEntries(self)
                   \/ RecvMsg(self) \/ W1(self) \/ W2(self)
                   \/ CheckMsgTerm(self) \/ MsgSwitch(self)
                   \/ AEUpdateCommited(self) \/ AEApplyCommitted(self)
                   \/ AEStale(self) \/ AENotMatching(self) \/ AEValid(self)
                   \/ RVStale(self) \/ RVValid(self) \/ RVInvalid(self)
                   \/ RetryAppendEntry(self)

Next == (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))

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
AppliedCorrect == \A n \in Servers, s \in 1..Slots : Cardinality(appliedLocal[n][s]) <= 1

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
