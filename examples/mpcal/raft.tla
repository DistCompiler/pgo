/--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Terms
CONSTANTS Slots
CONSTANTS N
CONSTANTS BUFFER_SIZE

\* A reserved value.
CONSTANTS Nil

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
        Follower == 0
        Candidate == 1
        Leader == 2
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log,index) == (IF index > 0 /\ Len(log) >= index /\ Len(log) > 0 THEN log[index].term ELSE 0)
    }
    
    macro SendRequestVotes(network, cterm, candidateId, lastLogIndex, lastLogTerm, idx) {
        while (idx <= Cardinality(Servers)) {
            if (idx # candidateId) {
                network[idx] := [sender |-> candidateId, type |-> RequestVote, term |-> cterm, granted |-> FALSE, entries |-> <<>>,
                                 prevIndex |-> lastLogIndex, prevTerm |-> lastLogTerm, commit |-> Nil];
            };

            idx := idx + 1;
        };
    }
    
    macro SendAppendEntries(network, cterm, candidateId, nextIndex, matchIndex, log, leaderCommit, idx) {
        while (idx <= Cardinality(Servers)) {
            if (idx # candidateId) {
                network[idx] := [sender |-> candidateId, type |-> AppendEntries, term |-> cterm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)),
                                 prevIndex |-> nextIndex[idx]-1, prevTerm |-> Term(log, nextIndex[idx]-1), commit |-> leaderCommit];
            };
            
            idx := idx + 1;
        };
    }
    
    mapping macro FIFOChannel {
        read {
            await Len($variable) > 0;
            with (msg = Head($variable)) {
                $variable := Tail($variable);
                yield msg;
            };
        }
  
        write {
            await Len($variable) < BUFFER_SIZE;
            yield Append($variable, $value);
        }
    }
      
    mapping macro Log {
        read {
            assert(FALSE);
        }
  
        write {
            yield $variable \union {$value};
        }
    }
    
    mapping macro Timeout {
        read {
            either { $variable := FALSE; } or { $variable := TRUE; };
            yield $variable;
        }
  
        write {
            assert(FALSE);
        }
    }
    
    mapping macro ID {
        read {
            yield $variable;
        }
  
        write {
            yield $value;
        }
    }
    
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
    variable currentTerm = 0,
             votedFor = Nil,
             log = <<>>,
             state = Follower,
             commitIndex = 0,
             lastApplied = 0,
             v,
             nextIndex,
             matchIndex,
             idx,
             votes = [t \in 0..Terms |-> {}],
             msg; {
Start:while (commitIndex < Slots /\ currentTerm < Terms) {
        \* Election timeout
N10:    if (state # Leader /\ timeout) {
            state := Candidate;
            currentTerm := currentTerm + 1;
            votes[currentTerm] := {self};
            votedFor := self;
            idx := 1;
loop4:      SendRequestVotes(network, currentTerm, self, Len(log), Term(log, Len(log)), idx);
        };

        \* Act as leader
N11:    if (state = Leader) {
            v := values;
            log := Append(log, [val |-> v, term |-> currentTerm]);
            matchIndex[self] := Len(log);
            nextIndex[self] := Len(log)+1;
            idx := 1;
loop5:      SendAppendEntries(network, currentTerm, self, nextIndex, matchIndex, log, commitIndex, idx);
        };
      
N1:     msg := network[self];
N1a:    if (msg.type = AppendEntries) {
            if (msg.term < currentTerm) {
N2:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif ((msg.prevIndex > 0 /\ Len(log) < msg.prevIndex) \/ Term(log, msg.prevIndex) # msg.prevTerm) {
                \* Following entries don't have matching terms
                log := SubSeq(log,1,msg.prevIndex-1);
N3:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif (Len(log) = msg.prevIndex) {
                log := log \o msg.entries;
N4:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> msg.prevIndex + Len(msg.entries), prevTerm |-> Nil, commit |-> Nil];
            };

N5:         if (msg.term > currentTerm) {
                state := Follower;
                currentTerm := msg.term;
            };

            if (msg.commit > commitIndex) {
                commitIndex := IF msg.commit < Len(log) THEN msg.commit ELSE Len(log);
loop1:          while(lastApplied < commitIndex) {
                    lastApplied := lastApplied + 1;
                    applied[lastApplied] := log[lastApplied];
                };
            };
        } elseif (msg.type = RequestVote) {
            if (msg.term < currentTerm) {
N6:             network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            } elseif ((votedFor = Nil \/ votedFor = msg.sender)
                     /\ (msg.prevTerm > Term(log, Len(log))
                         \/ (msg.prevTerm = Term(log, Len(log)) /\ msg.prevIndex >= Len(log)))) {
                \*log := SubSeq(log, 1, msg.prevIndex-1);
 N7:            network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
                votedFor := msg.sender;
                currentTerm := msg.term;
            } else {
 N8:            network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> msg.term, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil];
            }
        } elseif (msg.type = AppendEntriesResponse) {
            if (msg.granted /\ state = Leader) {
                nextIndex[msg.sender] := msg.prevIndex + 1;
                matchIndex[msg.sender] := msg.prevIndex;
loop2:          while (Cardinality({i \in Servers: matchIndex[i] > commitIndex})*2 > Cardinality(Servers) /\ Term(log, commitIndex+1) = currentTerm) {
                    commitIndex := commitIndex + 1;
                };
loop3:          while(lastApplied < commitIndex) {
                    lastApplied := lastApplied + 1;
                    applied[lastApplied] := log[lastApplied];
                };
            } else {
                nextIndex[msg.sender] := IF nextIndex[msg.sender] - 1 > 1 THEN nextIndex[msg.sender] - 1 ELSE 1;
N9:             network[msg.sender] := [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, nextIndex[msg.sender], Len(log)),
                                        prevIndex |-> nextIndex[msg.sender]-1, prevTerm |-> Term(log, nextIndex[msg.sender]-1), granted |-> FALSE, commit |-> commitIndex];
            };
        } elseif (msg.type = RequestVoteResponse) {
            if (msg.granted /\ state = Candidate) {
                votes[msg.term] := votes[msg.term] \union {msg.sender};
                if (Cardinality(votes[msg.term])*2 > Cardinality(Servers)) {
                    state := Leader;
                    matchIndex := [s3 \in Servers |-> 0];
                    nextIndex := [s4 \in Servers |-> 1];
                };
            };
        };
      };
    }
    
    
    variables
        mailboxes = [id \in Servers |-> <<>>];

    fair process (server \in Servers) == instance Node(ref mailboxes, [s \in 0..Slots |-> {}], <<1,2,3,4,5>>, TRUE)
        mapping mailboxes[_] via FIFOChannel
        mapping @2[_] via Log
        mapping @3 via Input
        mapping @4 via Timeout;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm Raft {
    variables mailboxes = [id \in Servers |-> <<>>], timeoutRead, timeoutWrite, timeoutWrite0, networkWrite, networkWrite0, networkWrite1, networkWrite2, valuesRead, valuesWrite, networkWrite3, networkWrite4, networkWrite5, networkRead, networkWrite6, networkWrite7, networkWrite8, ifResult, appliedWrite, appliedWrite0, appliedWrite1, networkWrite9, networkWrite10, appliedWrite2, ifResult0, appliedWrite3, networkWrite11, appliedWrite4, networkWrite12, networkWrite13, appliedWrite5, appliedWrite6, networkWrite14, appliedWrite7, networkWrite15;
    define {
        Servers == (1) .. (N)
        Follower == 0
        Candidate == 1
        Leader == 2
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0
    }
    fair process (server \in Servers)
    variables appliedLocal = [s \in (0) .. (Slots) |-> {}], valuesLocal = <<1, 2, 3, 4, 5>>, timeoutLocal = TRUE, currentTerm = 0, votedFor = Nil, log = <<>>, state = Follower, commitIndex = 0, lastApplied = 0, v, nextIndex, matchIndex, idx, votes = [t \in (0) .. (Terms) |-> {}], msg;
    {
        Start:
            if (((commitIndex) < (Slots)) /\ ((currentTerm) < (Terms))) {
                N10:
                    either {
                        timeoutWrite := FALSE;
                    } or {
                        timeoutWrite0 := TRUE;
                    };
                    timeoutRead := timeoutWrite0;
                    if (((state) # (Leader)) /\ (timeoutRead)) {
                        state := Candidate;
                        currentTerm := (currentTerm) + (1);
                        votes[currentTerm] := {self};
                        votedFor := self;
                        idx := 1;
                        timeoutLocal := timeoutWrite0;
                        loop4:
                            if ((idx) <= (Cardinality(Servers))) {
                                if ((idx) # (self)) {
                                    await (Len(mailboxes[idx])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![idx] = Append(mailboxes[idx], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log)), commit |-> Nil])];
                                    networkWrite0 := networkWrite;
                                } else {
                                    networkWrite0 := mailboxes;
                                };
                                idx := (idx) + (1);
                                networkWrite1 := networkWrite0;
                                mailboxes := networkWrite1;
                                goto loop4;
                            } else {
                                networkWrite1 := mailboxes;
                                mailboxes := networkWrite1;
                            };
                    
                    } else {
                        networkWrite2 := mailboxes;
                        mailboxes := networkWrite2;
                    };
                
                N11:
                    if ((state) = (Leader)) {
                        with (msg0 = Head(valuesLocal)) {
                            valuesWrite := Tail(valuesLocal);
                            valuesRead := msg0;
                        };
                        v := valuesRead;
                        log := Append(log, [val |-> v, term |-> currentTerm]);
                        matchIndex[self] := Len(log);
                        nextIndex[self] := (Len(log)) + (1);
                        idx := 1;
                        valuesLocal := valuesWrite;
                        loop5:
                            if ((idx) <= (Cardinality(Servers))) {
                                if ((idx) # (self)) {
                                    await (Len(mailboxes[idx])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![idx] = Append(mailboxes[idx], [sender |-> self, type |-> AppendEntries, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)), prevIndex |-> (nextIndex[idx]) - (1), prevTerm |-> Term(log, (nextIndex[idx]) - (1)), commit |-> commitIndex])];
                                    networkWrite3 := networkWrite;
                                } else {
                                    networkWrite3 := mailboxes;
                                };
                                idx := (idx) + (1);
                                networkWrite4 := networkWrite3;
                                mailboxes := networkWrite4;
                                goto loop5;
                            } else {
                                networkWrite4 := mailboxes;
                                mailboxes := networkWrite4;
                            };
                    
                    } else {
                        networkWrite5 := mailboxes;
                        mailboxes := networkWrite5;
                    };
                
                N1:
                    await (Len(mailboxes[self])) > (0);
                    with (msg1 = Head(mailboxes[self])) {
                        networkWrite := [mailboxes EXCEPT ![self] = Tail(mailboxes[self])];
                        networkRead := msg1;
                    };
                    msg := networkRead;
                    mailboxes := networkWrite;
                
                N1a:
                    if (((msg).type) = (AppendEntries)) {
                        if (((msg).term) < (currentTerm)) {
                            N2:
                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                mailboxes := networkWrite;
                        
                        } else {
                            if (((((msg).prevIndex) > (0)) /\ ((Len(log)) < ((msg).prevIndex))) \/ ((Term(log, (msg).prevIndex)) # ((msg).prevTerm))) {
                                log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                                N3:
                                    await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                    mailboxes := networkWrite;
                            
                            } else {
                                if ((Len(log)) = ((msg).prevIndex)) {
                                    log := (log) \o ((msg).entries);
                                    N4:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg).prevIndex) + (Len((msg).entries)), prevTerm |-> Nil, commit |-> Nil])];
                                        mailboxes := networkWrite;
                                
                                } else {
                                    networkWrite6 := mailboxes;
                                    networkWrite7 := networkWrite6;
                                    networkWrite8 := networkWrite7;
                                    mailboxes := networkWrite8;
                                };
                            };
                        };
                        N5:
                            if (((msg).term) > (currentTerm)) {
                                state := Follower;
                                currentTerm := (msg).term;
                            };
                            if (((msg).commit) > (commitIndex)) {
                                if (((msg).commit) < (Len(log))) {
                                    ifResult := (msg).commit;
                                } else {
                                    ifResult := Len(log);
                                };
                                commitIndex := ifResult;
                                loop1:
                                    if ((lastApplied) < (commitIndex)) {
                                        lastApplied := (lastApplied) + (1);
                                        appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
                                        appliedWrite0 := appliedWrite;
                                        appliedLocal := appliedWrite0;
                                        goto loop1;
                                    } else {
                                        appliedWrite0 := appliedLocal;
                                        appliedLocal := appliedWrite0;
                                        goto Start;
                                    };
                            
                            } else {
                                appliedWrite1 := appliedLocal;
                                appliedLocal := appliedWrite1;
                                goto Start;
                            };
                    
                    } else {
                        if (((msg).type) = (RequestVote)) {
                            if (((msg).term) < (currentTerm)) {
                                N6:
                                    await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                    mailboxes := networkWrite;
                                    goto Start;
                            
                            } else {
                                if ((((votedFor) = (Nil)) \/ ((votedFor) = ((msg).sender))) /\ ((((msg).prevTerm) > (Term(log, Len(log)))) \/ ((((msg).prevTerm) = (Term(log, Len(log)))) /\ (((msg).prevIndex) >= (Len(log)))))) {
                                    N7:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                        votedFor := (msg).sender;
                                        currentTerm := (msg).term;
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                } else {
                                    N8:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])];
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                };
                            };
                        } else {
                            if (((msg).type) = (AppendEntriesResponse)) {
                                if (((msg).granted) /\ ((state) = (Leader))) {
                                    nextIndex[(msg).sender] := ((msg).prevIndex) + (1);
                                    matchIndex[(msg).sender] := (msg).prevIndex;
                                    loop2:
                                        if ((((Cardinality({i \in Servers : (matchIndex[i]) > (commitIndex)})) * (2)) > (Cardinality(Servers))) /\ ((Term(log, (commitIndex) + (1))) = (currentTerm))) {
                                            commitIndex := (commitIndex) + (1);
                                            goto loop2;
                                        };
                                    
                                    loop3:
                                        if ((lastApplied) < (commitIndex)) {
                                            lastApplied := (lastApplied) + (1);
                                            appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
                                            appliedWrite2 := appliedWrite;
                                            appliedLocal := appliedWrite2;
                                            goto loop3;
                                        } else {
                                            appliedWrite2 := appliedLocal;
                                            appliedLocal := appliedWrite2;
                                            goto Start;
                                        };
                                
                                } else {
                                    if (((nextIndex[(msg).sender]) - (1)) > (1)) {
                                        ifResult0 := (nextIndex[(msg).sender]) - (1);
                                    } else {
                                        ifResult0 := 1;
                                    };
                                    nextIndex[(msg).sender] := ifResult0;
                                    N9:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, nextIndex[(msg).sender], Len(log)), prevIndex |-> (nextIndex[(msg).sender]) - (1), prevTerm |-> Term(log, (nextIndex[(msg).sender]) - (1)), granted |-> FALSE, commit |-> commitIndex])];
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                };
                            } else {
                                if (((msg).type) = (RequestVoteResponse)) {
                                    if (((msg).granted) /\ ((state) = (Candidate))) {
                                        votes[(msg).term] := (votes[(msg).term]) \union ({(msg).sender});
                                        if (((Cardinality(votes[(msg).term])) * (2)) > (Cardinality(Servers))) {
                                            state := Leader;
                                            matchIndex := [s3 \in Servers |-> 0];
                                            nextIndex := [s4 \in Servers |-> 1];
                                            appliedWrite4 := appliedLocal;
                                            networkWrite12 := mailboxes;
                                            networkWrite13 := networkWrite12;
                                            appliedWrite5 := appliedWrite4;
                                            appliedWrite6 := appliedWrite5;
                                            networkWrite14 := networkWrite13;
                                            mailboxes := networkWrite14;
                                            appliedLocal := appliedWrite6;
                                            goto Start;
                                        } else {
                                            appliedWrite4 := appliedLocal;
                                            networkWrite12 := mailboxes;
                                            networkWrite13 := networkWrite12;
                                            appliedWrite5 := appliedWrite4;
                                            appliedWrite6 := appliedWrite5;
                                            networkWrite14 := networkWrite13;
                                            mailboxes := networkWrite14;
                                            appliedLocal := appliedWrite6;
                                            goto Start;
                                        };
                                    } else {
                                        appliedWrite4 := appliedLocal;
                                        networkWrite12 := mailboxes;
                                        networkWrite13 := networkWrite12;
                                        appliedWrite5 := appliedWrite4;
                                        appliedWrite6 := appliedWrite5;
                                        networkWrite14 := networkWrite13;
                                        mailboxes := networkWrite14;
                                        appliedLocal := appliedWrite6;
                                        goto Start;
                                    };
                                } else {
                                    appliedWrite4 := appliedLocal;
                                    networkWrite12 := mailboxes;
                                    networkWrite13 := networkWrite12;
                                    appliedWrite5 := appliedWrite4;
                                    appliedWrite6 := appliedWrite5;
                                    networkWrite14 := networkWrite13;
                                    mailboxes := networkWrite14;
                                    appliedLocal := appliedWrite6;
                                    goto Start;
                                };
                            };
                        };
                    };
            
            } else {
                appliedWrite7 := appliedLocal;
                networkWrite15 := mailboxes;
                mailboxes := networkWrite15;
                appliedLocal := appliedWrite7;
            };
    
    }
}
\* END PLUSCAL TRANSLATION

******************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
          networkWrite2, valuesRead, valuesWrite, networkWrite3, 
          networkWrite4, networkWrite5, networkRead, networkWrite6, 
          networkWrite7, networkWrite8, ifResult, appliedWrite, appliedWrite0, 
          appliedWrite1, networkWrite9, networkWrite10, appliedWrite2, 
          ifResult0, appliedWrite3, networkWrite11, appliedWrite4, 
          networkWrite12, networkWrite13, appliedWrite5, appliedWrite6, 
          networkWrite14, appliedWrite7, networkWrite15, pc

(* define statement *)
Servers == (1) .. (N)
Follower == 0
Candidate == 1
Leader == 2
RequestVote == 0
RequestVoteResponse == 1
AppendEntries == 2
AppendEntriesResponse == 3
Term(log, index) == IF (((index) > (0)) /\ ((Len(log)) >= (index))) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0

VARIABLES appliedLocal, valuesLocal, timeoutLocal, currentTerm, votedFor, log, 
          state, commitIndex, lastApplied, v, nextIndex, matchIndex, idx, 
          votes, msg

vars == << mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
           networkWrite2, valuesRead, valuesWrite, networkWrite3, 
           networkWrite4, networkWrite5, networkRead, networkWrite6, 
           networkWrite7, networkWrite8, ifResult, appliedWrite, 
           appliedWrite0, appliedWrite1, networkWrite9, networkWrite10, 
           appliedWrite2, ifResult0, appliedWrite3, networkWrite11, 
           appliedWrite4, networkWrite12, networkWrite13, appliedWrite5, 
           appliedWrite6, networkWrite14, appliedWrite7, networkWrite15, pc, 
           appliedLocal, valuesLocal, timeoutLocal, currentTerm, votedFor, 
           log, state, commitIndex, lastApplied, v, nextIndex, matchIndex, 
           idx, votes, msg >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ mailboxes = [id \in Servers |-> <<>>]
        /\ timeoutRead = TRUE
        /\ networkWrite = defaultInitValue
        /\ networkWrite0 = defaultInitValue
        /\ networkWrite1 = defaultInitValue
        /\ networkWrite2 = defaultInitValue
        /\ valuesRead = defaultInitValue
        /\ valuesWrite = defaultInitValue
        /\ networkWrite3 = defaultInitValue
        /\ networkWrite4 = defaultInitValue
        /\ networkWrite5 = defaultInitValue
        /\ networkRead = defaultInitValue
        /\ networkWrite6 = defaultInitValue
        /\ networkWrite7 = defaultInitValue
        /\ networkWrite8 = defaultInitValue
        /\ ifResult = defaultInitValue
        /\ appliedWrite = defaultInitValue
        /\ appliedWrite0 = defaultInitValue
        /\ appliedWrite1 = defaultInitValue
        /\ networkWrite9 = defaultInitValue
        /\ networkWrite10 = defaultInitValue
        /\ appliedWrite2 = defaultInitValue
        /\ ifResult0 = defaultInitValue
        /\ appliedWrite3 = defaultInitValue
        /\ networkWrite11 = defaultInitValue
        /\ appliedWrite4 = defaultInitValue
        /\ networkWrite12 = defaultInitValue
        /\ networkWrite13 = defaultInitValue
        /\ appliedWrite5 = defaultInitValue
        /\ appliedWrite6 = defaultInitValue
        /\ networkWrite14 = defaultInitValue
        /\ appliedWrite7 = defaultInitValue
        /\ networkWrite15 = defaultInitValue
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
        /\ v = [self \in Servers |-> defaultInitValue]
        /\ nextIndex = [self \in Servers |-> defaultInitValue]
        /\ matchIndex = [self \in Servers |-> defaultInitValue]
        /\ idx = [self \in Servers |-> defaultInitValue]
        /\ votes = [self \in Servers |-> [t \in (0) .. (Terms) |-> {}]]
        /\ msg = [self \in Servers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ IF ((commitIndex[self]) < (Slots)) /\ ((currentTerm[self]) < (Terms))
                     THEN /\ pc' = [pc EXCEPT ![self] = "N10"]
                          /\ UNCHANGED << mailboxes, appliedWrite7, 
                                          networkWrite15, appliedLocal >>
                     ELSE /\ appliedWrite7' = appliedLocal[self]
                          /\ networkWrite15' = mailboxes
                          /\ mailboxes' = networkWrite15'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite7']
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                               networkWrite1, networkWrite2, valuesRead, 
                               valuesWrite, networkWrite3, networkWrite4, 
                               networkWrite5, networkRead, networkWrite6, 
                               networkWrite7, networkWrite8, ifResult, 
                               appliedWrite, appliedWrite0, appliedWrite1, 
                               networkWrite9, networkWrite10, appliedWrite2, 
                               ifResult0, appliedWrite3, networkWrite11, 
                               appliedWrite4, networkWrite12, networkWrite13, 
                               appliedWrite5, appliedWrite6, networkWrite14, 
                               valuesLocal, timeoutLocal, currentTerm, 
                               votedFor, log, state, commitIndex, lastApplied, 
                               v, nextIndex, matchIndex, idx, votes, msg >>

N10(self) == /\ pc[self] = "N10"
             /\ \/ /\ timeoutRead' = FALSE
                \/ /\ timeoutRead' = TRUE
             /\ IF ((state[self]) # (Leader)) /\ (timeoutRead')
                   THEN /\ state' = [state EXCEPT ![self] = Candidate]
                        /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                        /\ votes' = [votes EXCEPT ![self][currentTerm'[self]] = {self}]
                        /\ votedFor' = [votedFor EXCEPT ![self] = self]
                        /\ idx' = [idx EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "loop4"]
                        /\ UNCHANGED << mailboxes, networkWrite2 >>
                   ELSE /\ networkWrite2' = mailboxes
                        /\ mailboxes' = networkWrite2'
                        /\ pc' = [pc EXCEPT ![self] = "N11"]
                        /\ UNCHANGED << currentTerm, votedFor, state, idx, 
                                        votes >>
             /\ UNCHANGED << networkWrite, networkWrite0, networkWrite1, 
                             valuesRead, valuesWrite, networkWrite3, 
                             networkWrite4, networkWrite5, networkRead, 
                             networkWrite6, networkWrite7, networkWrite8, 
                             ifResult, appliedWrite, appliedWrite0, 
                             appliedWrite1, networkWrite9, networkWrite10, 
                             appliedWrite2, ifResult0, appliedWrite3, 
                             networkWrite11, appliedWrite4, networkWrite12, 
                             networkWrite13, appliedWrite5, appliedWrite6, 
                             networkWrite14, appliedWrite7, networkWrite15, 
                             appliedLocal, valuesLocal, timeoutLocal, log, 
                             commitIndex, lastApplied, v, nextIndex, 
                             matchIndex, msg >>

loop4(self) == /\ pc[self] = "loop4"
               /\ IF (idx[self]) <= (Cardinality(Servers))
                     THEN /\ IF (idx[self]) # (self)
                                THEN /\ (Len(mailboxes[idx[self]])) < (BUFFER_SIZE)
                                     /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self])), commit |-> Nil])]
                                     /\ networkWrite0' = networkWrite'
                                ELSE /\ networkWrite0' = mailboxes
                                     /\ UNCHANGED networkWrite
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite1' = networkWrite0'
                          /\ mailboxes' = networkWrite1'
                          /\ pc' = [pc EXCEPT ![self] = "loop4"]
                     ELSE /\ networkWrite1' = mailboxes
                          /\ mailboxes' = networkWrite1'
                          /\ pc' = [pc EXCEPT ![self] = "N11"]
                          /\ UNCHANGED << networkWrite, networkWrite0, idx >>
               /\ UNCHANGED << timeoutRead, networkWrite2, valuesRead, 
                               valuesWrite, networkWrite3, networkWrite4, 
                               networkWrite5, networkRead, networkWrite6, 
                               networkWrite7, networkWrite8, ifResult, 
                               appliedWrite, appliedWrite0, appliedWrite1, 
                               networkWrite9, networkWrite10, appliedWrite2, 
                               ifResult0, appliedWrite3, networkWrite11, 
                               appliedWrite4, networkWrite12, networkWrite13, 
                               appliedWrite5, appliedWrite6, networkWrite14, 
                               appliedWrite7, networkWrite15, appliedLocal, 
                               valuesLocal, timeoutLocal, currentTerm, 
                               votedFor, log, state, commitIndex, lastApplied, 
                               v, nextIndex, matchIndex, votes, msg >>

N11(self) == /\ pc[self] = "N11"
             /\ IF (state[self]) = (Leader)
                   THEN /\ LET msg0 == Head(valuesLocal[self]) IN
                             /\ valuesWrite' = Tail(valuesLocal[self])
                             /\ valuesRead' = msg0
                        /\ v' = [v EXCEPT ![self] = valuesRead']
                        /\ log' = [log EXCEPT ![self] = Append(log[self], [val |-> v'[self], term |-> currentTerm[self]])]
                        /\ matchIndex' = [matchIndex EXCEPT ![self][self] = Len(log'[self])]
                        /\ nextIndex' = [nextIndex EXCEPT ![self][self] = (Len(log'[self])) + (1)]
                        /\ idx' = [idx EXCEPT ![self] = 1]
                        /\ valuesLocal' = [valuesLocal EXCEPT ![self] = valuesWrite']
                        /\ pc' = [pc EXCEPT ![self] = "loop5"]
                        /\ UNCHANGED << mailboxes, networkWrite5 >>
                   ELSE /\ networkWrite5' = mailboxes
                        /\ mailboxes' = networkWrite5'
                        /\ pc' = [pc EXCEPT ![self] = "N1"]
                        /\ UNCHANGED << valuesRead, valuesWrite, valuesLocal, 
                                        log, v, nextIndex, matchIndex, idx >>
             /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                             networkWrite1, networkWrite2, networkWrite3, 
                             networkWrite4, networkRead, networkWrite6, 
                             networkWrite7, networkWrite8, ifResult, 
                             appliedWrite, appliedWrite0, appliedWrite1, 
                             networkWrite9, networkWrite10, appliedWrite2, 
                             ifResult0, appliedWrite3, networkWrite11, 
                             appliedWrite4, networkWrite12, networkWrite13, 
                             appliedWrite5, appliedWrite6, networkWrite14, 
                             appliedWrite7, networkWrite15, appliedLocal, 
                             timeoutLocal, currentTerm, votedFor, state, 
                             commitIndex, lastApplied, votes, msg >>

loop5(self) == /\ pc[self] = "loop5"
               /\ IF (idx[self]) <= (Cardinality(Servers))
                     THEN /\ IF (idx[self]) # (self)
                                THEN /\ (Len(mailboxes[idx[self]])) < (BUFFER_SIZE)
                                     /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [sender |-> self, type |-> AppendEntries, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][idx[self]], Len(log[self])), prevIndex |-> (nextIndex[self][idx[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][idx[self]]) - (1)), commit |-> commitIndex[self]])]
                                     /\ networkWrite3' = networkWrite'
                                ELSE /\ networkWrite3' = mailboxes
                                     /\ UNCHANGED networkWrite
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite4' = networkWrite3'
                          /\ mailboxes' = networkWrite4'
                          /\ pc' = [pc EXCEPT ![self] = "loop5"]
                     ELSE /\ networkWrite4' = mailboxes
                          /\ mailboxes' = networkWrite4'
                          /\ pc' = [pc EXCEPT ![self] = "N1"]
                          /\ UNCHANGED << networkWrite, networkWrite3, idx >>
               /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                               networkWrite2, valuesRead, valuesWrite, 
                               networkWrite5, networkRead, networkWrite6, 
                               networkWrite7, networkWrite8, ifResult, 
                               appliedWrite, appliedWrite0, appliedWrite1, 
                               networkWrite9, networkWrite10, appliedWrite2, 
                               ifResult0, appliedWrite3, networkWrite11, 
                               appliedWrite4, networkWrite12, networkWrite13, 
                               appliedWrite5, appliedWrite6, networkWrite14, 
                               appliedWrite7, networkWrite15, appliedLocal, 
                               valuesLocal, timeoutLocal, currentTerm, 
                               votedFor, log, state, commitIndex, lastApplied, 
                               v, nextIndex, matchIndex, votes, msg >>

N1(self) == /\ pc[self] = "N1"
            /\ (Len(mailboxes[self])) > (0)
            /\ LET msg1 == Head(mailboxes[self]) IN
                 /\ networkWrite' = [mailboxes EXCEPT ![self] = Tail(mailboxes[self])]
                 /\ networkRead' = msg1
            /\ msg' = [msg EXCEPT ![self] = networkRead']
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N1a"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkWrite6, networkWrite7, networkWrite8, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite9, networkWrite10, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite11, appliedWrite4, networkWrite12, 
                            networkWrite13, appliedWrite5, appliedWrite6, 
                            networkWrite14, appliedWrite7, networkWrite15, 
                            appliedLocal, valuesLocal, timeoutLocal, 
                            currentTerm, votedFor, log, state, commitIndex, 
                            lastApplied, v, nextIndex, matchIndex, idx, votes >>

N1a(self) == /\ pc[self] = "N1a"
             /\ IF ((msg[self]).type) = (AppendEntries)
                   THEN /\ IF ((msg[self]).term) < (currentTerm[self])
                              THEN /\ pc' = [pc EXCEPT ![self] = "N2"]
                                   /\ UNCHANGED << mailboxes, networkWrite6, 
                                                   networkWrite7, 
                                                   networkWrite8, log >>
                              ELSE /\ IF ((((msg[self]).prevIndex) > (0)) /\ ((Len(log[self])) < ((msg[self]).prevIndex))) \/ ((Term(log[self], (msg[self]).prevIndex)) # ((msg[self]).prevTerm))
                                         THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg[self]).prevIndex) - (1))]
                                              /\ pc' = [pc EXCEPT ![self] = "N3"]
                                              /\ UNCHANGED << mailboxes, 
                                                              networkWrite6, 
                                                              networkWrite7, 
                                                              networkWrite8 >>
                                         ELSE /\ IF (Len(log[self])) = ((msg[self]).prevIndex)
                                                    THEN /\ log' = [log EXCEPT ![self] = (log[self]) \o ((msg[self]).entries)]
                                                         /\ pc' = [pc EXCEPT ![self] = "N4"]
                                                         /\ UNCHANGED << mailboxes, 
                                                                         networkWrite6, 
                                                                         networkWrite7, 
                                                                         networkWrite8 >>
                                                    ELSE /\ networkWrite6' = mailboxes
                                                         /\ networkWrite7' = networkWrite6'
                                                         /\ networkWrite8' = networkWrite7'
                                                         /\ mailboxes' = networkWrite8'
                                                         /\ pc' = [pc EXCEPT ![self] = "N5"]
                                                         /\ log' = log
                        /\ UNCHANGED << ifResult0, appliedWrite4, 
                                        networkWrite12, networkWrite13, 
                                        appliedWrite5, appliedWrite6, 
                                        networkWrite14, appliedLocal, state, 
                                        nextIndex, matchIndex, votes >>
                   ELSE /\ IF ((msg[self]).type) = (RequestVote)
                              THEN /\ IF ((msg[self]).term) < (currentTerm[self])
                                         THEN /\ pc' = [pc EXCEPT ![self] = "N6"]
                                         ELSE /\ IF (((votedFor[self]) = (Nil)) \/ ((votedFor[self]) = ((msg[self]).sender))) /\ ((((msg[self]).prevTerm) > (Term(log[self], Len(log[self])))) \/ ((((msg[self]).prevTerm) = (Term(log[self], Len(log[self])))) /\ (((msg[self]).prevIndex) >= (Len(log[self])))))
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "N7"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "N8"]
                                   /\ UNCHANGED << mailboxes, ifResult0, 
                                                   appliedWrite4, 
                                                   networkWrite12, 
                                                   networkWrite13, 
                                                   appliedWrite5, 
                                                   appliedWrite6, 
                                                   networkWrite14, 
                                                   appliedLocal, state, 
                                                   nextIndex, matchIndex, 
                                                   votes >>
                              ELSE /\ IF ((msg[self]).type) = (AppendEntriesResponse)
                                         THEN /\ IF ((msg[self]).granted) /\ ((state[self]) = (Leader))
                                                    THEN /\ nextIndex' = [nextIndex EXCEPT ![self][(msg[self]).sender] = ((msg[self]).prevIndex) + (1)]
                                                         /\ matchIndex' = [matchIndex EXCEPT ![self][(msg[self]).sender] = (msg[self]).prevIndex]
                                                         /\ pc' = [pc EXCEPT ![self] = "loop2"]
                                                         /\ UNCHANGED ifResult0
                                                    ELSE /\ IF ((nextIndex[self][(msg[self]).sender]) - (1)) > (1)
                                                               THEN /\ ifResult0' = (nextIndex[self][(msg[self]).sender]) - (1)
                                                               ELSE /\ ifResult0' = 1
                                                         /\ nextIndex' = [nextIndex EXCEPT ![self][(msg[self]).sender] = ifResult0']
                                                         /\ pc' = [pc EXCEPT ![self] = "N9"]
                                                         /\ UNCHANGED matchIndex
                                              /\ UNCHANGED << mailboxes, 
                                                              appliedWrite4, 
                                                              networkWrite12, 
                                                              networkWrite13, 
                                                              appliedWrite5, 
                                                              appliedWrite6, 
                                                              networkWrite14, 
                                                              appliedLocal, 
                                                              state, votes >>
                                         ELSE /\ IF ((msg[self]).type) = (RequestVoteResponse)
                                                    THEN /\ IF ((msg[self]).granted) /\ ((state[self]) = (Candidate))
                                                               THEN /\ votes' = [votes EXCEPT ![self][(msg[self]).term] = (votes[self][(msg[self]).term]) \union ({(msg[self]).sender})]
                                                                    /\ IF ((Cardinality(votes'[self][(msg[self]).term])) * (2)) > (Cardinality(Servers))
                                                                          THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                               /\ matchIndex' = [matchIndex EXCEPT ![self] = [s3 \in Servers |-> 0]]
                                                                               /\ nextIndex' = [nextIndex EXCEPT ![self] = [s4 \in Servers |-> 1]]
                                                                               /\ appliedWrite4' = appliedLocal[self]
                                                                               /\ networkWrite12' = mailboxes
                                                                               /\ networkWrite13' = networkWrite12'
                                                                               /\ appliedWrite5' = appliedWrite4'
                                                                               /\ appliedWrite6' = appliedWrite5'
                                                                               /\ networkWrite14' = networkWrite13'
                                                                               /\ mailboxes' = networkWrite14'
                                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                               /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                          ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                               /\ networkWrite12' = mailboxes
                                                                               /\ networkWrite13' = networkWrite12'
                                                                               /\ appliedWrite5' = appliedWrite4'
                                                                               /\ appliedWrite6' = appliedWrite5'
                                                                               /\ networkWrite14' = networkWrite13'
                                                                               /\ mailboxes' = networkWrite14'
                                                                               /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                               /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                               /\ UNCHANGED << state, 
                                                                                               nextIndex, 
                                                                                               matchIndex >>
                                                               ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                    /\ networkWrite12' = mailboxes
                                                                    /\ networkWrite13' = networkWrite12'
                                                                    /\ appliedWrite5' = appliedWrite4'
                                                                    /\ appliedWrite6' = appliedWrite5'
                                                                    /\ networkWrite14' = networkWrite13'
                                                                    /\ mailboxes' = networkWrite14'
                                                                    /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                    /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                    /\ UNCHANGED << state, 
                                                                                    nextIndex, 
                                                                                    matchIndex, 
                                                                                    votes >>
                                                    ELSE /\ appliedWrite4' = appliedLocal[self]
                                                         /\ networkWrite12' = mailboxes
                                                         /\ networkWrite13' = networkWrite12'
                                                         /\ appliedWrite5' = appliedWrite4'
                                                         /\ appliedWrite6' = appliedWrite5'
                                                         /\ networkWrite14' = networkWrite13'
                                                         /\ mailboxes' = networkWrite14'
                                                         /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                         /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                         /\ UNCHANGED << state, 
                                                                         nextIndex, 
                                                                         matchIndex, 
                                                                         votes >>
                                              /\ UNCHANGED ifResult0
                        /\ UNCHANGED << networkWrite6, networkWrite7, 
                                        networkWrite8, log >>
             /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                             networkWrite1, networkWrite2, valuesRead, 
                             valuesWrite, networkWrite3, networkWrite4, 
                             networkWrite5, networkRead, ifResult, 
                             appliedWrite, appliedWrite0, appliedWrite1, 
                             networkWrite9, networkWrite10, appliedWrite2, 
                             appliedWrite3, networkWrite11, appliedWrite7, 
                             networkWrite15, valuesLocal, timeoutLocal, 
                             currentTerm, votedFor, commitIndex, lastApplied, 
                             v, idx, msg >>

N5(self) == /\ pc[self] = "N5"
            /\ IF ((msg[self]).term) > (currentTerm[self])
                  THEN /\ state' = [state EXCEPT ![self] = Follower]
                       /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
                  ELSE /\ TRUE
                       /\ UNCHANGED << currentTerm, state >>
            /\ IF ((msg[self]).commit) > (commitIndex[self])
                  THEN /\ IF ((msg[self]).commit) < (Len(log[self]))
                             THEN /\ ifResult' = (msg[self]).commit
                             ELSE /\ ifResult' = Len(log[self])
                       /\ commitIndex' = [commitIndex EXCEPT ![self] = ifResult']
                       /\ pc' = [pc EXCEPT ![self] = "loop1"]
                       /\ UNCHANGED << appliedWrite1, appliedLocal >>
                  ELSE /\ appliedWrite1' = appliedLocal[self]
                       /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite1']
                       /\ pc' = [pc EXCEPT ![self] = "Start"]
                       /\ UNCHANGED << ifResult, commitIndex >>
            /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                            networkWrite0, networkWrite1, networkWrite2, 
                            valuesRead, valuesWrite, networkWrite3, 
                            networkWrite4, networkWrite5, networkRead, 
                            networkWrite6, networkWrite7, networkWrite8, 
                            appliedWrite, appliedWrite0, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, valuesLocal, timeoutLocal, 
                            votedFor, log, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

loop1(self) == /\ pc[self] = "loop1"
               /\ IF (lastApplied[self]) < (commitIndex[self])
                     THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied'[self]] = (appliedLocal[self][lastApplied'[self]]) \union ({log[self][lastApplied'[self]]})]
                          /\ appliedWrite0' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "loop1"]
                     ELSE /\ appliedWrite0' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, networkWrite2, 
                               valuesRead, valuesWrite, networkWrite3, 
                               networkWrite4, networkWrite5, networkRead, 
                               networkWrite6, networkWrite7, networkWrite8, 
                               ifResult, appliedWrite1, networkWrite9, 
                               networkWrite10, appliedWrite2, ifResult0, 
                               appliedWrite3, networkWrite11, appliedWrite4, 
                               networkWrite12, networkWrite13, appliedWrite5, 
                               appliedWrite6, networkWrite14, appliedWrite7, 
                               networkWrite15, valuesLocal, timeoutLocal, 
                               currentTerm, votedFor, log, state, commitIndex, 
                               v, nextIndex, matchIndex, idx, votes, msg >>

N2(self) == /\ pc[self] = "N2"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

N3(self) == /\ pc[self] = "N3"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

N4(self) == /\ pc[self] = "N4"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg[self]).prevIndex) + (Len((msg[self]).entries)), prevTerm |-> Nil, commit |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

N6(self) == /\ pc[self] = "N6"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

N7(self) == /\ pc[self] = "N7"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
            /\ votedFor' = [votedFor EXCEPT ![self] = (msg[self]).sender]
            /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, log, state, commitIndex, lastApplied, 
                            v, nextIndex, matchIndex, idx, votes, msg >>

N8(self) == /\ pc[self] = "N8"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> (msg[self]).term, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil, commit |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

loop2(self) == /\ pc[self] = "loop2"
               /\ IF (((Cardinality({i \in Servers : (matchIndex[self][i]) > (commitIndex[self])})) * (2)) > (Cardinality(Servers))) /\ ((Term(log[self], (commitIndex[self]) + (1))) = (currentTerm[self]))
                     THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (commitIndex[self]) + (1)]
                          /\ pc' = [pc EXCEPT ![self] = "loop2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "loop3"]
                          /\ UNCHANGED commitIndex
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, networkWrite2, 
                               valuesRead, valuesWrite, networkWrite3, 
                               networkWrite4, networkWrite5, networkRead, 
                               networkWrite6, networkWrite7, networkWrite8, 
                               ifResult, appliedWrite, appliedWrite0, 
                               appliedWrite1, networkWrite9, networkWrite10, 
                               appliedWrite2, ifResult0, appliedWrite3, 
                               networkWrite11, appliedWrite4, networkWrite12, 
                               networkWrite13, appliedWrite5, appliedWrite6, 
                               networkWrite14, appliedWrite7, networkWrite15, 
                               appliedLocal, valuesLocal, timeoutLocal, 
                               currentTerm, votedFor, log, state, lastApplied, 
                               v, nextIndex, matchIndex, idx, votes, msg >>

loop3(self) == /\ pc[self] = "loop3"
               /\ IF (lastApplied[self]) < (commitIndex[self])
                     THEN /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied'[self]] = (appliedLocal[self][lastApplied'[self]]) \union ({log[self][lastApplied'[self]]})]
                          /\ appliedWrite2' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "loop3"]
                     ELSE /\ appliedWrite2' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, networkWrite2, 
                               valuesRead, valuesWrite, networkWrite3, 
                               networkWrite4, networkWrite5, networkRead, 
                               networkWrite6, networkWrite7, networkWrite8, 
                               ifResult, appliedWrite0, appliedWrite1, 
                               networkWrite9, networkWrite10, ifResult0, 
                               appliedWrite3, networkWrite11, appliedWrite4, 
                               networkWrite12, networkWrite13, appliedWrite5, 
                               appliedWrite6, networkWrite14, appliedWrite7, 
                               networkWrite15, valuesLocal, timeoutLocal, 
                               currentTerm, votedFor, log, state, commitIndex, 
                               v, nextIndex, matchIndex, idx, votes, msg >>

N9(self) == /\ pc[self] = "N9"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [type |-> RequestVote, term |-> currentTerm[self], sender |-> self, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), granted |-> FALSE, commit |-> commitIndex[self]])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            networkWrite2, valuesRead, valuesWrite, 
                            networkWrite3, networkWrite4, networkWrite5, 
                            networkRead, networkWrite6, networkWrite7, 
                            networkWrite8, ifResult, appliedWrite, 
                            appliedWrite0, appliedWrite1, networkWrite9, 
                            networkWrite10, appliedWrite2, ifResult0, 
                            appliedWrite3, networkWrite11, appliedWrite4, 
                            networkWrite12, networkWrite13, appliedWrite5, 
                            appliedWrite6, networkWrite14, appliedWrite7, 
                            networkWrite15, appliedLocal, valuesLocal, 
                            timeoutLocal, currentTerm, votedFor, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

server(self) == Start(self) \/ N10(self) \/ loop4(self) \/ N11(self)
                   \/ loop5(self) \/ N1(self) \/ N1a(self) \/ N5(self)
                   \/ loop1(self) \/ N2(self) \/ N3(self) \/ N4(self)
                   \/ N6(self) \/ N7(self) \/ N8(self) \/ loop2(self)
                   \/ loop3(self) \/ N9(self)

Next == (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

StateMachineCorrectness == \A i,j \in Servers :
                            \A k \in 1..(IF commitIndex[i] < commitIndex[j] THEN commitIndex[i] ELSE commitIndex[j]):
                                log[i][k] = log[j][k] 
                                
ElectionSafety == \A i,j \in Servers :
                   (currentTerm[i] = currentTerm[j] /\ i # j) => state[i] # Leader \/ state[j] # Leader

LogMatching == \A i,j \in Servers :
                \A k \in 1..((IF Len(log[i]) < Len(log[j]) THEN Len(log[i]) ELSE Len(log[j]))-1):
                  log[i][k] = log[j][k] => \A l \in 1..k : log[i][l] = log[j][l]

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
