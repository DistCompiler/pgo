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
        Term(log,index) == (IF Len(log) >= index /\ Len(log) > 0 THEN log[index].term ELSE 0)
    }
    
    macro SendRequestVotes(network, cterm, candidateId, lastLogIndex, lastLogTerm, idx) {
        while (idx <= Cardinality(Servers)) {
            network[idx] := [sender |-> candidateId, type |-> RequestVote, term |-> cterm, granted |-> FALSE, entries |-> <<>>,
                             prevIndex |-> lastLogIndex, prevTerm |-> lastLogTerm];
            idx := idx + 1;
        };
    }
    
    macro SendAppendEntries(network, cterm, candidateId, nextIndex, matchIndex, log, leaderCommit, idx) {
        while (idx <= Cardinality(Servers)) {
            if (idx # candidateId) {
                network[idx] := [sender |-> candidateId, type |-> RequestVote, term |-> cterm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)),
                                 prevIndex |-> nextIndex[idx]-1, prevTerm |-> Term(log, nextIndex[idx]-1)];
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
            print <<"Applying", $value>>;
            yield $variable \union {$value};
        }
    }
    
    mapping macro Timeout {
        read {
            either { yield FALSE } or { yield TRUE }
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
            \*votedFor := self;
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
        if (msg.type = AppendEntries) {
            if (msg.term < currentTerm) {
N2:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
            } elseif (Len(log) < msg.prevIndex \/ log[msg.prevIndex].term # msg.prevTerm) {
                \* Following entries don't have matching terms
                log := SubSeq(log,1,msg.prevIndex-1);
N3:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
            } elseif (Len(log) = msg.prevIndex) {
                log := log \o msg.entries;
N4:             network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> msg.prevIndex + Len(msg.entries), prevTerm |-> Nil];
            };

N5:         if (msg.term > currentTerm) {
                state := Follower;
                currentTerm := msg.term;
            };

            if (msg.leaderCommit > commitIndex) {
                commitIndex := IF msg.leaderCommit < Len(log) THEN msg.leaderCommit ELSE Len(log[self]);
loop1:          while(lastApplied <= commitIndex) {
                    applied[lastApplied] := log[lastApplied];
                    lastApplied := lastApplied + 1;
                };
            };
        } elseif (msg.type = RequestVote) {
            if (msg.term < currentTerm) {
N6:             network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
            } elseif ((votedFor = Nil \/ votedFor = msg.sender)
                     /\ (msg.prevTerm > Term(log, Len(log))
                         \/ (msg.prevTerm = Term(log, Len(log)) /\ msg.prevIndex >= Len(log)))) {
                log := SubSeq(log, 1, msg.prevIndex-1);
 N7:            network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> TRUE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
                votedFor := msg.sender;
            } else {
 N8:            network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE,
                                        entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
            }
        } elseif (msg.type = AppendEntriesResponse /\ state = Leader) {
            if (msg.granted) {
                nextIndex[msg.sender] := msg.prevIndex + 1;
                matchIndex[msg.sender] := msg.prevIndex;
loop2:          while (Cardinality({i \in Servers: matchIndex[idx] > commitIndex})*2 > Cardinality(Servers) /\ Term(log, commitIndex+1) = currentTerm) {
                    commitIndex := commitIndex + 1;
                };
loop3:          while(lastApplied <= commitIndex) {
                    applied[lastApplied] := log[lastApplied];
                    lastApplied := lastApplied + 1;
                };
            } else {
                nextIndex[msg.sender] := IF nextIndex[msg.sender] - 1 > 1 THEN nextIndex[msg.sender] - 1 ELSE 1;
N9:             network[msg.sender] := [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, nextIndex[msg.sender], Len(log)),
                                        prevIndex |-> nextIndex[msg.sender]-1, prevTerm |-> Term(log, nextIndex[msg.sender]-1), granted |-> FALSE];
            };
        } elseif (msg.type = RequestVoteResponse) {
            if (msg.granted /\ state = Candidate) {
                votes[msg.term] := votes[msg.term] \union {msg.sender};
                if (Cardinality(votes[msg.term])*2 > Cardinality(Servers)) {
                    state := Leader;
                    matchIndex := [s3 \in Servers |-> 0];
                    nextIndex := [s4 \in Servers |-> 0];
                };
            };
        };
      };
    }
    
    
    variables
        mailboxes = [id \in Servers |-> <<>>];

    fair process (server \in Servers) == instance Node(ref mailboxes, [s \in 0..Slots |-> {}], <<1,2,3,4,5>>, Nil)
        mapping mailboxes[_] via FIFOChannel
        mapping @2[_] via Log
        mapping @3 via Input
        mapping @4 via Timeout;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm Raft {
    variables mailboxes = [id \in Servers |-> <<>>], timeoutRead, networkWrite, networkWrite0, networkWrite1, valuesRead, valuesWrite, networkWrite2, networkWrite3, networkWrite4, networkRead, networkWrite5, networkWrite6, networkWrite7, ifResult, appliedWrite, appliedWrite0, appliedWrite1, networkWrite8, networkWrite9, appliedWrite2, ifResult0, appliedWrite3, networkWrite10, appliedWrite4, networkWrite11, networkWrite12, appliedWrite5, appliedWrite6, networkWrite13, appliedWrite7, networkWrite14;
    define {
        Servers == (1) .. (N)
        Follower == 0
        Candidate == 1
        Leader == 2
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        Term(log, index) == IF ((Len(log)) >= (index)) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0
    }
    fair process (server \in Servers)
    variables appliedLocal = [s \in (0) .. (Slots) |-> {}], valuesLocal = <<1, 2, 3, 4, 5>>, currentTerm = 0, votedFor = Nil, log = <<>>, state = Follower, commitIndex = 0, lastApplied = 0, v, nextIndex, matchIndex, idx, votes = [t \in (0) .. (Terms) |-> {}], msg;
    {
        Start:
            if (((commitIndex) < (Slots)) /\ ((currentTerm) < (Terms))) {
                N10:
                    either {
                        timeoutRead := FALSE;
                    } or {
                        timeoutRead := TRUE;
                    };
                    if (((state) # (Leader)) /\ (timeoutRead)) {
                        state := Candidate;
                        currentTerm := (currentTerm) + (1);
                        votes[currentTerm] := {self};
                        idx := 1;
                        loop4:
                            if ((idx) <= (Cardinality(Servers))) {
                                await (Len(mailboxes[idx])) < (BUFFER_SIZE);
                                networkWrite := [mailboxes EXCEPT ![idx] = Append(mailboxes[idx], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log))])];
                                idx := (idx) + (1);
                                networkWrite0 := networkWrite;
                                mailboxes := networkWrite0;
                                goto loop4;
                            } else {
                                networkWrite0 := mailboxes;
                                mailboxes := networkWrite0;
                            };
                    
                    } else {
                        networkWrite1 := mailboxes;
                        mailboxes := networkWrite1;
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
                                    networkWrite := [mailboxes EXCEPT ![idx] = Append(mailboxes[idx], [sender |-> self, type |-> RequestVote, term |-> currentTerm, granted |-> FALSE, entries |-> SubSeq(log, nextIndex[idx], Len(log)), prevIndex |-> (nextIndex[idx]) - (1), prevTerm |-> Term(log, (nextIndex[idx]) - (1))])];
                                    networkWrite2 := networkWrite;
                                } else {
                                    networkWrite2 := mailboxes;
                                };
                                idx := (idx) + (1);
                                networkWrite3 := networkWrite2;
                                mailboxes := networkWrite3;
                                goto loop5;
                            } else {
                                networkWrite3 := mailboxes;
                                mailboxes := networkWrite3;
                            };
                    
                    } else {
                        networkWrite4 := mailboxes;
                        mailboxes := networkWrite4;
                    };
                
                N1:
                    await (Len(mailboxes[self])) > (0);
                    with (msg1 = Head(mailboxes[self])) {
                        networkWrite := [mailboxes EXCEPT ![self] = Tail(mailboxes[self])];
                        networkRead := msg1;
                    };
                    msg := networkRead;
                    if (((msg).type) = (AppendEntries)) {
                        if (((msg).term) < (currentTerm)) {
                            mailboxes := networkWrite;
                            N2:
                                await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])];
                                mailboxes := networkWrite;
                        
                        } else {
                            if (((Len(log)) < ((msg).prevIndex)) \/ (((log[(msg).prevIndex]).term) # ((msg).prevTerm))) {
                                log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                                N3:
                                    await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])];
                                    mailboxes := networkWrite;
                            
                            } else {
                                if ((Len(log)) = ((msg).prevIndex)) {
                                    log := (log) \o ((msg).entries);
                                    N4:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg).prevIndex) + (Len((msg).entries)), prevTerm |-> Nil])];
                                        mailboxes := networkWrite;
                                
                                } else {
                                    networkWrite5 := mailboxes;
                                    networkWrite6 := networkWrite5;
                                    networkWrite7 := networkWrite6;
                                    mailboxes := networkWrite7;
                                };
                            };
                        };
                        N5:
                            if (((msg).term) > (currentTerm)) {
                                state := Follower;
                                currentTerm := (msg).term;
                            };
                            if (((msg).leaderCommit) > (commitIndex)) {
                                if (((msg).leaderCommit) < (Len(log))) {
                                    ifResult := (msg).leaderCommit;
                                } else {
                                    ifResult := Len(log[self]);
                                };
                                commitIndex := ifResult;
                                loop1:
                                    if ((lastApplied) <= (commitIndex)) {
                                        print <<"Applying", log[lastApplied]>>;
                                        appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
                                        lastApplied := (lastApplied) + (1);
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
                                    networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])];
                                    mailboxes := networkWrite;
                                    goto Start;
                            
                            } else {
                                if ((((votedFor) = (Nil)) \/ ((votedFor) = ((msg).sender))) /\ ((((msg).prevTerm) > (Term(log, Len(log)))) \/ ((((msg).prevTerm) = (Term(log, Len(log)))) /\ (((msg).prevIndex) >= (Len(log)))))) {
                                    log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                                    N7:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])];
                                        votedFor := (msg).sender;
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                } else {
                                    N8:
                                        await (Len(mailboxes[(msg).sender])) < (BUFFER_SIZE);
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])];
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                };
                            };
                        } else {
                            if ((((msg).type) = (AppendEntriesResponse)) /\ ((state) = (Leader))) {
                                if ((msg).granted) {
                                    nextIndex[(msg).sender] := ((msg).prevIndex) + (1);
                                    matchIndex[(msg).sender] := (msg).prevIndex;
                                    loop2:
                                        if ((((Cardinality({i \in Servers : (matchIndex[idx]) > (commitIndex)})) * (2)) > (Cardinality(Servers))) /\ ((Term(log, (commitIndex) + (1))) = (currentTerm))) {
                                            commitIndex := (commitIndex) + (1);
                                            goto loop2;
                                        };
                                    
                                    loop3:
                                        if ((lastApplied) <= (commitIndex)) {
                                            print <<"Applying", log[lastApplied]>>;
                                            appliedWrite := [appliedLocal EXCEPT ![lastApplied] = (appliedLocal[lastApplied]) \union ({log[lastApplied]})];
                                            lastApplied := (lastApplied) + (1);
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
                                        networkWrite := [mailboxes EXCEPT ![(msg).sender] = Append(mailboxes[(msg).sender], [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, nextIndex[(msg).sender], Len(log)), prevIndex |-> (nextIndex[(msg).sender]) - (1), prevTerm |-> Term(log, (nextIndex[(msg).sender]) - (1)), granted |-> FALSE])];
                                        mailboxes := networkWrite;
                                        goto Start;
                                
                                };
                            } else {
                                if (((msg).type) = (RequestVoteResponse)) {
                                    if (((msg).granted) /\ ((state) = (Candidate))) {
                                        votes[(msg).term] := (votes[(msg).term]) \union ({(msg).sender});
                                        if (((Cardinality(votes[(msg).term])) * (2)) > (Cardinality(Servers))) {
                                            print "And here!";
                                            state := Leader;
                                            matchIndex := [s3 \in Servers |-> 0];
                                            nextIndex := [s4 \in Servers |-> 0];
                                            appliedWrite4 := appliedLocal;
                                            networkWrite11 := mailboxes;
                                            networkWrite12 := networkWrite11;
                                            appliedWrite5 := appliedWrite4;
                                            appliedWrite6 := appliedWrite5;
                                            networkWrite13 := networkWrite12;
                                            mailboxes := networkWrite13;
                                            appliedLocal := appliedWrite6;
                                            goto Start;
                                        } else {
                                            appliedWrite4 := appliedLocal;
                                            networkWrite11 := mailboxes;
                                            networkWrite12 := networkWrite11;
                                            appliedWrite5 := appliedWrite4;
                                            appliedWrite6 := appliedWrite5;
                                            networkWrite13 := networkWrite12;
                                            mailboxes := networkWrite13;
                                            appliedLocal := appliedWrite6;
                                            goto Start;
                                        };
                                    } else {
                                        appliedWrite4 := appliedLocal;
                                        networkWrite11 := mailboxes;
                                        networkWrite12 := networkWrite11;
                                        appliedWrite5 := appliedWrite4;
                                        appliedWrite6 := appliedWrite5;
                                        networkWrite13 := networkWrite12;
                                        mailboxes := networkWrite13;
                                        appliedLocal := appliedWrite6;
                                        goto Start;
                                    };
                                } else {
                                    appliedWrite4 := appliedLocal;
                                    networkWrite11 := mailboxes;
                                    networkWrite12 := networkWrite11;
                                    appliedWrite5 := appliedWrite4;
                                    appliedWrite6 := appliedWrite5;
                                    networkWrite13 := networkWrite12;
                                    mailboxes := networkWrite13;
                                    appliedLocal := appliedWrite6;
                                    goto Start;
                                };
                            };
                        };
                    };
            
            } else {
                appliedWrite7 := appliedLocal;
                networkWrite14 := mailboxes;
                mailboxes := networkWrite14;
                appliedLocal := appliedWrite7;
            };
    
    }
}
\* END PLUSCAL TRANSLATION

******************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
          valuesRead, valuesWrite, networkWrite2, networkWrite3, 
          networkWrite4, networkRead, networkWrite5, networkWrite6, 
          networkWrite7, ifResult, appliedWrite, appliedWrite0, appliedWrite1, 
          networkWrite8, networkWrite9, appliedWrite2, ifResult0, 
          appliedWrite3, networkWrite10, appliedWrite4, networkWrite11, 
          networkWrite12, appliedWrite5, appliedWrite6, networkWrite13, 
          appliedWrite7, networkWrite14, pc

(* define statement *)
Servers == (1) .. (N)
Follower == 0
Candidate == 1
Leader == 2
RequestVote == 0
RequestVoteResponse == 1
AppendEntries == 2
AppendEntriesResponse == 3
Term(log, index) == IF ((Len(log)) >= (index)) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0

VARIABLES appliedLocal, valuesLocal, currentTerm, votedFor, log, state, 
          commitIndex, lastApplied, v, nextIndex, matchIndex, idx, votes, msg

vars == << mailboxes, timeoutRead, networkWrite, networkWrite0, networkWrite1, 
           valuesRead, valuesWrite, networkWrite2, networkWrite3, 
           networkWrite4, networkRead, networkWrite5, networkWrite6, 
           networkWrite7, ifResult, appliedWrite, appliedWrite0, 
           appliedWrite1, networkWrite8, networkWrite9, appliedWrite2, 
           ifResult0, appliedWrite3, networkWrite10, appliedWrite4, 
           networkWrite11, networkWrite12, appliedWrite5, appliedWrite6, 
           networkWrite13, appliedWrite7, networkWrite14, pc, appliedLocal, 
           valuesLocal, currentTerm, votedFor, log, state, commitIndex, 
           lastApplied, v, nextIndex, matchIndex, idx, votes, msg >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ mailboxes = [id \in Servers |-> <<>>]
        /\ timeoutRead = defaultInitValue
        /\ networkWrite = defaultInitValue
        /\ networkWrite0 = defaultInitValue
        /\ networkWrite1 = defaultInitValue
        /\ valuesRead = defaultInitValue
        /\ valuesWrite = defaultInitValue
        /\ networkWrite2 = defaultInitValue
        /\ networkWrite3 = defaultInitValue
        /\ networkWrite4 = defaultInitValue
        /\ networkRead = defaultInitValue
        /\ networkWrite5 = defaultInitValue
        /\ networkWrite6 = defaultInitValue
        /\ networkWrite7 = defaultInitValue
        /\ ifResult = defaultInitValue
        /\ appliedWrite = defaultInitValue
        /\ appliedWrite0 = defaultInitValue
        /\ appliedWrite1 = defaultInitValue
        /\ networkWrite8 = defaultInitValue
        /\ networkWrite9 = defaultInitValue
        /\ appliedWrite2 = defaultInitValue
        /\ ifResult0 = defaultInitValue
        /\ appliedWrite3 = defaultInitValue
        /\ networkWrite10 = defaultInitValue
        /\ appliedWrite4 = defaultInitValue
        /\ networkWrite11 = defaultInitValue
        /\ networkWrite12 = defaultInitValue
        /\ appliedWrite5 = defaultInitValue
        /\ appliedWrite6 = defaultInitValue
        /\ networkWrite13 = defaultInitValue
        /\ appliedWrite7 = defaultInitValue
        /\ networkWrite14 = defaultInitValue
        (* Process server *)
        /\ appliedLocal = [self \in Servers |-> [s \in (0) .. (Slots) |-> {}]]
        /\ valuesLocal = [self \in Servers |-> <<1, 2, 3, 4, 5>>]
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
                                          networkWrite14, appliedLocal >>
                     ELSE /\ appliedWrite7' = appliedLocal[self]
                          /\ networkWrite14' = mailboxes
                          /\ mailboxes' = networkWrite14'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite7']
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                               networkWrite1, valuesRead, valuesWrite, 
                               networkWrite2, networkWrite3, networkWrite4, 
                               networkRead, networkWrite5, networkWrite6, 
                               networkWrite7, ifResult, appliedWrite, 
                               appliedWrite0, appliedWrite1, networkWrite8, 
                               networkWrite9, appliedWrite2, ifResult0, 
                               appliedWrite3, networkWrite10, appliedWrite4, 
                               networkWrite11, networkWrite12, appliedWrite5, 
                               appliedWrite6, networkWrite13, valuesLocal, 
                               currentTerm, votedFor, log, state, commitIndex, 
                               lastApplied, v, nextIndex, matchIndex, idx, 
                               votes, msg >>

N10(self) == /\ pc[self] = "N10"
             /\ \/ /\ timeoutRead' = FALSE
                \/ /\ timeoutRead' = TRUE
             /\ IF ((state[self]) # (Leader)) /\ (timeoutRead')
                   THEN /\ state' = [state EXCEPT ![self] = Candidate]
                        /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                        /\ votes' = [votes EXCEPT ![self][currentTerm'[self]] = {self}]
                        /\ idx' = [idx EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "loop4"]
                        /\ UNCHANGED << mailboxes, networkWrite1 >>
                   ELSE /\ networkWrite1' = mailboxes
                        /\ mailboxes' = networkWrite1'
                        /\ pc' = [pc EXCEPT ![self] = "N11"]
                        /\ UNCHANGED << currentTerm, state, idx, votes >>
             /\ UNCHANGED << networkWrite, networkWrite0, valuesRead, 
                             valuesWrite, networkWrite2, networkWrite3, 
                             networkWrite4, networkRead, networkWrite5, 
                             networkWrite6, networkWrite7, ifResult, 
                             appliedWrite, appliedWrite0, appliedWrite1, 
                             networkWrite8, networkWrite9, appliedWrite2, 
                             ifResult0, appliedWrite3, networkWrite10, 
                             appliedWrite4, networkWrite11, networkWrite12, 
                             appliedWrite5, appliedWrite6, networkWrite13, 
                             appliedWrite7, networkWrite14, appliedLocal, 
                             valuesLocal, votedFor, log, commitIndex, 
                             lastApplied, v, nextIndex, matchIndex, msg >>

loop4(self) == /\ pc[self] = "loop4"
               /\ IF (idx[self]) <= (Cardinality(Servers))
                     THEN /\ (Len(mailboxes[idx[self]])) < (BUFFER_SIZE)
                          /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self]))])]
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite0' = networkWrite'
                          /\ mailboxes' = networkWrite0'
                          /\ pc' = [pc EXCEPT ![self] = "loop4"]
                     ELSE /\ networkWrite0' = mailboxes
                          /\ mailboxes' = networkWrite0'
                          /\ pc' = [pc EXCEPT ![self] = "N11"]
                          /\ UNCHANGED << networkWrite, idx >>
               /\ UNCHANGED << timeoutRead, networkWrite1, valuesRead, 
                               valuesWrite, networkWrite2, networkWrite3, 
                               networkWrite4, networkRead, networkWrite5, 
                               networkWrite6, networkWrite7, ifResult, 
                               appliedWrite, appliedWrite0, appliedWrite1, 
                               networkWrite8, networkWrite9, appliedWrite2, 
                               ifResult0, appliedWrite3, networkWrite10, 
                               appliedWrite4, networkWrite11, networkWrite12, 
                               appliedWrite5, appliedWrite6, networkWrite13, 
                               appliedWrite7, networkWrite14, appliedLocal, 
                               valuesLocal, currentTerm, votedFor, log, state, 
                               commitIndex, lastApplied, v, nextIndex, 
                               matchIndex, votes, msg >>

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
                        /\ UNCHANGED << mailboxes, networkWrite4 >>
                   ELSE /\ networkWrite4' = mailboxes
                        /\ mailboxes' = networkWrite4'
                        /\ pc' = [pc EXCEPT ![self] = "N1"]
                        /\ UNCHANGED << valuesRead, valuesWrite, valuesLocal, 
                                        log, v, nextIndex, matchIndex, idx >>
             /\ UNCHANGED << timeoutRead, networkWrite, networkWrite0, 
                             networkWrite1, networkWrite2, networkWrite3, 
                             networkRead, networkWrite5, networkWrite6, 
                             networkWrite7, ifResult, appliedWrite, 
                             appliedWrite0, appliedWrite1, networkWrite8, 
                             networkWrite9, appliedWrite2, ifResult0, 
                             appliedWrite3, networkWrite10, appliedWrite4, 
                             networkWrite11, networkWrite12, appliedWrite5, 
                             appliedWrite6, networkWrite13, appliedWrite7, 
                             networkWrite14, appliedLocal, currentTerm, 
                             votedFor, state, commitIndex, lastApplied, votes, 
                             msg >>

loop5(self) == /\ pc[self] = "loop5"
               /\ IF (idx[self]) <= (Cardinality(Servers))
                     THEN /\ IF (idx[self]) # (self)
                                THEN /\ (Len(mailboxes[idx[self]])) < (BUFFER_SIZE)
                                     /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [sender |-> self, type |-> RequestVote, term |-> currentTerm[self], granted |-> FALSE, entries |-> SubSeq(log[self], nextIndex[self][idx[self]], Len(log[self])), prevIndex |-> (nextIndex[self][idx[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][idx[self]]) - (1))])]
                                     /\ networkWrite2' = networkWrite'
                                ELSE /\ networkWrite2' = mailboxes
                                     /\ UNCHANGED networkWrite
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite3' = networkWrite2'
                          /\ mailboxes' = networkWrite3'
                          /\ pc' = [pc EXCEPT ![self] = "loop5"]
                     ELSE /\ networkWrite3' = mailboxes
                          /\ mailboxes' = networkWrite3'
                          /\ pc' = [pc EXCEPT ![self] = "N1"]
                          /\ UNCHANGED << networkWrite, networkWrite2, idx >>
               /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                               valuesRead, valuesWrite, networkWrite4, 
                               networkRead, networkWrite5, networkWrite6, 
                               networkWrite7, ifResult, appliedWrite, 
                               appliedWrite0, appliedWrite1, networkWrite8, 
                               networkWrite9, appliedWrite2, ifResult0, 
                               appliedWrite3, networkWrite10, appliedWrite4, 
                               networkWrite11, networkWrite12, appliedWrite5, 
                               appliedWrite6, networkWrite13, appliedWrite7, 
                               networkWrite14, appliedLocal, valuesLocal, 
                               currentTerm, votedFor, log, state, commitIndex, 
                               lastApplied, v, nextIndex, matchIndex, votes, 
                               msg >>

N1(self) == /\ pc[self] = "N1"
            /\ (Len(mailboxes[self])) > (0)
            /\ LET msg1 == Head(mailboxes[self]) IN
                 /\ networkWrite' = [mailboxes EXCEPT ![self] = Tail(mailboxes[self])]
                 /\ networkRead' = msg1
            /\ msg' = [msg EXCEPT ![self] = networkRead']
            /\ IF ((msg'[self]).type) = (AppendEntries)
                  THEN /\ IF ((msg'[self]).term) < (currentTerm[self])
                             THEN /\ mailboxes' = networkWrite'
                                  /\ pc' = [pc EXCEPT ![self] = "N2"]
                                  /\ UNCHANGED << networkWrite5, networkWrite6, 
                                                  networkWrite7, log >>
                             ELSE /\ IF ((Len(log[self])) < ((msg'[self]).prevIndex)) \/ (((log[self][(msg'[self]).prevIndex]).term) # ((msg'[self]).prevTerm))
                                        THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg'[self]).prevIndex) - (1))]
                                             /\ pc' = [pc EXCEPT ![self] = "N3"]
                                             /\ UNCHANGED << mailboxes, 
                                                             networkWrite5, 
                                                             networkWrite6, 
                                                             networkWrite7 >>
                                        ELSE /\ IF (Len(log[self])) = ((msg'[self]).prevIndex)
                                                   THEN /\ log' = [log EXCEPT ![self] = (log[self]) \o ((msg'[self]).entries)]
                                                        /\ pc' = [pc EXCEPT ![self] = "N4"]
                                                        /\ UNCHANGED << mailboxes, 
                                                                        networkWrite5, 
                                                                        networkWrite6, 
                                                                        networkWrite7 >>
                                                   ELSE /\ networkWrite5' = mailboxes
                                                        /\ networkWrite6' = networkWrite5'
                                                        /\ networkWrite7' = networkWrite6'
                                                        /\ mailboxes' = networkWrite7'
                                                        /\ pc' = [pc EXCEPT ![self] = "N5"]
                                                        /\ log' = log
                       /\ UNCHANGED << ifResult0, appliedWrite4, 
                                       networkWrite11, networkWrite12, 
                                       appliedWrite5, appliedWrite6, 
                                       networkWrite13, appliedLocal, state, 
                                       nextIndex, matchIndex, votes >>
                  ELSE /\ IF ((msg'[self]).type) = (RequestVote)
                             THEN /\ IF ((msg'[self]).term) < (currentTerm[self])
                                        THEN /\ pc' = [pc EXCEPT ![self] = "N6"]
                                             /\ log' = log
                                        ELSE /\ IF (((votedFor[self]) = (Nil)) \/ ((votedFor[self]) = ((msg'[self]).sender))) /\ ((((msg'[self]).prevTerm) > (Term(log[self], Len(log[self])))) \/ ((((msg'[self]).prevTerm) = (Term(log[self], Len(log[self])))) /\ (((msg'[self]).prevIndex) >= (Len(log[self])))))
                                                   THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg'[self]).prevIndex) - (1))]
                                                        /\ pc' = [pc EXCEPT ![self] = "N7"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "N8"]
                                                        /\ log' = log
                                  /\ UNCHANGED << mailboxes, ifResult0, 
                                                  appliedWrite4, 
                                                  networkWrite11, 
                                                  networkWrite12, 
                                                  appliedWrite5, appliedWrite6, 
                                                  networkWrite13, appliedLocal, 
                                                  state, nextIndex, matchIndex, 
                                                  votes >>
                             ELSE /\ IF (((msg'[self]).type) = (AppendEntriesResponse)) /\ ((state[self]) = (Leader))
                                        THEN /\ IF (msg'[self]).granted
                                                   THEN /\ nextIndex' = [nextIndex EXCEPT ![self][(msg'[self]).sender] = ((msg'[self]).prevIndex) + (1)]
                                                        /\ matchIndex' = [matchIndex EXCEPT ![self][(msg'[self]).sender] = (msg'[self]).prevIndex]
                                                        /\ pc' = [pc EXCEPT ![self] = "loop2"]
                                                        /\ UNCHANGED ifResult0
                                                   ELSE /\ IF ((nextIndex[self][(msg'[self]).sender]) - (1)) > (1)
                                                              THEN /\ ifResult0' = (nextIndex[self][(msg'[self]).sender]) - (1)
                                                              ELSE /\ ifResult0' = 1
                                                        /\ nextIndex' = [nextIndex EXCEPT ![self][(msg'[self]).sender] = ifResult0']
                                                        /\ pc' = [pc EXCEPT ![self] = "N9"]
                                                        /\ UNCHANGED matchIndex
                                             /\ UNCHANGED << mailboxes, 
                                                             appliedWrite4, 
                                                             networkWrite11, 
                                                             networkWrite12, 
                                                             appliedWrite5, 
                                                             appliedWrite6, 
                                                             networkWrite13, 
                                                             appliedLocal, 
                                                             state, votes >>
                                        ELSE /\ IF ((msg'[self]).type) = (RequestVoteResponse)
                                                   THEN /\ IF ((msg'[self]).granted) /\ ((state[self]) = (Candidate))
                                                              THEN /\ votes' = [votes EXCEPT ![self][(msg'[self]).term] = (votes[self][(msg'[self]).term]) \union ({(msg'[self]).sender})]
                                                                   /\ IF ((Cardinality(votes'[self][(msg'[self]).term])) * (2)) > (Cardinality(Servers))
                                                                         THEN /\ PrintT("And here!")
                                                                              /\ state' = [state EXCEPT ![self] = Leader]
                                                                              /\ matchIndex' = [matchIndex EXCEPT ![self] = [s3 \in Servers |-> 0]]
                                                                              /\ nextIndex' = [nextIndex EXCEPT ![self] = [s4 \in Servers |-> 0]]
                                                                              /\ appliedWrite4' = appliedLocal[self]
                                                                              /\ networkWrite11' = mailboxes
                                                                              /\ networkWrite12' = networkWrite11'
                                                                              /\ appliedWrite5' = appliedWrite4'
                                                                              /\ appliedWrite6' = appliedWrite5'
                                                                              /\ networkWrite13' = networkWrite12'
                                                                              /\ mailboxes' = networkWrite13'
                                                                              /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                              /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                         ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                              /\ networkWrite11' = mailboxes
                                                                              /\ networkWrite12' = networkWrite11'
                                                                              /\ appliedWrite5' = appliedWrite4'
                                                                              /\ appliedWrite6' = appliedWrite5'
                                                                              /\ networkWrite13' = networkWrite12'
                                                                              /\ mailboxes' = networkWrite13'
                                                                              /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                              /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                              /\ UNCHANGED << state, 
                                                                                              nextIndex, 
                                                                                              matchIndex >>
                                                              ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                   /\ networkWrite11' = mailboxes
                                                                   /\ networkWrite12' = networkWrite11'
                                                                   /\ appliedWrite5' = appliedWrite4'
                                                                   /\ appliedWrite6' = appliedWrite5'
                                                                   /\ networkWrite13' = networkWrite12'
                                                                   /\ mailboxes' = networkWrite13'
                                                                   /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                   /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                   /\ UNCHANGED << state, 
                                                                                   nextIndex, 
                                                                                   matchIndex, 
                                                                                   votes >>
                                                   ELSE /\ appliedWrite4' = appliedLocal[self]
                                                        /\ networkWrite11' = mailboxes
                                                        /\ networkWrite12' = networkWrite11'
                                                        /\ appliedWrite5' = appliedWrite4'
                                                        /\ appliedWrite6' = appliedWrite5'
                                                        /\ networkWrite13' = networkWrite12'
                                                        /\ mailboxes' = networkWrite13'
                                                        /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                        /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                        /\ UNCHANGED << state, 
                                                                        nextIndex, 
                                                                        matchIndex, 
                                                                        votes >>
                                             /\ UNCHANGED ifResult0
                                  /\ log' = log
                       /\ UNCHANGED << networkWrite5, networkWrite6, 
                                       networkWrite7 >>
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, ifResult, 
                            appliedWrite, appliedWrite0, appliedWrite1, 
                            networkWrite8, networkWrite9, appliedWrite2, 
                            appliedWrite3, networkWrite10, appliedWrite7, 
                            networkWrite14, valuesLocal, currentTerm, votedFor, 
                            commitIndex, lastApplied, v, idx >>

N5(self) == /\ pc[self] = "N5"
            /\ IF ((msg[self]).term) > (currentTerm[self])
                  THEN /\ state' = [state EXCEPT ![self] = Follower]
                       /\ currentTerm' = [currentTerm EXCEPT ![self] = (msg[self]).term]
                  ELSE /\ TRUE
                       /\ UNCHANGED << currentTerm, state >>
            /\ IF ((msg[self]).leaderCommit) > (commitIndex[self])
                  THEN /\ IF ((msg[self]).leaderCommit) < (Len(log[self]))
                             THEN /\ ifResult' = (msg[self]).leaderCommit
                             ELSE /\ ifResult' = Len(log[self][self])
                       /\ commitIndex' = [commitIndex EXCEPT ![self] = ifResult']
                       /\ pc' = [pc EXCEPT ![self] = "loop1"]
                       /\ UNCHANGED << appliedWrite1, appliedLocal >>
                  ELSE /\ appliedWrite1' = appliedLocal[self]
                       /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite1']
                       /\ pc' = [pc EXCEPT ![self] = "Start"]
                       /\ UNCHANGED << ifResult, commitIndex >>
            /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                            networkWrite0, networkWrite1, valuesRead, 
                            valuesWrite, networkWrite2, networkWrite3, 
                            networkWrite4, networkRead, networkWrite5, 
                            networkWrite6, networkWrite7, appliedWrite, 
                            appliedWrite0, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            valuesLocal, votedFor, log, lastApplied, v, 
                            nextIndex, matchIndex, idx, votes, msg >>

loop1(self) == /\ pc[self] = "loop1"
               /\ IF (lastApplied[self]) <= (commitIndex[self])
                     THEN /\ PrintT(<<"Applying", log[self][lastApplied[self]]>>)
                          /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied[self]] = (appliedLocal[self][lastApplied[self]]) \union ({log[self][lastApplied[self]]})]
                          /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite0' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "loop1"]
                     ELSE /\ appliedWrite0' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, valuesRead, 
                               valuesWrite, networkWrite2, networkWrite3, 
                               networkWrite4, networkRead, networkWrite5, 
                               networkWrite6, networkWrite7, ifResult, 
                               appliedWrite1, networkWrite8, networkWrite9, 
                               appliedWrite2, ifResult0, appliedWrite3, 
                               networkWrite10, appliedWrite4, networkWrite11, 
                               networkWrite12, appliedWrite5, appliedWrite6, 
                               networkWrite13, appliedWrite7, networkWrite14, 
                               valuesLocal, currentTerm, votedFor, log, state, 
                               commitIndex, v, nextIndex, matchIndex, idx, 
                               votes, msg >>

N2(self) == /\ pc[self] = "N2"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

N3(self) == /\ pc[self] = "N3"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

N4(self) == /\ pc[self] = "N4"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg[self]).prevIndex) + (Len((msg[self]).entries)), prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

N6(self) == /\ pc[self] = "N6"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

N7(self) == /\ pc[self] = "N7"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ votedFor' = [votedFor EXCEPT ![self] = (msg[self]).sender]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, log, state, 
                            commitIndex, lastApplied, v, nextIndex, matchIndex, 
                            idx, votes, msg >>

N8(self) == /\ pc[self] = "N8"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

loop2(self) == /\ pc[self] = "loop2"
               /\ IF (((Cardinality({i \in Servers : (matchIndex[self][idx[self]]) > (commitIndex[self])})) * (2)) > (Cardinality(Servers))) /\ ((Term(log[self], (commitIndex[self]) + (1))) = (currentTerm[self]))
                     THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (commitIndex[self]) + (1)]
                          /\ pc' = [pc EXCEPT ![self] = "loop2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "loop3"]
                          /\ UNCHANGED commitIndex
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, valuesRead, 
                               valuesWrite, networkWrite2, networkWrite3, 
                               networkWrite4, networkRead, networkWrite5, 
                               networkWrite6, networkWrite7, ifResult, 
                               appliedWrite, appliedWrite0, appliedWrite1, 
                               networkWrite8, networkWrite9, appliedWrite2, 
                               ifResult0, appliedWrite3, networkWrite10, 
                               appliedWrite4, networkWrite11, networkWrite12, 
                               appliedWrite5, appliedWrite6, networkWrite13, 
                               appliedWrite7, networkWrite14, appliedLocal, 
                               valuesLocal, currentTerm, votedFor, log, state, 
                               lastApplied, v, nextIndex, matchIndex, idx, 
                               votes, msg >>

loop3(self) == /\ pc[self] = "loop3"
               /\ IF (lastApplied[self]) <= (commitIndex[self])
                     THEN /\ PrintT(<<"Applying", log[self][lastApplied[self]]>>)
                          /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied[self]] = (appliedLocal[self][lastApplied[self]]) \union ({log[self][lastApplied[self]]})]
                          /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite2' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "loop3"]
                     ELSE /\ appliedWrite2' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, timeoutRead, networkWrite, 
                               networkWrite0, networkWrite1, valuesRead, 
                               valuesWrite, networkWrite2, networkWrite3, 
                               networkWrite4, networkRead, networkWrite5, 
                               networkWrite6, networkWrite7, ifResult, 
                               appliedWrite0, appliedWrite1, networkWrite8, 
                               networkWrite9, ifResult0, appliedWrite3, 
                               networkWrite10, appliedWrite4, networkWrite11, 
                               networkWrite12, appliedWrite5, appliedWrite6, 
                               networkWrite13, appliedWrite7, networkWrite14, 
                               valuesLocal, currentTerm, votedFor, log, state, 
                               commitIndex, v, nextIndex, matchIndex, idx, 
                               votes, msg >>

N9(self) == /\ pc[self] = "N9"
            /\ (Len(mailboxes[(msg[self]).sender])) < (BUFFER_SIZE)
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [type |-> RequestVote, term |-> currentTerm[self], sender |-> self, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), granted |-> FALSE])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << timeoutRead, networkWrite0, networkWrite1, 
                            valuesRead, valuesWrite, networkWrite2, 
                            networkWrite3, networkWrite4, networkRead, 
                            networkWrite5, networkWrite6, networkWrite7, 
                            ifResult, appliedWrite, appliedWrite0, 
                            appliedWrite1, networkWrite8, networkWrite9, 
                            appliedWrite2, ifResult0, appliedWrite3, 
                            networkWrite10, appliedWrite4, networkWrite11, 
                            networkWrite12, appliedWrite5, appliedWrite6, 
                            networkWrite13, appliedWrite7, networkWrite14, 
                            appliedLocal, valuesLocal, currentTerm, votedFor, 
                            log, state, commitIndex, lastApplied, v, nextIndex, 
                            matchIndex, idx, votes, msg >>

server(self) == Start(self) \/ N10(self) \/ loop4(self) \/ N11(self)
                   \/ loop5(self) \/ N1(self) \/ N5(self) \/ loop1(self)
                   \/ N2(self) \/ N3(self) \/ N4(self) \/ N6(self)
                   \/ N7(self) \/ N8(self) \/ loop2(self) \/ loop3(self)
                   \/ N9(self)

Next == (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

StateMachineCorrectness == \A i,j \in Servers :
                            \A k \in 0..((IF commitIndex[i] < commitIndex[j] THEN commitIndex[i] ELSE commitIndex[j])-1):
                                log[i][k] = log[j][k] 
                                
ElectionSafety == \A i,j \in Servers :
                   currentTerm[i] = currentTerm[j] => state[i] # Leader \/ state[j] # Leader

LogMatching == \A i,j \in Servers :
                \A k \in 0..((IF Len(log[i]) < Len(log[j]) THEN Len(log[i]) ELSE Len(log[j]))-1):
                  log[i][k] = log[j][k] => \A l \in 0..k : log[i][l] = log[j][l]

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
