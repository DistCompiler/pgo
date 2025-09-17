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
        Servers == 0..N-1
        Follower == 0
        Candidate == 1
        Leader == 2
        RequestVote == 0
        RequestVoteResponse == 1
        AppendEntries == 2
        AppendEntriesResponse == 3
        SubSeq(seq,first,last) == [i \in 1..(1+first-last) |-> seq[first+last-1]]
        Term(log,index) == (IF Len(log) >= index /\ Len(log) > 0 THEN log[index].term ELSE 0)
    }

    macro SendRequestVotes(network, cterm, candidateId, lastLogIndex, lastLogTerm, idx) {
        while (idx < Cardinality(Servers)) {
            network[idx] := [type |-> RequestVote, term |-> cterm, sender |-> candidateId, entries |-> <<>>,
                             prevIndex |-> lastLogIndex, prevTerm |-> lastLogTerm, granted |-> FALSE];
            idx := idx + 1;
        };
    }

    macro SendAppendEntries(network, cterm, candidateId, nextIndex, matchIndex, log, leaderCommit, idx) {
        while (idx < Cardinality(Servers)) {
            if (idx # candidateId) {
                network[idx] := [type |-> RequestVote, term |-> cterm, sender |-> candidateId, entries |-> SubSeq(log, nextIndex[idx], Len(log)),
                                 prevIndex |-> nextIndex[idx]-1, prevTerm |-> Term(log, nextIndex[idx]-1), granted |-> FALSE];
            };

            idx := idx + 1;
        };
    }

    macro SubSeq(t, t2, end, idx) {
        while(idx <= end) {
            t2 := Append(t2,Head(t));
            t := Tail(t);
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

    archetype Node(ref network[_], ref applied[_], ref values)
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
        either {
N1:         msg := network[self];
            if (msg.type = AppendEntries) {
                if (msg.term < currentTerm) {
N2:                 network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                            entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
                } else if (Len(log) < msg.prevIndex \/ log[msg.prevIndex].term # msg.prevTerm) {
                    \* Following entries don't have matching terms
                    log := SubSeq(log,1,msg.prevIndex-1);
N3:                 network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE,
                                            entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
                } else if (Len(log) = msg.prevIndex) {
                    log := log \o msg.entries;
N4:                 network[msg.sender] := [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> TRUE,
                                            entries |-> <<>>, prevIndex |-> msg.prevIndex + Len(msg.entries), prevTerm |-> Nil];
                };

N5:             if (msg.term > currentTerm) {
                    state := Follower;
                    currentTerm := msg.term;
                };

                if (msg.leaderCommit > commitIndex) {
                    commitIndex := IF msg.leaderCommit < Len(log) THEN msg.leaderCommit ELSE Len(log[self]);
loop1:              while(lastApplied <= commitIndex) {
                        \* with (tmp = applied) {
                        \*     applied := [tmp EXCEPT ![lastApplied] = log[lastApplied]];
                        \* };
                        applied[lastApplied] := log[lastApplied];
                        lastApplied := lastApplied + 1;
                    };
                };
            } else if (msg.type = RequestVote) {
                if (msg.term < currentTerm) {
N6:                 network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> FALSE,
                                            entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
                } else if ((votedFor = Nil \/ votedFor = msg.sender)
                         /\ (msg.prevTerm > Term(log, Len(log))
                             \/ (msg.prevTerm = Term(log, Len(log)) /\ msg.prevIndex >= Len(log)))) {
                    log := SubSeq(log, 1, msg.prevIndex-1);
 N7:                network[msg.sender] := [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm, granted |-> TRUE,
                                            entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil];
                };
            } else if (msg.type = AppendEntriesResponse /\ state = Leader) {
                if (msg.granted) {
                    nextIndex[msg.sender] := msg.prevIndex + 1;
                    matchIndex[msg.sender] := msg.prevIndex;
loop2:              while (Cardinality({i \in Servers: matchIndex[idx] > commitIndex})*2 > Cardinality(Servers) /\ Term(log, commitIndex+1) = currentTerm) {
                        commitIndex := commitIndex + 1;
                    };
loop3:              while(lastApplied <= commitIndex) {
                        \* with (tmp = applied) {
                        \*     applied := [tmp EXCEPT ![lastApplied] = log[lastApplied]];
                        \* };
                        applied[lastApplied] := log[lastApplied];
                        lastApplied := lastApplied + 1;
                    };
                } else {
                    nextIndex[msg.sender] := IF nextIndex[msg.sender] - 1 > 1 THEN nextIndex[msg.sender] - 1 ELSE 1;
N8:                 network[msg.sender] := [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, nextIndex[msg.sender], Len(log)),
                                            prevIndex |-> nextIndex[msg.sender]-1, prevTerm |-> Term(log, nextIndex[msg.sender]-1), granted |-> FALSE];
                };
            } else if (msg.type = RequestVoteResponse) {
                if (msg.granted /\ state = Candidate) {
                    votes[msg.term] := votes[msg.term] \union {msg.sender};
                    if (Cardinality(votes[msg.term])*2 > Cardinality(Servers)) {
                        state := Leader;
                        matchIndex := [s3 \in Servers |-> 0];
                        nextIndex := [s4 \in Servers |-> 0];
                    };
                };
            };
        } or {
            \* Election timeout
N9:         if (state # Leader) {
                state := Candidate;
                currentTerm := currentTerm + 1;
                votes[currentTerm] := {self};
                votedFor := self;
                idx := 0;
loop4:          SendRequestVotes(network, self, currentTerm, Len(log), Term(log, Len(log)), idx);
            };
        } or {
            \* Act as leader
N10:        if (state = Leader) {
                v := values;
                log := Append(log, [val |-> v, term |-> currentTerm]);
                matchIndex[self] := Len(log);
                nextIndex[self] := Len(log)+1;
                idx := 0;
loop5:          SendAppendEntries(network, currentTerm, self, nextIndex, matchIndex, log, commitIndex, idx);
            };
        };
      };
    }


    variables
        mailboxes = [id \in Servers |-> <<>>];

    fair process (server \in Servers) == instance Node(ref mailboxes[_], [s \in 0..Slots |-> {}], {1})
        mapping mailboxes[_] via FIFOChannel
        mapping @2[_] via Log
        mapping @3 via Input;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm Raft {
  variables mailboxes = [id \in Servers |-> <<>>];
  define{
    Servers == (0) .. ((N) - (1))
    Follower == 0
    Candidate == 1
    Leader == 2
    RequestVote == 0
    RequestVoteResponse == 1
    AppendEntries == 2
    AppendEntriesResponse == 3
    SubSeq(seq, first, last) == [i \in (1) .. ((1) + ((first) - (last))) |-> (seq)[(first) + ((last) - (1))]]
    Term(log, index) == IF ((Len(log)) >= (index)) /\ ((Len(log)) > (0)) THEN ((log)[index]).term ELSE 0
  }

  fair process (server \in Servers)
    variables currentTerm = 0; votedFor = Nil; log = <<>>; state = Follower; commitIndex = 0; lastApplied = 0; v; nextIndex; matchIndex; idx; votes = [t \in (0) .. (Terms) |-> {}]; msg; applied = [s \in (0) .. (Slots) |-> {}]; values = {1};
  {
    Start:
      if(((commitIndex) < (Slots)) /\ ((currentTerm) < (Terms))) {
        either {
          goto N1;
        } or {
          goto N9;
        } or {
          goto N10;
        };
      } else {
        goto Done;
      };
    N1:
      await (Len((mailboxes)[self])) > (0);
      with (msg00 = Head((mailboxes)[self])) {
        mailboxes := [mailboxes EXCEPT ![self] = Tail((mailboxes)[self])];
        with (yielded_mailboxes0 = msg00) {
          msg := yielded_mailboxes0;
          if(((msg).type) = (AppendEntries)) {
            if(((msg).term) < (currentTerm)) {
              goto N2;
            } else {
              if(((Len(log)) < ((msg).prevIndex)) \/ ((((log)[(msg).prevIndex]).term) # ((msg).prevTerm))) {
                log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                goto N3;
              } else {
                if((Len(log)) = ((msg).prevIndex)) {
                  log := (log) \o ((msg).entries);
                  goto N4;
                } else {
                  goto N5;
                };
              };
            };
          } else {
            if(((msg).type) = (RequestVote)) {
              if(((msg).term) < (currentTerm)) {
                goto N6;
              } else {
                if((((votedFor) = (Nil)) \/ ((votedFor) = ((msg).sender))) /\ ((((msg).prevTerm) > (Term(log, Len(log)))) \/ ((((msg).prevTerm) = (Term(log, Len(log)))) /\ (((msg).prevIndex) >= (Len(log)))))) {
                  log := SubSeq(log, 1, ((msg).prevIndex) - (1));
                  goto N7;
                } else {
                  goto Start;
                };
              };
            } else {
              if((((msg).type) = (AppendEntriesResponse)) /\ ((state) = (Leader))) {
                if((msg).granted) {
                  nextIndex := [nextIndex EXCEPT ![(msg).sender] = ((msg).prevIndex) + (1)];
                  matchIndex := [matchIndex EXCEPT ![(msg).sender] = (msg).prevIndex];
                  goto loop2;
                } else {
                  nextIndex := [nextIndex EXCEPT ![(msg).sender] = IF (((nextIndex)[(msg).sender]) - (1)) > (1) THEN ((nextIndex)[(msg).sender]) - (1) ELSE 1];
                  goto N8;
                };
              } else {
                if(((msg).type) = (RequestVoteResponse)) {
                  if(((msg).granted) /\ ((state) = (Candidate))) {
                    votes := [votes EXCEPT ![(msg).term] = ((votes)[(msg).term]) \union ({(msg).sender})];
                    if(((Cardinality((votes)[(msg).term])) * (2)) > (Cardinality(Servers))) {
                      state := Leader;
                      matchIndex := [s3 \in Servers |-> 0];
                      nextIndex := [s4 \in Servers |-> 0];
                      goto Start;
                    } else {
                      goto Start;
                    };
                  } else {
                    goto Start;
                  };
                } else {
                  goto Start;
                };
              };
            };
          };
        };
      };
    N2:
      with (value3 = [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm, granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil]) {
        mailboxes := [mailboxes EXCEPT ![(msg).sender] = Append((mailboxes)[(msg).sender], value3)];
        goto N5;
      };
    N5:
      if(((msg).term) > (currentTerm)) {
        state := Follower;
        currentTerm := (msg).term;
        if(((msg).leaderCommit) > (commitIndex)) {
          commitIndex := IF ((msg).leaderCommit) < (Len(log)) THEN (msg).leaderCommit ELSE Len((log)[self]);
          goto loop1;
        } else {
          goto Start;
        };
      } else {
        if(((msg).leaderCommit) > (commitIndex)) {
          commitIndex := IF ((msg).leaderCommit) < (Len(log)) THEN (msg).leaderCommit ELSE Len((log)[self]);
          goto loop1;
        } else {
          goto Start;
        };
      };
    loop1:
      if((lastApplied) <= (commitIndex)) {
        with (value00 = (log)[lastApplied]) {
          applied := [applied EXCEPT ![lastApplied] = ((applied)[lastApplied]) \union ({value00})];
          lastApplied := (lastApplied) + (1);
          goto loop1;
        };
      } else {
        goto Start;
      };
    N9:
      if((state) # (Leader)) {
        state := Candidate;
        currentTerm := (currentTerm) + (1);
        votes := [votes EXCEPT ![currentTerm] = {self}];
        votedFor := self;
        idx := 0;
        goto loop4;
      } else {
        goto Start;
      };
    loop4:
      if((idx) < (Cardinality(Servers))) {
        with (value10 = [type |-> RequestVote, term |-> self, sender |-> currentTerm, entries |-> <<>>, prevIndex |-> Len(log), prevTerm |-> Term(log, Len(log)), granted |-> FALSE]) {
          mailboxes := [mailboxes EXCEPT ![idx] = Append((mailboxes)[idx], value10)];
          idx := (idx) + (1);
          goto loop4;
        };
      } else {
        goto Start;
      };
    N10:
      if((state) = (Leader)) {
        with (msg10 = Head(values)) {
          values := Tail(values);
          with (yielded_values0 = msg10) {
            v := yielded_values0;
            log := Append(log, [val |-> v, term |-> currentTerm]);
            matchIndex := [matchIndex EXCEPT ![self] = Len(log)];
            nextIndex := [nextIndex EXCEPT ![self] = (Len(log)) + (1)];
            idx := 0;
            goto loop5;
          };
        };
      } else {
        goto Start;
      };
    loop5:
      if((idx) < (Cardinality(Servers))) {
        if((idx) # (self)) {
          with (value20 = [type |-> RequestVote, term |-> currentTerm, sender |-> self, entries |-> SubSeq(log, (nextIndex)[idx], Len(log)), prevIndex |-> ((nextIndex)[idx]) - (1), prevTerm |-> Term(log, ((nextIndex)[idx]) - (1)), granted |-> FALSE]) {
            mailboxes := [mailboxes EXCEPT ![idx] = Append((mailboxes)[idx], value20)];
            idx := (idx) + (1);
            goto loop5;
          };
        } else {
          idx := (idx) + (1);
          goto loop5;
        };
      } else {
        goto Start;
      };
  }
}

\* END PLUSCAL TRANSLATION

******************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES mailboxes, networkRead, networkWrite, networkWrite0, networkWrite1,
          networkWrite2, ifResult, appliedWrite, appliedWrite0, appliedWrite1,
          networkWrite3, networkWrite4, appliedWrite2, ifResult0,
          appliedWrite3, networkWrite5, appliedWrite4, networkWrite6,
          networkWrite7, appliedWrite5, appliedWrite6, networkWrite8,
          networkWrite9, networkWrite10, valuesRead, valuesWrite,
          networkWrite11, networkWrite12, networkWrite13, appliedWrite7,
          networkWrite14, appliedWrite8, networkWrite15, pc

(* define statement *)
Servers == (0) .. ((N) - (1))
Follower == 0
Candidate == 1
Leader == 2
RequestVote == 0
RequestVoteResponse == 1
AppendEntries == 2
AppendEntriesResponse == 3
\*SubSeq(seq, first, last) == IF ((Len(seq)) = (0)) \/ ((last) <= (0)) THEN <<>> ELSE IF (first) > (1) THEN SubSeq(Tail(seq), (first) - (1), (last) - (1)) ELSE Append(Head(seq), SubSeq(Tail(seq), first, (last) - (1)))
Term(log, index) == IF ((Len(log)) >= (index)) /\ ((Len(log)) > (0)) THEN (log[index]).term ELSE 0

VARIABLES appliedLocal, valuesLocal, currentTerm, votedFor, log, state,
          commitIndex, lastApplied, v, nextIndex, matchIndex, idx, votes, msg

vars == << mailboxes, networkRead, networkWrite, networkWrite0, networkWrite1,
           networkWrite2, ifResult, appliedWrite, appliedWrite0,
           appliedWrite1, networkWrite3, networkWrite4, appliedWrite2,
           ifResult0, appliedWrite3, networkWrite5, appliedWrite4,
           networkWrite6, networkWrite7, appliedWrite5, appliedWrite6,
           networkWrite8, networkWrite9, networkWrite10, valuesRead,
           valuesWrite, networkWrite11, networkWrite12, networkWrite13,
           appliedWrite7, networkWrite14, appliedWrite8, networkWrite15, pc,
           appliedLocal, valuesLocal, currentTerm, votedFor, log, state,
           commitIndex, lastApplied, v, nextIndex, matchIndex, idx, votes,
           msg >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ mailboxes = [id \in Servers |-> <<>>]
        /\ networkRead = defaultInitValue
        /\ networkWrite = defaultInitValue
        /\ networkWrite0 = defaultInitValue
        /\ networkWrite1 = defaultInitValue
        /\ networkWrite2 = defaultInitValue
        /\ ifResult = defaultInitValue
        /\ appliedWrite = defaultInitValue
        /\ appliedWrite0 = defaultInitValue
        /\ appliedWrite1 = defaultInitValue
        /\ networkWrite3 = defaultInitValue
        /\ networkWrite4 = defaultInitValue
        /\ appliedWrite2 = defaultInitValue
        /\ ifResult0 = defaultInitValue
        /\ appliedWrite3 = defaultInitValue
        /\ networkWrite5 = defaultInitValue
        /\ appliedWrite4 = defaultInitValue
        /\ networkWrite6 = defaultInitValue
        /\ networkWrite7 = defaultInitValue
        /\ appliedWrite5 = defaultInitValue
        /\ appliedWrite6 = defaultInitValue
        /\ networkWrite8 = defaultInitValue
        /\ networkWrite9 = defaultInitValue
        /\ networkWrite10 = defaultInitValue
        /\ valuesRead = defaultInitValue
        /\ valuesWrite = defaultInitValue
        /\ networkWrite11 = defaultInitValue
        /\ networkWrite12 = defaultInitValue
        /\ networkWrite13 = defaultInitValue
        /\ appliedWrite7 = defaultInitValue
        /\ networkWrite14 = defaultInitValue
        /\ appliedWrite8 = defaultInitValue
        /\ networkWrite15 = defaultInitValue
        (* Process server *)
        /\ appliedLocal = [self \in Servers |-> [s \in (0) .. (Slots) |-> {}]]
        /\ valuesLocal = [self \in Servers |-> {self}]
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
                     THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "N1"]
                             \/ /\ pc' = [pc EXCEPT ![self] = "N9"]
                             \/ /\ pc' = [pc EXCEPT ![self] = "N10"]
                          /\ UNCHANGED << mailboxes, appliedWrite8,
                                          networkWrite15, appliedLocal >>
                     ELSE /\ appliedWrite8' = appliedLocal[self]
                          /\ networkWrite15' = mailboxes
                          /\ mailboxes' = networkWrite15'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite8']
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << networkRead, networkWrite, networkWrite0,
                               networkWrite1, networkWrite2, ifResult,
                               appliedWrite, appliedWrite0, appliedWrite1,
                               networkWrite3, networkWrite4, appliedWrite2,
                               ifResult0, appliedWrite3, networkWrite5,
                               appliedWrite4, networkWrite6, networkWrite7,
                               appliedWrite5, appliedWrite6, networkWrite8,
                               networkWrite9, networkWrite10, valuesRead,
                               valuesWrite, networkWrite11, networkWrite12,
                               networkWrite13, appliedWrite7, networkWrite14,
                               valuesLocal, currentTerm, votedFor, log, state,
                               commitIndex, lastApplied, v, nextIndex,
                               matchIndex, idx, votes, msg >>

N1(self) == /\ pc[self] = "N1"
            /\ (Len(mailboxes[self])) > (0)
            /\ LET msg0 == Head(mailboxes[self]) IN
                 /\ networkWrite' = [mailboxes EXCEPT ![self] = Tail(mailboxes[self])]
                 /\ networkRead' = msg0
            /\ msg' = [msg EXCEPT ![self] = networkRead']
            /\ IF ((msg'[self]).type) = (AppendEntries)
                  THEN /\ IF ((msg'[self]).term) < (currentTerm[self])
                             THEN /\ mailboxes' = networkWrite'
                                  /\ pc' = [pc EXCEPT ![self] = "N2"]
                                  /\ UNCHANGED << networkWrite0, networkWrite1,
                                                  networkWrite2, log >>
                             ELSE /\ IF ((Len(log[self])) < ((msg'[self]).prevIndex)) \/ (((log[self][(msg'[self]).prevIndex]).term) # ((msg'[self]).prevTerm))
                                        THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg'[self]).prevIndex) - (1))]
                                             /\ pc' = [pc EXCEPT ![self] = "N3"]
                                             /\ UNCHANGED << mailboxes,
                                                             networkWrite0,
                                                             networkWrite1,
                                                             networkWrite2 >>
                                        ELSE /\ IF (Len(log[self])) = ((msg'[self]).prevIndex)
                                                   THEN /\ log' = [log EXCEPT ![self] = (log[self]) \o ((msg'[self]).entries)]
                                                        /\ pc' = [pc EXCEPT ![self] = "N4"]
                                                        /\ UNCHANGED << mailboxes,
                                                                        networkWrite0,
                                                                        networkWrite1,
                                                                        networkWrite2 >>
                                                   ELSE /\ networkWrite0' = mailboxes
                                                        /\ networkWrite1' = networkWrite0'
                                                        /\ networkWrite2' = networkWrite1'
                                                        /\ mailboxes' = networkWrite2'
                                                        /\ pc' = [pc EXCEPT ![self] = "N5"]
                                                        /\ log' = log
                       /\ UNCHANGED << networkWrite3, networkWrite4, ifResult0,
                                       appliedWrite4, networkWrite6,
                                       networkWrite7, appliedWrite5,
                                       appliedWrite6, networkWrite8,
                                       appliedLocal, state, nextIndex,
                                       matchIndex, votes >>
                  ELSE /\ IF ((msg'[self]).type) = (RequestVote)
                             THEN /\ IF ((msg'[self]).term) < (currentTerm[self])
                                        THEN /\ pc' = [pc EXCEPT ![self] = "N6"]
                                             /\ UNCHANGED << mailboxes,
                                                             networkWrite3,
                                                             networkWrite4,
                                                             networkWrite7,
                                                             appliedWrite5,
                                                             appliedWrite6,
                                                             networkWrite8,
                                                             appliedLocal, log >>
                                        ELSE /\ IF (((votedFor[self]) = (Nil)) \/ ((votedFor[self]) = ((msg'[self]).sender))) /\ ((((msg'[self]).prevTerm) > (Term(log[self], Len(log[self])))) \/ ((((msg'[self]).prevTerm) = (Term(log[self], Len(log[self])))) /\ (((msg'[self]).prevIndex) >= (Len(log[self])))))
                                                   THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, ((msg'[self]).prevIndex) - (1))]
                                                        /\ pc' = [pc EXCEPT ![self] = "N7"]
                                                        /\ UNCHANGED << mailboxes,
                                                                        networkWrite3,
                                                                        networkWrite4,
                                                                        networkWrite7,
                                                                        appliedWrite5,
                                                                        appliedWrite6,
                                                                        networkWrite8,
                                                                        appliedLocal >>
                                                   ELSE /\ networkWrite3' = mailboxes
                                                        /\ networkWrite4' = networkWrite3'
                                                        /\ networkWrite7' = networkWrite4'
                                                        /\ appliedWrite5' = appliedLocal[self]
                                                        /\ appliedWrite6' = appliedWrite5'
                                                        /\ networkWrite8' = networkWrite7'
                                                        /\ mailboxes' = networkWrite8'
                                                        /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                        /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                        /\ log' = log
                                  /\ UNCHANGED << ifResult0, appliedWrite4,
                                                  networkWrite6, state,
                                                  nextIndex, matchIndex, votes >>
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
                                                        /\ pc' = [pc EXCEPT ![self] = "N8"]
                                                        /\ UNCHANGED matchIndex
                                             /\ UNCHANGED << mailboxes,
                                                             appliedWrite4,
                                                             networkWrite6,
                                                             networkWrite7,
                                                             appliedWrite5,
                                                             appliedWrite6,
                                                             networkWrite8,
                                                             appliedLocal,
                                                             state, votes >>
                                        ELSE /\ IF ((msg'[self]).type) = (RequestVoteResponse)
                                                   THEN /\ IF ((msg'[self]).granted) /\ ((state[self]) = (Candidate))
                                                              THEN /\ votes' = [votes EXCEPT ![self][(msg'[self]).term] = (votes[self][(msg'[self]).term]) \union ({(msg'[self]).sender})]
                                                                   /\ IF ((Cardinality(votes'[self][(msg'[self]).term])) * (2)) > (Cardinality(Servers))
                                                                         THEN /\ state' = [state EXCEPT ![self] = Leader]
                                                                              /\ matchIndex' = [matchIndex EXCEPT ![self] = [s3 \in Servers |-> 0]]
                                                                              /\ nextIndex' = [nextIndex EXCEPT ![self] = [s4 \in Servers |-> 0]]
                                                                              /\ appliedWrite4' = appliedLocal[self]
                                                                              /\ networkWrite6' = mailboxes
                                                                              /\ networkWrite7' = networkWrite6'
                                                                              /\ appliedWrite5' = appliedWrite4'
                                                                              /\ appliedWrite6' = appliedWrite5'
                                                                              /\ networkWrite8' = networkWrite7'
                                                                              /\ mailboxes' = networkWrite8'
                                                                              /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                              /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                         ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                              /\ networkWrite6' = mailboxes
                                                                              /\ networkWrite7' = networkWrite6'
                                                                              /\ appliedWrite5' = appliedWrite4'
                                                                              /\ appliedWrite6' = appliedWrite5'
                                                                              /\ networkWrite8' = networkWrite7'
                                                                              /\ mailboxes' = networkWrite8'
                                                                              /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                              /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                              /\ UNCHANGED << state,
                                                                                              nextIndex,
                                                                                              matchIndex >>
                                                              ELSE /\ appliedWrite4' = appliedLocal[self]
                                                                   /\ networkWrite6' = mailboxes
                                                                   /\ networkWrite7' = networkWrite6'
                                                                   /\ appliedWrite5' = appliedWrite4'
                                                                   /\ appliedWrite6' = appliedWrite5'
                                                                   /\ networkWrite8' = networkWrite7'
                                                                   /\ mailboxes' = networkWrite8'
                                                                   /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                                   /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                                   /\ UNCHANGED << state,
                                                                                   nextIndex,
                                                                                   matchIndex,
                                                                                   votes >>
                                                   ELSE /\ appliedWrite4' = appliedLocal[self]
                                                        /\ networkWrite6' = mailboxes
                                                        /\ networkWrite7' = networkWrite6'
                                                        /\ appliedWrite5' = appliedWrite4'
                                                        /\ appliedWrite6' = appliedWrite5'
                                                        /\ networkWrite8' = networkWrite7'
                                                        /\ mailboxes' = networkWrite8'
                                                        /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite6']
                                                        /\ pc' = [pc EXCEPT ![self] = "Start"]
                                                        /\ UNCHANGED << state,
                                                                        nextIndex,
                                                                        matchIndex,
                                                                        votes >>
                                             /\ UNCHANGED ifResult0
                                  /\ UNCHANGED << networkWrite3, networkWrite4,
                                                  log >>
                       /\ UNCHANGED << networkWrite0, networkWrite1,
                                       networkWrite2 >>
            /\ UNCHANGED << ifResult, appliedWrite, appliedWrite0,
                            appliedWrite1, appliedWrite2, appliedWrite3,
                            networkWrite5, networkWrite9, networkWrite10,
                            valuesRead, valuesWrite, networkWrite11,
                            networkWrite12, networkWrite13, appliedWrite7,
                            networkWrite14, appliedWrite8, networkWrite15,
                            valuesLocal, currentTerm, votedFor, commitIndex,
                            lastApplied, v, idx >>

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
            /\ UNCHANGED << mailboxes, networkRead, networkWrite,
                            networkWrite0, networkWrite1, networkWrite2,
                            appliedWrite, appliedWrite0, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, valuesLocal, votedFor, log,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

loop1(self) == /\ pc[self] = "loop1"
               /\ IF (lastApplied[self]) <= (commitIndex[self])
                     THEN /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied[self]] = (appliedLocal[self][lastApplied[self]]) \union ({log[self][lastApplied[self]]})]
                          /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite0' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "loop1"]
                     ELSE /\ appliedWrite0' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite0']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, networkRead, networkWrite,
                               networkWrite0, networkWrite1, networkWrite2,
                               ifResult, appliedWrite1, networkWrite3,
                               networkWrite4, appliedWrite2, ifResult0,
                               appliedWrite3, networkWrite5, appliedWrite4,
                               networkWrite6, networkWrite7, appliedWrite5,
                               appliedWrite6, networkWrite8, networkWrite9,
                               networkWrite10, valuesRead, valuesWrite,
                               networkWrite11, networkWrite12, networkWrite13,
                               appliedWrite7, networkWrite14, appliedWrite8,
                               networkWrite15, valuesLocal, currentTerm,
                               votedFor, log, state, commitIndex, v, nextIndex,
                               matchIndex, idx, votes, msg >>

N2(self) == /\ pc[self] = "N2"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

N3(self) == /\ pc[self] = "N3"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

N4(self) == /\ pc[self] = "N4"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> AppendEntriesResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> ((msg[self]).prevIndex) + (Len((msg[self]).entries)), prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "N5"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

N6(self) == /\ pc[self] = "N6"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> FALSE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

N7(self) == /\ pc[self] = "N7"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [sender |-> self, type |-> RequestVoteResponse, term |-> currentTerm[self], granted |-> TRUE, entries |-> <<>>, prevIndex |-> Nil, prevTerm |-> Nil])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

loop2(self) == /\ pc[self] = "loop2"
               /\ IF (((Cardinality({i \in Servers : (matchIndex[self][idx[self]]) > (commitIndex[self])})) * (2)) > (Cardinality(Servers))) /\ ((Term(log[self], (commitIndex[self]) + (1))) = (currentTerm[self]))
                     THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = (commitIndex[self]) + (1)]
                          /\ pc' = [pc EXCEPT ![self] = "loop2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "loop3"]
                          /\ UNCHANGED commitIndex
               /\ UNCHANGED << mailboxes, networkRead, networkWrite,
                               networkWrite0, networkWrite1, networkWrite2,
                               ifResult, appliedWrite, appliedWrite0,
                               appliedWrite1, networkWrite3, networkWrite4,
                               appliedWrite2, ifResult0, appliedWrite3,
                               networkWrite5, appliedWrite4, networkWrite6,
                               networkWrite7, appliedWrite5, appliedWrite6,
                               networkWrite8, networkWrite9, networkWrite10,
                               valuesRead, valuesWrite, networkWrite11,
                               networkWrite12, networkWrite13, appliedWrite7,
                               networkWrite14, appliedWrite8, networkWrite15,
                               appliedLocal, valuesLocal, currentTerm,
                               votedFor, log, state, lastApplied, v, nextIndex,
                               matchIndex, idx, votes, msg >>

loop3(self) == /\ pc[self] = "loop3"
               /\ IF (lastApplied[self]) <= (commitIndex[self])
                     THEN /\ appliedWrite' = [appliedLocal[self] EXCEPT ![lastApplied[self]] = (appliedLocal[self][lastApplied[self]]) \union ({log[self][lastApplied[self]]})]
                          /\ lastApplied' = [lastApplied EXCEPT ![self] = (lastApplied[self]) + (1)]
                          /\ appliedWrite2' = appliedWrite'
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "loop3"]
                     ELSE /\ appliedWrite2' = appliedLocal[self]
                          /\ appliedLocal' = [appliedLocal EXCEPT ![self] = appliedWrite2']
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << appliedWrite, lastApplied >>
               /\ UNCHANGED << mailboxes, networkRead, networkWrite,
                               networkWrite0, networkWrite1, networkWrite2,
                               ifResult, appliedWrite0, appliedWrite1,
                               networkWrite3, networkWrite4, ifResult0,
                               appliedWrite3, networkWrite5, appliedWrite4,
                               networkWrite6, networkWrite7, appliedWrite5,
                               appliedWrite6, networkWrite8, networkWrite9,
                               networkWrite10, valuesRead, valuesWrite,
                               networkWrite11, networkWrite12, networkWrite13,
                               appliedWrite7, networkWrite14, appliedWrite8,
                               networkWrite15, valuesLocal, currentTerm,
                               votedFor, log, state, commitIndex, v, nextIndex,
                               matchIndex, idx, votes, msg >>

N8(self) == /\ pc[self] = "N8"
            /\ networkWrite' = [mailboxes EXCEPT ![(msg[self]).sender] = Append(mailboxes[(msg[self]).sender], [type |-> RequestVote, term |-> currentTerm[self], sender |-> self, entries |-> SubSeq(log[self], nextIndex[self][(msg[self]).sender], Len(log[self])), prevIndex |-> (nextIndex[self][(msg[self]).sender]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][(msg[self]).sender]) - (1)), granted |-> FALSE])]
            /\ mailboxes' = networkWrite'
            /\ pc' = [pc EXCEPT ![self] = "Start"]
            /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                            networkWrite2, ifResult, appliedWrite,
                            appliedWrite0, appliedWrite1, networkWrite3,
                            networkWrite4, appliedWrite2, ifResult0,
                            appliedWrite3, networkWrite5, appliedWrite4,
                            networkWrite6, networkWrite7, appliedWrite5,
                            appliedWrite6, networkWrite8, networkWrite9,
                            networkWrite10, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal,
                            currentTerm, votedFor, log, state, commitIndex,
                            lastApplied, v, nextIndex, matchIndex, idx, votes,
                            msg >>

N9(self) == /\ pc[self] = "N9"
            /\ IF (state[self]) # (Leader)
                  THEN /\ state' = [state EXCEPT ![self] = Candidate]
                       /\ currentTerm' = [currentTerm EXCEPT ![self] = (currentTerm[self]) + (1)]
                       /\ votes' = [votes EXCEPT ![self][currentTerm'[self]] = {self}]
                       /\ votedFor' = [votedFor EXCEPT ![self] = self]
                       /\ idx' = [idx EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "loop4"]
                       /\ UNCHANGED << mailboxes, networkWrite10 >>
                  ELSE /\ networkWrite10' = mailboxes
                       /\ mailboxes' = networkWrite10'
                       /\ pc' = [pc EXCEPT ![self] = "Start"]
                       /\ UNCHANGED << currentTerm, votedFor, state, idx,
                                       votes >>
            /\ UNCHANGED << networkRead, networkWrite, networkWrite0,
                            networkWrite1, networkWrite2, ifResult,
                            appliedWrite, appliedWrite0, appliedWrite1,
                            networkWrite3, networkWrite4, appliedWrite2,
                            ifResult0, appliedWrite3, networkWrite5,
                            appliedWrite4, networkWrite6, networkWrite7,
                            appliedWrite5, appliedWrite6, networkWrite8,
                            networkWrite9, valuesRead, valuesWrite,
                            networkWrite11, networkWrite12, networkWrite13,
                            appliedWrite7, networkWrite14, appliedWrite8,
                            networkWrite15, appliedLocal, valuesLocal, log,
                            commitIndex, lastApplied, v, nextIndex, matchIndex,
                            msg >>

loop4(self) == /\ pc[self] = "loop4"
               /\ IF (idx[self]) < (Cardinality(Servers))
                     THEN /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [type |-> RequestVote, term |-> self, sender |-> currentTerm[self], entries |-> <<>>, prevIndex |-> Len(log[self]), prevTerm |-> Term(log[self], Len(log[self])), granted |-> FALSE])]
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite9' = networkWrite'
                          /\ mailboxes' = networkWrite9'
                          /\ pc' = [pc EXCEPT ![self] = "loop4"]
                     ELSE /\ networkWrite9' = mailboxes
                          /\ mailboxes' = networkWrite9'
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << networkWrite, idx >>
               /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                               networkWrite2, ifResult, appliedWrite,
                               appliedWrite0, appliedWrite1, networkWrite3,
                               networkWrite4, appliedWrite2, ifResult0,
                               appliedWrite3, networkWrite5, appliedWrite4,
                               networkWrite6, networkWrite7, appliedWrite5,
                               appliedWrite6, networkWrite8, networkWrite10,
                               valuesRead, valuesWrite, networkWrite11,
                               networkWrite12, networkWrite13, appliedWrite7,
                               networkWrite14, appliedWrite8, networkWrite15,
                               appliedLocal, valuesLocal, currentTerm,
                               votedFor, log, state, commitIndex, lastApplied,
                               v, nextIndex, matchIndex, votes, msg >>

N10(self) == /\ pc[self] = "N10"
             /\ IF (state[self]) = (Leader)
                   THEN /\ LET msg1 == Head(valuesLocal[self]) IN
                             /\ valuesWrite' = Tail(valuesLocal[self])
                             /\ valuesRead' = msg1
                        /\ v' = [v EXCEPT ![self] = valuesRead']
                        /\ log' = [log EXCEPT ![self] = Append(log[self], [val |-> v'[self], term |-> currentTerm[self]])]
                        /\ matchIndex' = [matchIndex EXCEPT ![self][self] = Len(log'[self])]
                        /\ nextIndex' = [nextIndex EXCEPT ![self][self] = (Len(log'[self])) + (1)]
                        /\ idx' = [idx EXCEPT ![self] = 0]
                        /\ valuesLocal' = [valuesLocal EXCEPT ![self] = valuesWrite']
                        /\ pc' = [pc EXCEPT ![self] = "loop5"]
                        /\ UNCHANGED << mailboxes, networkWrite13 >>
                   ELSE /\ networkWrite13' = mailboxes
                        /\ mailboxes' = networkWrite13'
                        /\ pc' = [pc EXCEPT ![self] = "Start"]
                        /\ UNCHANGED << valuesRead, valuesWrite, valuesLocal,
                                        log, v, nextIndex, matchIndex, idx >>
             /\ UNCHANGED << networkRead, networkWrite, networkWrite0,
                             networkWrite1, networkWrite2, ifResult,
                             appliedWrite, appliedWrite0, appliedWrite1,
                             networkWrite3, networkWrite4, appliedWrite2,
                             ifResult0, appliedWrite3, networkWrite5,
                             appliedWrite4, networkWrite6, networkWrite7,
                             appliedWrite5, appliedWrite6, networkWrite8,
                             networkWrite9, networkWrite10, networkWrite11,
                             networkWrite12, appliedWrite7, networkWrite14,
                             appliedWrite8, networkWrite15, appliedLocal,
                             currentTerm, votedFor, state, commitIndex,
                             lastApplied, votes, msg >>

loop5(self) == /\ pc[self] = "loop5"
               /\ IF (idx[self]) < (Cardinality(Servers))
                     THEN /\ IF (idx[self]) # (self)
                                THEN /\ networkWrite' = [mailboxes EXCEPT ![idx[self]] = Append(mailboxes[idx[self]], [type |-> RequestVote, term |-> currentTerm[self], sender |-> self, entries |-> SubSeq(log[self], nextIndex[self][idx[self]], Len(log[self])), prevIndex |-> (nextIndex[self][idx[self]]) - (1), prevTerm |-> Term(log[self], (nextIndex[self][idx[self]]) - (1)), granted |-> FALSE])]
                                     /\ networkWrite11' = networkWrite'
                                ELSE /\ networkWrite11' = mailboxes
                                     /\ UNCHANGED networkWrite
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ networkWrite12' = networkWrite11'
                          /\ mailboxes' = networkWrite12'
                          /\ pc' = [pc EXCEPT ![self] = "loop5"]
                     ELSE /\ networkWrite12' = mailboxes
                          /\ mailboxes' = networkWrite12'
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED << networkWrite, networkWrite11, idx >>
               /\ UNCHANGED << networkRead, networkWrite0, networkWrite1,
                               networkWrite2, ifResult, appliedWrite,
                               appliedWrite0, appliedWrite1, networkWrite3,
                               networkWrite4, appliedWrite2, ifResult0,
                               appliedWrite3, networkWrite5, appliedWrite4,
                               networkWrite6, networkWrite7, appliedWrite5,
                               appliedWrite6, networkWrite8, networkWrite9,
                               networkWrite10, valuesRead, valuesWrite,
                               networkWrite13, appliedWrite7, networkWrite14,
                               appliedWrite8, networkWrite15, appliedLocal,
                               valuesLocal, currentTerm, votedFor, log, state,
                               commitIndex, lastApplied, v, nextIndex,
                               matchIndex, votes, msg >>

server(self) == Start(self) \/ N1(self) \/ N5(self) \/ loop1(self)
                   \/ N2(self) \/ N3(self) \/ N4(self) \/ N6(self)
                   \/ N7(self) \/ loop2(self) \/ loop3(self) \/ N8(self)
                   \/ N9(self) \/ loop4(self) \/ N10(self) \/ loop5(self)

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