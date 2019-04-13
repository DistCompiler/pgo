------------- MODULE paxos --------------------
(*\* Paxos algorithm *)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT M, N, K, STOP, MAXB
ASSUME M \in Nat /\ N \in Nat /\ K \in Nat /\ M<=N /\ N < K
\* \* In the model, use M=2, N=3, STOP=5 (number of slots), MAXB=10

(***************************************************************************
\* 3/23
    \* 14:20 - 14:35
\* 3/26
    \* 13:00 - 13:15
\* 4/8
    \* 15:50 - 16:30
\* 4/9
    \* 13:00 - 13:45
    \* 15:45 - 16:00
    \* 16:35 - 17:40
\* 4/10
    \* 10:35 - 11:40
    \* 12:20 - 14:15
    \* 14:30 - 15:00 -- Finished spec
    \* 16:50 - 17:45 -- Work on conversion to PGo-Compilable
\* 4/11
    \* 13:30 - 15:15 

--mpcal Paxos {
  define {
      Proposer == 0..M-1
      Acceptor == M..N
      Learner == N+1..K
      \* \* M leaders, and N-M+1 acceptors
      Slots == 1..STOP
      Ballots == 0..MAXB
      PREPARE_MSG == 0
      PROMISE_MSG == 1
      PROPOSE_MSG == 2
      ACCEPT_MSG == 3
      CHOSEN_MSG == 4
  }

  macro Broadcast(mailboxes, msg, i, stop)
  {
      while (i <= stop) {
          mailboxes[i] := msg;
          i := i + 1;
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
  
    \* \* Acceptor process actions
  archetype ALearner(ref mailboxes)
  variable accepts={}, decided=[i \in Slots |-> {}], msg = [type |-> -1, sender |-> -1, bal |-> -1, val |-> -1, slot |-> -1, hv |-> {}];
  {
L:  while (TRUE) {
        msg := mailboxes[self];
L1:     if (msg.type = ACCEPT_MSG) {
            accepts := accepts \union {msg};
            if (Cardinality({a \in accepts: a.val = msg.val /\ a.slot = msg.slot /\ a.bal = msg.bal})*2 > Cardinality(Acceptor)) {
                decided[msg.slot] := decided[msg.slot] \union {msg.val};
            };
        };
    };
  }

  \* \* Acceptor process actions
  archetype AAcceptor(ref mailboxes)
  variable maxBal=-1, hVal={[slot |-> -1, bal |-> -1, val |-> -1]}, aidx=N+1,
           decided=[i \in Slots |-> {}], msg = [type |-> -1, sender |-> -1, bal |-> -1, val |-> -1, slot |-> -1, hv |-> {}];
  {
A:  while (TRUE) {
        msg := mailboxes[self];
A1:     if (msg.type = PREPARE_MSG /\ msg.bal > maxBal) {
A2:         maxBal := msg.bal;
            mailboxes[msg.sender] := [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, hv |-> hVal];
        } elseif (msg.type = PROPOSE_MSG /\ msg.bal >= maxBal) {
A3:         maxBal := msg.bal;
            aidx := N+1;
            hVal := hVal \union {[slot |-> msg.slot, bal |-> msg.bal, val |-> msg.val]};
            mailboxes[msg.sender] := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, hv |-> hVal];
loop2:      Broadcast(mailboxes, [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, hv |-> hVal], aidx, K);
        } elseif (msg.type = PROPOSE_MSG /\ msg.bal < maxBal) {
            mailboxes[msg.sender] := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, hv |-> hVal];
        }
    }
  }

\* \* Leader process
  archetype AProposer(ref mailboxes)
  variable b=-1, s=1, elected=FALSE, pVal={[slot |-> -1, bal |-> -1, val |-> -1]},
           promises=0, accepts=0, v=-1, resp=[type |-> -1, sender |-> -1, bal |-> -1, slot |-> -1, val |-> -1, hv |-> {}], idx=M;
  {
Pre:b := self;
P:  while (s \in Slots /\ b \in Ballots) {
P1:     if (elected) {
            accepts := 0;
            v := self;
P5:         if (Cardinality({pv \in pVal: pv.slot=s}) # 0) {
                with (w \in {pv \in pVal: pv.slot=s /\ \A pv2 \in pVal: pv.bal >= pv2.bal}) {
                    v := w.val;
                }
            };

loop1:      Broadcast(mailboxes, [type |-> PROPOSE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v], idx, N);
            idx := M;
            \* await responses, abort if necessary
search1:    while (accepts*2 < Cardinality(Acceptor) /\ elected) {
                \* Wait for accept message
                resp := mailboxes[self];
                assert(resp.type = ACCEPT_MSG);
                \* Is it still from a current term?
P6:             if (resp.bal > b \/ resp.slot # s \/ resp.val # v) {
                    \* Pre-empted by another proposer
                    elected := FALSE;
                } else {
                    accepts := accepts + 1;
                };
            };
            \* If still elected, then we must have a majority of accepts
P7:         if (elected) {
P8:             s := s + 1;
            };
        } else {
loop3:      Broadcast(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v], idx, N);
            idx := M;
            promises := 0;
            \* Wait for response from majority of acceptors
search2:    while (~elected) {
                \* Wait for promise
                resp := mailboxes[self];
                assert(resp.type = PROMISE_MSG);
                pVal := pVal \union resp.hv;
                \* Is it still from a current term?
P2:             if (resp.bal > b) {
                    \* Pre-empted, try again for election
                    b := b+M;
loop4:              Broadcast(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v], idx, N);
                    idx := M;
                } else {
P3:                 if (resp.bal = b) {
                        promises := promises + 1;
P4:                     if (promises*2 > Cardinality(Acceptor)) {
                            elected := TRUE;
                        };
                    };
                };
            };
        };
   }
  }
    variables
        network = [id \in 0..K |-> <<>>];

    fair process (proposer \in Proposer) == instance AProposer(ref network)
        mapping network[_] via FIFOChannel;

    fair process (acceptor \in Acceptor) == instance AAcceptor(ref network)
        mapping network[_] via FIFOChannel;
        
    fair process (learner \in Learner) == instance ALearner(ref network)
        mapping network[_] via FIFOChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm Paxos {
    variables network = [id \in (0) .. (K) |-> <<>>], mailboxesWrite, mailboxesWrite0, mailboxesRead, mailboxesWrite1, mailboxesWrite2, mailboxesRead0, mailboxesWrite3, mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, mailboxesRead1, mailboxesWrite7;
    define {
        Proposer == (0) .. ((M) - (1))
        Acceptor == (M) .. (N)
        Learner == ((N) + (1)) .. (K)
        Slots == (1) .. (STOP)
        Ballots == (0) .. (MAXB)
        PREPARE_MSG == 0
        PROMISE_MSG == 1
        PROPOSE_MSG == 2
        ACCEPT_MSG == 3
        CHOSEN_MSG == 4
    }
    fair process (proposer \in Proposer)
    variables b = -(1), s = 1, elected = FALSE, pVal = {[slot |-> -(1), bal |-> -(1), val |-> -(1)]}, promises = 0, accepts = 0, v = -(1), resp = [type |-> -(1), sender |-> -(1), bal |-> -(1), slot |-> -(1), val |-> -(1), hv |-> {}], idx = M;
    {
        Pre:
            b := self;
        P:
            if (((s) \in (Slots)) /\ ((b) \in (Ballots))) {
                P1:
                    if (elected) {
                        accepts := 0;
                        v := self;
                        P5:
                            if ((Cardinality({pv \in pVal : ((pv).slot) = (s)})) # (0)) {
                                with (w \in {pv \in pVal : (((pv).slot) = (s)) /\ (\A pv2 \in pVal : ((pv).bal) >= ((pv2).bal))}) {
                                    v := (w).val;
                                };
                            };
                        
                        loop1:
                            if ((idx) <= (N)) {
                                mailboxesWrite := [network EXCEPT ![idx] = Append(network[idx], [type |-> PROPOSE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v])];
                                idx := (idx) + (1);
                                mailboxesWrite0 := mailboxesWrite;
                                network := mailboxesWrite0;
                                goto loop1;
                            } else {
                                idx := M;
                                mailboxesWrite0 := network;
                                network := mailboxesWrite0;
                            };
                        
                        search1:
                            if ((((accepts) * (2)) < (Cardinality(Acceptor))) /\ (elected)) {
                                await (Len(network[self])) > (0);
                                with (msg0 = Head(network[self])) {
                                    mailboxesWrite := [network EXCEPT ![self] = Tail(network[self])];
                                    mailboxesRead := msg0;
                                };
                                resp := mailboxesRead;
                                assert ((resp).type) = (ACCEPT_MSG);
                                network := mailboxesWrite;
                                P6:
                                    if (((((resp).bal) > (b)) \/ (((resp).slot) # (s))) \/ (((resp).val) # (v))) {
                                        elected := FALSE;
                                        goto search1;
                                    } else {
                                        accepts := (accepts) + (1);
                                        goto search1;
                                    };
                            
                            };
                        
                        P7:
                            if (elected) {
                                P8:
                                    s := (s) + (1);
                                    goto P;
                            
                            } else {
                                goto P;
                            };
                    
                    } else {
                        loop3:
                            if ((idx) <= (N)) {
                                mailboxesWrite := [network EXCEPT ![idx] = Append(network[idx], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v])];
                                idx := (idx) + (1);
                                mailboxesWrite1 := mailboxesWrite;
                                network := mailboxesWrite1;
                                goto loop3;
                            } else {
                                idx := M;
                                promises := 0;
                                mailboxesWrite1 := network;
                                network := mailboxesWrite1;
                            };
                        
                        search2:
                            if (~(elected)) {
                                await (Len(network[self])) > (0);
                                with (msg1 = Head(network[self])) {
                                    mailboxesWrite := [network EXCEPT ![self] = Tail(network[self])];
                                    mailboxesRead := msg1;
                                };
                                resp := mailboxesRead;
                                assert ((resp).type) = (PROMISE_MSG);
                                pVal := (pVal) \union ((resp).hv);
                                network := mailboxesWrite;
                                P2:
                                    if (((resp).bal) > (b)) {
                                        b := (b) + (M);
                                        loop4:
                                            if ((idx) <= (N)) {
                                                mailboxesWrite := [network EXCEPT ![idx] = Append(network[idx], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> v])];
                                                idx := (idx) + (1);
                                                mailboxesWrite2 := mailboxesWrite;
                                                network := mailboxesWrite2;
                                                goto loop4;
                                            } else {
                                                idx := M;
                                                mailboxesWrite2 := network;
                                                network := mailboxesWrite2;
                                                goto search2;
                                            };
                                    
                                    } else {
                                        P3:
                                            if (((resp).bal) = (b)) {
                                                promises := (promises) + (1);
                                                P4:
                                                    if (((promises) * (2)) > (Cardinality(Acceptor))) {
                                                        elected := TRUE;
                                                        goto search2;
                                                    } else {
                                                        goto search2;
                                                    };
                                            
                                            } else {
                                                goto search2;
                                            };
                                    
                                    };
                            
                            } else {
                                goto P;
                            };
                    
                    };
            
            };
    
    }
    fair process (acceptor \in Acceptor)
    variables maxBal = -(1), hVal = {[slot |-> -(1), bal |-> -(1), val |-> -(1)]}, aidx = (N) + (1), decided = [i \in Slots |-> {}], msg = [type |-> -(1), sender |-> -(1), bal |-> -(1), val |-> -(1), slot |-> -(1), hv |-> {}];
    {
        A:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg2 = Head(network[self])) {
                    mailboxesWrite3 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead0 := msg2;
                };
                msg := mailboxesRead0;
                network := mailboxesWrite3;
                A1:
                    if ((((msg).type) = (PREPARE_MSG)) /\ (((msg).bal) > (maxBal))) {
                        A2:
                            maxBal := (msg).bal;
                            mailboxesWrite3 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, hv |-> hVal])];
                            network := mailboxesWrite3;
                            goto A;
                    
                    } else {
                        if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) >= (maxBal))) {
                            A3:
                                maxBal := (msg).bal;
                                aidx := (N) + (1);
                                hVal := (hVal) \union ({[slot |-> (msg).slot, bal |-> (msg).bal, val |-> (msg).val]});
                                mailboxesWrite3 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, hv |-> hVal])];
                                network := mailboxesWrite3;
                            
                            loop2:
                                if ((aidx) <= (K)) {
                                    mailboxesWrite3 := [network EXCEPT ![aidx] = Append(network[aidx], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, hv |-> hVal])];
                                    aidx := (aidx) + (1);
                                    mailboxesWrite4 := mailboxesWrite3;
                                    network := mailboxesWrite4;
                                    goto loop2;
                                } else {
                                    mailboxesWrite4 := network;
                                    network := mailboxesWrite4;
                                    goto A;
                                };
                        
                        } else {
                            if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) < (maxBal))) {
                                mailboxesWrite3 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, hv |-> hVal])];
                                mailboxesWrite5 := mailboxesWrite3;
                                mailboxesWrite6 := network;
                                network := mailboxesWrite6;
                                goto A;
                            } else {
                                mailboxesWrite5 := network;
                                mailboxesWrite6 := network;
                                network := mailboxesWrite6;
                                goto A;
                            };
                        };
                    };
            
            };
    
    }
    fair process (learner \in Learner)
    variables accepts = {}, decided = [i \in Slots |-> {}], msg = [type |-> -(1), sender |-> -(1), bal |-> -(1), val |-> -(1), slot |-> -(1), hv |-> {}];
    {
        L:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg3 = Head(network[self])) {
                    mailboxesWrite7 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead1 := msg3;
                };
                msg := mailboxesRead1;
                network := mailboxesWrite7;
                L1:
                    if (((msg).type) = (ACCEPT_MSG)) {
                        accepts := (accepts) \union ({msg});
                        if (((Cardinality({a \in accepts : ((((a).val) = ((msg).val)) /\ (((a).slot) = ((msg).slot))) /\ (((a).bal) = ((msg).bal))})) * (2)) > (Cardinality(Acceptor))) {
                            decided[(msg).slot] := (decided[(msg).slot]) \union ({(msg).val});
                            goto L;
                        } else {
                            goto L;
                        };
                    } else {
                        goto L;
                    };
            
            };
    
    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)

\* BEGIN TRANSLATION
\* Process variable accepts of process proposer at line 193 col 117 changed to accepts_
\* Process variable decided of process acceptor at line 325 col 102 changed to decided_
\* Process variable msg of process acceptor at line 325 col 134 changed to msg_
CONSTANT defaultInitValue
VARIABLES network, mailboxesWrite, mailboxesWrite0, mailboxesRead, 
          mailboxesWrite1, mailboxesWrite2, mailboxesRead0, mailboxesWrite3, 
          mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
          mailboxesWrite7, pc

(* define statement *)
Proposer == (0) .. ((M) - (1))
Acceptor == (M) .. (N)
Learner == ((N) + (1)) .. (K)
Slots == (1) .. (STOP)
Ballots == (0) .. (MAXB)
PREPARE_MSG == 0
PROMISE_MSG == 1
PROPOSE_MSG == 2
ACCEPT_MSG == 3
CHOSEN_MSG == 4

VARIABLES b, s, elected, pVal, promises, accepts_, v, resp, idx, maxBal, hVal, 
          aidx, decided_, msg_, accepts, decided, msg

vars == << network, mailboxesWrite, mailboxesWrite0, mailboxesRead, 
           mailboxesWrite1, mailboxesWrite2, mailboxesRead0, mailboxesWrite3, 
           mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
           mailboxesWrite7, pc, b, s, elected, pVal, promises, accepts_, v, 
           resp, idx, maxBal, hVal, aidx, decided_, msg_, accepts, decided, 
           msg >>

ProcSet == (Proposer) \cup (Acceptor) \cup (Learner)

Init == (* Global variables *)
        /\ network = [id \in (0) .. (K) |-> <<>>]
        /\ mailboxesWrite = defaultInitValue
        /\ mailboxesWrite0 = defaultInitValue
        /\ mailboxesRead = defaultInitValue
        /\ mailboxesWrite1 = defaultInitValue
        /\ mailboxesWrite2 = defaultInitValue
        /\ mailboxesRead0 = defaultInitValue
        /\ mailboxesWrite3 = defaultInitValue
        /\ mailboxesWrite4 = defaultInitValue
        /\ mailboxesWrite5 = defaultInitValue
        /\ mailboxesWrite6 = defaultInitValue
        /\ mailboxesRead1 = defaultInitValue
        /\ mailboxesWrite7 = defaultInitValue
        (* Process proposer *)
        /\ b = [self \in Proposer |-> -(1)]
        /\ s = [self \in Proposer |-> 1]
        /\ elected = [self \in Proposer |-> FALSE]
        /\ pVal = [self \in Proposer |-> {[slot |-> -(1), bal |-> -(1), val |-> -(1)]}]
        /\ promises = [self \in Proposer |-> 0]
        /\ accepts_ = [self \in Proposer |-> 0]
        /\ v = [self \in Proposer |-> -(1)]
        /\ resp = [self \in Proposer |-> [type |-> -(1), sender |-> -(1), bal |-> -(1), slot |-> -(1), val |-> -(1), hv |-> {}]]
        /\ idx = [self \in Proposer |-> M]
        (* Process acceptor *)
        /\ maxBal = [self \in Acceptor |-> -(1)]
        /\ hVal = [self \in Acceptor |-> {[slot |-> -(1), bal |-> -(1), val |-> -(1)]}]
        /\ aidx = [self \in Acceptor |-> (N) + (1)]
        /\ decided_ = [self \in Acceptor |-> [i \in Slots |-> {}]]
        /\ msg_ = [self \in Acceptor |-> [type |-> -(1), sender |-> -(1), bal |-> -(1), val |-> -(1), slot |-> -(1), hv |-> {}]]
        (* Process learner *)
        /\ accepts = [self \in Learner |-> {}]
        /\ decided = [self \in Learner |-> [i \in Slots |-> {}]]
        /\ msg = [self \in Learner |-> [type |-> -(1), sender |-> -(1), bal |-> -(1), val |-> -(1), slot |-> -(1), hv |-> {}]]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposer -> "Pre"
                                        [] self \in Acceptor -> "A"
                                        [] self \in Learner -> "L"]

Pre(self) == /\ pc[self] = "Pre"
             /\ b' = [b EXCEPT ![self] = self]
             /\ pc' = [pc EXCEPT ![self] = "P"]
             /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                             mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                             mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                             mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                             mailboxesWrite7, s, elected, pVal, promises, 
                             accepts_, v, resp, idx, maxBal, hVal, aidx, 
                             decided_, msg_, accepts, decided, msg >>

P(self) == /\ pc[self] = "P"
           /\ IF ((s[self]) \in (Slots)) /\ ((b[self]) \in (Ballots))
                 THEN /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                           mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                           mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                           mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                           mailboxesWrite7, b, s, elected, pVal, promises, 
                           accepts_, v, resp, idx, maxBal, hVal, aidx, 
                           decided_, msg_, accepts, decided, msg >>

P1(self) == /\ pc[self] = "P1"
            /\ IF elected[self]
                  THEN /\ accepts_' = [accepts_ EXCEPT ![self] = 0]
                       /\ v' = [v EXCEPT ![self] = self]
                       /\ pc' = [pc EXCEPT ![self] = "P5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "loop3"]
                       /\ UNCHANGED << accepts_, v >>
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, elected, pVal, promises, 
                            resp, idx, maxBal, hVal, aidx, decided_, msg_, 
                            accepts, decided, msg >>

P5(self) == /\ pc[self] = "P5"
            /\ IF (Cardinality({pv \in pVal[self] : ((pv).slot) = (s[self])})) # (0)
                  THEN /\ \E w \in {pv \in pVal[self] : (((pv).slot) = (s[self])) /\ (\A pv2 \in pVal[self] : ((pv).bal) >= ((pv2).bal))}:
                            v' = [v EXCEPT ![self] = (w).val]
                  ELSE /\ TRUE
                       /\ v' = v
            /\ pc' = [pc EXCEPT ![self] = "loop1"]
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, elected, pVal, promises, 
                            accepts_, resp, idx, maxBal, hVal, aidx, decided_, 
                            msg_, accepts, decided, msg >>

loop1(self) == /\ pc[self] = "loop1"
               /\ IF (idx[self]) <= (N)
                     THEN /\ mailboxesWrite' = [network EXCEPT ![idx[self]] = Append(network[idx[self]], [type |-> PROPOSE_MSG, bal |-> b[self], sender |-> self, slot |-> s[self], val |-> v[self]])]
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ mailboxesWrite0' = mailboxesWrite'
                          /\ network' = mailboxesWrite0'
                          /\ pc' = [pc EXCEPT ![self] = "loop1"]
                     ELSE /\ idx' = [idx EXCEPT ![self] = M]
                          /\ mailboxesWrite0' = network
                          /\ network' = mailboxesWrite0'
                          /\ pc' = [pc EXCEPT ![self] = "search1"]
                          /\ UNCHANGED mailboxesWrite
               /\ UNCHANGED << mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                               mailboxesRead0, mailboxesWrite3, 
                               mailboxesWrite4, mailboxesWrite5, 
                               mailboxesWrite6, mailboxesRead1, 
                               mailboxesWrite7, b, s, elected, pVal, promises, 
                               accepts_, v, resp, maxBal, hVal, aidx, decided_, 
                               msg_, accepts, decided, msg >>

search1(self) == /\ pc[self] = "search1"
                 /\ IF (((accepts_[self]) * (2)) < (Cardinality(Acceptor))) /\ (elected[self])
                       THEN /\ (Len(network[self])) > (0)
                            /\ LET msg0 == Head(network[self]) IN
                                 /\ mailboxesWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                 /\ mailboxesRead' = msg0
                            /\ resp' = [resp EXCEPT ![self] = mailboxesRead']
                            /\ Assert(((resp'[self]).type) = (ACCEPT_MSG), 
                                      "Failure of assertion at line 231, column 33.")
                            /\ network' = mailboxesWrite'
                            /\ pc' = [pc EXCEPT ![self] = "P6"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "P7"]
                            /\ UNCHANGED << network, mailboxesWrite, 
                                            mailboxesRead, resp >>
                 /\ UNCHANGED << mailboxesWrite0, mailboxesWrite1, 
                                 mailboxesWrite2, mailboxesRead0, 
                                 mailboxesWrite3, mailboxesWrite4, 
                                 mailboxesWrite5, mailboxesWrite6, 
                                 mailboxesRead1, mailboxesWrite7, b, s, 
                                 elected, pVal, promises, accepts_, v, idx, 
                                 maxBal, hVal, aidx, decided_, msg_, accepts, 
                                 decided, msg >>

P6(self) == /\ pc[self] = "P6"
            /\ IF ((((resp[self]).bal) > (b[self])) \/ (((resp[self]).slot) # (s[self]))) \/ (((resp[self]).val) # (v[self]))
                  THEN /\ elected' = [elected EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "search1"]
                       /\ UNCHANGED accepts_
                  ELSE /\ accepts_' = [accepts_ EXCEPT ![self] = (accepts_[self]) + (1)]
                       /\ pc' = [pc EXCEPT ![self] = "search1"]
                       /\ UNCHANGED elected
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, pVal, promises, v, resp, 
                            idx, maxBal, hVal, aidx, decided_, msg_, accepts, 
                            decided, msg >>

P7(self) == /\ pc[self] = "P7"
            /\ IF elected[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, elected, pVal, promises, 
                            accepts_, v, resp, idx, maxBal, hVal, aidx, 
                            decided_, msg_, accepts, decided, msg >>

P8(self) == /\ pc[self] = "P8"
            /\ s' = [s EXCEPT ![self] = (s[self]) + (1)]
            /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, elected, pVal, promises, 
                            accepts_, v, resp, idx, maxBal, hVal, aidx, 
                            decided_, msg_, accepts, decided, msg >>

loop3(self) == /\ pc[self] = "loop3"
               /\ IF (idx[self]) <= (N)
                     THEN /\ mailboxesWrite' = [network EXCEPT ![idx[self]] = Append(network[idx[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> s[self], val |-> v[self]])]
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ mailboxesWrite1' = mailboxesWrite'
                          /\ network' = mailboxesWrite1'
                          /\ pc' = [pc EXCEPT ![self] = "loop3"]
                          /\ UNCHANGED promises
                     ELSE /\ idx' = [idx EXCEPT ![self] = M]
                          /\ promises' = [promises EXCEPT ![self] = 0]
                          /\ mailboxesWrite1' = network
                          /\ network' = mailboxesWrite1'
                          /\ pc' = [pc EXCEPT ![self] = "search2"]
                          /\ UNCHANGED mailboxesWrite
               /\ UNCHANGED << mailboxesWrite0, mailboxesRead, mailboxesWrite2, 
                               mailboxesRead0, mailboxesWrite3, 
                               mailboxesWrite4, mailboxesWrite5, 
                               mailboxesWrite6, mailboxesRead1, 
                               mailboxesWrite7, b, s, elected, pVal, accepts_, 
                               v, resp, maxBal, hVal, aidx, decided_, msg_, 
                               accepts, decided, msg >>

search2(self) == /\ pc[self] = "search2"
                 /\ IF ~(elected[self])
                       THEN /\ (Len(network[self])) > (0)
                            /\ LET msg1 == Head(network[self]) IN
                                 /\ mailboxesWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                 /\ mailboxesRead' = msg1
                            /\ resp' = [resp EXCEPT ![self] = mailboxesRead']
                            /\ Assert(((resp'[self]).type) = (PROMISE_MSG), 
                                      "Failure of assertion at line 277, column 33.")
                            /\ pVal' = [pVal EXCEPT ![self] = (pVal[self]) \union ((resp'[self]).hv)]
                            /\ network' = mailboxesWrite'
                            /\ pc' = [pc EXCEPT ![self] = "P2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "P"]
                            /\ UNCHANGED << network, mailboxesWrite, 
                                            mailboxesRead, pVal, resp >>
                 /\ UNCHANGED << mailboxesWrite0, mailboxesWrite1, 
                                 mailboxesWrite2, mailboxesRead0, 
                                 mailboxesWrite3, mailboxesWrite4, 
                                 mailboxesWrite5, mailboxesWrite6, 
                                 mailboxesRead1, mailboxesWrite7, b, s, 
                                 elected, promises, accepts_, v, idx, maxBal, 
                                 hVal, aidx, decided_, msg_, accepts, decided, 
                                 msg >>

P2(self) == /\ pc[self] = "P2"
            /\ IF ((resp[self]).bal) > (b[self])
                  THEN /\ b' = [b EXCEPT ![self] = (b[self]) + (M)]
                       /\ pc' = [pc EXCEPT ![self] = "loop4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P3"]
                       /\ b' = b
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, s, elected, pVal, promises, 
                            accepts_, v, resp, idx, maxBal, hVal, aidx, 
                            decided_, msg_, accepts, decided, msg >>

loop4(self) == /\ pc[self] = "loop4"
               /\ IF (idx[self]) <= (N)
                     THEN /\ mailboxesWrite' = [network EXCEPT ![idx[self]] = Append(network[idx[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> s[self], val |-> v[self]])]
                          /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                          /\ mailboxesWrite2' = mailboxesWrite'
                          /\ network' = mailboxesWrite2'
                          /\ pc' = [pc EXCEPT ![self] = "loop4"]
                     ELSE /\ idx' = [idx EXCEPT ![self] = M]
                          /\ mailboxesWrite2' = network
                          /\ network' = mailboxesWrite2'
                          /\ pc' = [pc EXCEPT ![self] = "search2"]
                          /\ UNCHANGED mailboxesWrite
               /\ UNCHANGED << mailboxesWrite0, mailboxesRead, mailboxesWrite1, 
                               mailboxesRead0, mailboxesWrite3, 
                               mailboxesWrite4, mailboxesWrite5, 
                               mailboxesWrite6, mailboxesRead1, 
                               mailboxesWrite7, b, s, elected, pVal, promises, 
                               accepts_, v, resp, maxBal, hVal, aidx, decided_, 
                               msg_, accepts, decided, msg >>

P3(self) == /\ pc[self] = "P3"
            /\ IF ((resp[self]).bal) = (b[self])
                  THEN /\ promises' = [promises EXCEPT ![self] = (promises[self]) + (1)]
                       /\ pc' = [pc EXCEPT ![self] = "P4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "search2"]
                       /\ UNCHANGED promises
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, elected, pVal, accepts_, v, 
                            resp, idx, maxBal, hVal, aidx, decided_, msg_, 
                            accepts, decided, msg >>

P4(self) == /\ pc[self] = "P4"
            /\ IF ((promises[self]) * (2)) > (Cardinality(Acceptor))
                  THEN /\ elected' = [elected EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "search2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "search2"]
                       /\ UNCHANGED elected
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, pVal, promises, accepts_, v, 
                            resp, idx, maxBal, hVal, aidx, decided_, msg_, 
                            accepts, decided, msg >>

proposer(self) == Pre(self) \/ P(self) \/ P1(self) \/ P5(self)
                     \/ loop1(self) \/ search1(self) \/ P6(self)
                     \/ P7(self) \/ P8(self) \/ loop3(self)
                     \/ search2(self) \/ P2(self) \/ loop4(self)
                     \/ P3(self) \/ P4(self)

A(self) == /\ pc[self] = "A"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg2 == Head(network[self]) IN
                           /\ mailboxesWrite3' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead0' = msg2
                      /\ msg_' = [msg_ EXCEPT ![self] = mailboxesRead0']
                      /\ network' = mailboxesWrite3'
                      /\ pc' = [pc EXCEPT ![self] = "A1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << network, mailboxesRead0, mailboxesWrite3, 
                                      msg_ >>
           /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                           mailboxesWrite1, mailboxesWrite2, mailboxesWrite4, 
                           mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                           mailboxesWrite7, b, s, elected, pVal, promises, 
                           accepts_, v, resp, idx, maxBal, hVal, aidx, 
                           decided_, accepts, decided, msg >>

A1(self) == /\ pc[self] = "A1"
            /\ IF (((msg_[self]).type) = (PREPARE_MSG)) /\ (((msg_[self]).bal) > (maxBal[self]))
                  THEN /\ pc' = [pc EXCEPT ![self] = "A2"]
                       /\ UNCHANGED << network, mailboxesWrite3, 
                                       mailboxesWrite5, mailboxesWrite6 >>
                  ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) >= (maxBal[self]))
                             THEN /\ pc' = [pc EXCEPT ![self] = "A3"]
                                  /\ UNCHANGED << network, mailboxesWrite3, 
                                                  mailboxesWrite5, 
                                                  mailboxesWrite6 >>
                             ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) < (maxBal[self]))
                                        THEN /\ mailboxesWrite3' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, hv |-> hVal[self]])]
                                             /\ mailboxesWrite5' = mailboxesWrite3'
                                             /\ mailboxesWrite6' = network
                                             /\ network' = mailboxesWrite6'
                                             /\ pc' = [pc EXCEPT ![self] = "A"]
                                        ELSE /\ mailboxesWrite5' = network
                                             /\ mailboxesWrite6' = network
                                             /\ network' = mailboxesWrite6'
                                             /\ pc' = [pc EXCEPT ![self] = "A"]
                                             /\ UNCHANGED mailboxesWrite3
            /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                            mailboxesWrite1, mailboxesWrite2, mailboxesRead0, 
                            mailboxesWrite4, mailboxesRead1, mailboxesWrite7, 
                            b, s, elected, pVal, promises, accepts_, v, resp, 
                            idx, maxBal, hVal, aidx, decided_, msg_, accepts, 
                            decided, msg >>

A2(self) == /\ pc[self] = "A2"
            /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
            /\ mailboxesWrite3' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, hv |-> hVal[self]])]
            /\ network' = mailboxesWrite3'
            /\ pc' = [pc EXCEPT ![self] = "A"]
            /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                            mailboxesWrite1, mailboxesWrite2, mailboxesRead0, 
                            mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, 
                            mailboxesRead1, mailboxesWrite7, b, s, elected, 
                            pVal, promises, accepts_, v, resp, idx, hVal, aidx, 
                            decided_, msg_, accepts, decided, msg >>

A3(self) == /\ pc[self] = "A3"
            /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
            /\ aidx' = [aidx EXCEPT ![self] = (N) + (1)]
            /\ hVal' = [hVal EXCEPT ![self] = (hVal[self]) \union ({[slot |-> (msg_[self]).slot, bal |-> (msg_[self]).bal, val |-> (msg_[self]).val]})]
            /\ mailboxesWrite3' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, hv |-> hVal'[self]])]
            /\ network' = mailboxesWrite3'
            /\ pc' = [pc EXCEPT ![self] = "loop2"]
            /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                            mailboxesWrite1, mailboxesWrite2, mailboxesRead0, 
                            mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, 
                            mailboxesRead1, mailboxesWrite7, b, s, elected, 
                            pVal, promises, accepts_, v, resp, idx, decided_, 
                            msg_, accepts, decided, msg >>

loop2(self) == /\ pc[self] = "loop2"
               /\ IF (aidx[self]) <= (K)
                     THEN /\ mailboxesWrite3' = [network EXCEPT ![aidx[self]] = Append(network[aidx[self]], [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, hv |-> hVal[self]])]
                          /\ aidx' = [aidx EXCEPT ![self] = (aidx[self]) + (1)]
                          /\ mailboxesWrite4' = mailboxesWrite3'
                          /\ network' = mailboxesWrite4'
                          /\ pc' = [pc EXCEPT ![self] = "loop2"]
                     ELSE /\ mailboxesWrite4' = network
                          /\ network' = mailboxesWrite4'
                          /\ pc' = [pc EXCEPT ![self] = "A"]
                          /\ UNCHANGED << mailboxesWrite3, aidx >>
               /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                               mailboxesWrite1, mailboxesWrite2, 
                               mailboxesRead0, mailboxesWrite5, 
                               mailboxesWrite6, mailboxesRead1, 
                               mailboxesWrite7, b, s, elected, pVal, promises, 
                               accepts_, v, resp, idx, maxBal, hVal, decided_, 
                               msg_, accepts, decided, msg >>

acceptor(self) == A(self) \/ A1(self) \/ A2(self) \/ A3(self)
                     \/ loop2(self)

L(self) == /\ pc[self] = "L"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg3 == Head(network[self]) IN
                           /\ mailboxesWrite7' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead1' = msg3
                      /\ msg' = [msg EXCEPT ![self] = mailboxesRead1']
                      /\ network' = mailboxesWrite7'
                      /\ pc' = [pc EXCEPT ![self] = "L1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << network, mailboxesRead1, mailboxesWrite7, 
                                      msg >>
           /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead, 
                           mailboxesWrite1, mailboxesWrite2, mailboxesRead0, 
                           mailboxesWrite3, mailboxesWrite4, mailboxesWrite5, 
                           mailboxesWrite6, b, s, elected, pVal, promises, 
                           accepts_, v, resp, idx, maxBal, hVal, aidx, 
                           decided_, msg_, accepts, decided >>

L1(self) == /\ pc[self] = "L1"
            /\ IF ((msg[self]).type) = (ACCEPT_MSG)
                  THEN /\ accepts' = [accepts EXCEPT ![self] = (accepts[self]) \union ({msg[self]})]
                       /\ IF ((Cardinality({a \in accepts'[self] : ((((a).val) = ((msg[self]).val)) /\ (((a).slot) = ((msg[self]).slot))) /\ (((a).bal) = ((msg[self]).bal))})) * (2)) > (Cardinality(Acceptor))
                             THEN /\ decided' = [decided EXCEPT ![self][(msg[self]).slot] = (decided[self][(msg[self]).slot]) \union ({(msg[self]).val})]
                                  /\ pc' = [pc EXCEPT ![self] = "L"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "L"]
                                  /\ UNCHANGED decided
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L"]
                       /\ UNCHANGED << accepts, decided >>
            /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0, 
                            mailboxesRead, mailboxesWrite1, mailboxesWrite2, 
                            mailboxesRead0, mailboxesWrite3, mailboxesWrite4, 
                            mailboxesWrite5, mailboxesWrite6, mailboxesRead1, 
                            mailboxesWrite7, b, s, elected, pVal, promises, 
                            accepts_, v, resp, idx, maxBal, hVal, aidx, 
                            decided_, msg_, msg >>

learner(self) == L(self) \/ L1(self)

Next == (\E self \in Proposer: proposer(self))
           \/ (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Learner: learner(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proposer : WF_vars(proposer(self))
        /\ \A self \in Acceptor : WF_vars(acceptor(self))
        /\ \A self \in Learner : WF_vars(learner(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\*\*  No acceptor could have finalized/decided 2 different vals for same slot 
\*\* check the two below as invariant
Agreement == \A a1,a2 \in Learner: 
              \A k \in Slots: Cardinality(decided[a1][k])=1 
                           /\ Cardinality(decided[a2][k])=1 => decided[a1][k]=decided[a2][k]

Agreement2 == \A i \in Learner: 
               \A k \in 1..STOP: Cardinality(decided[i][k]) <=1


\* \* Short cut for the above

Agreement3 == \A i \in Learner: 
               \A k \in 1..STOP: Cardinality(decided[i][k]) <=1


\* Of course this is violated! Don't check this as invariant
No2Leaders == \A i,j \in Proposer : elected[i] /\ elected[j] => i=j

\* Agreement ==
\*    \A i,j \in Acceptor : 
\*        (   accepted[i] \subseteq accepted[j] 
\*         \/ accepted[j] \subseteq accepted[i] )
=========================================================
