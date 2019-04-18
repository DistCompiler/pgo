------------- MODULE paxos --------------------
(*\* Paxos algorithm *)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NUM_PROPOSERS, NUM_ACCEPTORS, NUM_LEARNERS, NUM_SLOTS, MAX_BALLOTS

ASSUME /\ NUM_PROPOSERS \in Nat
       /\ NUM_ACCEPTORS \in Nat
       /\ NUM_LEARNERS \in Nat

CONSTANT NULL
ASSUME NULL \notin 1..NUM_SLOTS

AllNodes == 0..(NUM_PROPOSERS+NUM_ACCEPTORS+NUM_LEARNERS-1)

(***************************************************************************
--mpcal Paxos {
  define {
      Proposer == 0..NUM_PROPOSERS-1
      Acceptor == NUM_PROPOSERS..(NUM_PROPOSERS+NUM_ACCEPTORS-1)
      Learner == (NUM_PROPOSERS+NUM_ACCEPTORS)..(NUM_PROPOSERS+NUM_ACCEPTORS+NUM_LEARNERS-1)
      Slots == 1..NUM_SLOTS
      Ballots == 0..MAX_BALLOTS
      PREPARE_MSG == 0
      PROMISE_MSG == 1
      PROPOSE_MSG == 2
      ACCEPT_MSG == 3
      REJECT_MSG == 4
  }

  \* Broadcasts to nodes in range i..stop.
  macro Broadcast(mailboxes, msg, i, stop)
  {
      while (i <= stop) {
          mailboxes[i] := msg;
          i := i + 1;
      };
  }

  macro BroadcastLearners(mailboxes, msg, i)
  {
      Broadcast(mailboxes, msg, i, NUM_PROPOSERS+NUM_ACCEPTORS+NUM_LEARNERS-1);
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

  \* Defines how variables get applied to the state machine
  mapping macro Log {
      read {
          assert(FALSE);
      }

      write {
          \* make sure that, when a value is being accepted for a slot, either there was no
          \* value for that slot yet, or the value being decided on is the same as previously
          \* decided.
          assert($variable = NULL \/ $variable = $value);
          yield $value;
      }
  }

  archetype ALearner(ref mailboxes, ref decided)
  variables accepts = <<>>,
            numAccepted = 0,
            iterator,
            entry,
            msg;
  {
L:  while (TRUE) {
        msg := mailboxes[self];
        \* Add new accepts to record
LGotAcc: if (msg.type = ACCEPT_MSG) {
            accepts := Append(accepts, msg);
            iterator := 1;
            numAccepted := 0;
            \* Count the number of equivalent accepts to the received message
LCheckMajority: while (iterator <= Len(accepts)) {
                entry := accepts[iterator];
                if (entry.slot = msg.slot /\ entry.bal = msg.bal /\ entry.val = msg.val) {
                    numAccepted := numAccepted + 1;
                };
                iterator := iterator + 1;
            };

            \* Checks whether the majority of acceptors accepted a value for the current slot
            if (numAccepted*2 > Cardinality(Acceptor)) {
                decided[msg.slot] := msg.val;

                \* garbage collect: no longer need to keep previously accepted values
                \* TODO: I don't think this is legal actually
                accepts := <<>>;
            };
        };
    };
  }

  \* maxBal is monotonically increasing over time
  archetype AAcceptor(ref mailboxes)
  variables maxBal = -1,
            loopIndex,
            acceptedValues = <<>>,
            payload,
            msg;
  {
A:  while (TRUE) {
        \* Acceptors just listen for and respond to messages from proposers
        msg := mailboxes[self];
AMsgSwitch: if (msg.type = PREPARE_MSG /\ msg.bal > maxBal) { \* Essentially voting for a new leader, ensures no values with a ballot less than the new ballot are ever accepted
APrepare:   maxBal := msg.bal;
            \* Respond with promise to reject all proposals with a lower ballot number
            mailboxes[msg.sender] := [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal, slot |-> NULL, val |-> NULL, accepted |-> acceptedValues];

        } elseif (msg.type = PROPOSE_MSG /\ msg.bal >= maxBal) { \* Accept valid proposals. Invariants are maintained by the proposer so no need to check the value
            \* Update max ballot
APropose:   maxBal := msg.bal;
            payload := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, accepted |-> <<>>];

            \* Add the value to the list of accepted values
            acceptedValues := Append(acceptedValues, [slot |-> msg.slot, bal |-> msg.bal, val |-> msg.val]);
            \* Respond that the proposal was accepted
            mailboxes[msg.sender] := payload;

            loopIndex := NUM_PROPOSERS+NUM_ACCEPTORS;
            \* Inform the learners of the accept
ANotifyLearners: BroadcastLearners(mailboxes, payload, loopIndex);

        } elseif (msg.type = PROPOSE_MSG /\ msg.bal < maxBal) { \* Reject invalid proposals to maintain promises
ABadPropose: mailboxes[msg.sender] := [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, accepted |-> <<>>];
        }
    }
  }

  \* Key idea: Proposer must have received promises from majority, so it knows about every chosen value before it attempts to propose a value for a given slot
  archetype AProposer(ref mailboxes)
  variables b, \* local ballot
            s = 1, \* current slot
            elected = FALSE,
            acceptedValues = <<>>,
            max = [slot |-> -1, bal |-> -1, val |-> -1],
            index, \* temporary variable for iteration
            entry,
            promises,
            accepts = 0,
            value,
            resp;
  {
Pre:b := self;
P:  while (s \in Slots) {
PLeaderCheck: if (elected) { \* This proposer thinks it is the distinguished proposer
            \***********
            \* PHASE 2
            \***********
            accepts := 0;
            \* Default value is myself (TODO: Make this come from an archetype parameter)
            value := self;
            index := 1;
            \* Make sure the value proposed is the same as the value of the accepted proposal with the highest ballot (if such a value exists)
PFindMaxVal: while (index <= Len(acceptedValues)) {
                entry := acceptedValues[index];
                if (entry.slot = s /\ entry.bal >= max.bal) {
                    value := entry.val;
                    max := entry;
                };
                index := index + 1;
            };

            index := NUM_PROPOSERS;
            \* Send Propose message to every acceptor
PSendProposes: Broadcast(mailboxes, [type |-> PROPOSE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> value], index, NUM_PROPOSERS+NUM_ACCEPTORS-1);

            \* Await responses, abort if necessary
PSearchAccs: while (accepts*2 < Cardinality(Acceptor) /\ elected) {
                \* Wait for response
                resp := mailboxes[self];
                if (resp.type = ACCEPT_MSG) {
                    \* Is it valid?
                    if (resp.bal = b /\ resp.slot = s /\ resp.val = value) {
                        accepts := accepts + 1;
                    };
                } elseif (resp.type = REJECT_MSG) {
                    \* Pre-empted by another proposer (this is no longer the distinguished proposer)
                    elected := FALSE;
                }
            };
            \* If still elected, then we must have a majority of accepts, so we can try to find a value for the next slot
PIncSlot:   if (elected) {
               s := s + 1;
            };
        } else { \* Try to become elected the distiguished proposer (TODO: only do so initially and on timeout)
            \***********
            \* PHASE 1
            \***********
            index := NUM_PROPOSERS;
            \* Send prepares to every acceptor
PReqVotes:  Broadcast(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL], index, NUM_PROPOSERS+NUM_ACCEPTORS-1);
            promises := 0;
            \* Wait for response from majority of acceptors
PCandidate: while (~elected) {
                \* Wait for promise
                resp := mailboxes[self];
                if (resp.type = PROMISE_MSG) {
                    acceptedValues := acceptedValues \o resp.accepted;

                    \* Is it still from a current term?
PGotPromise:        if (resp.bal > b) {
                        \* Pre-empted, try again for election
                        b := b+NUM_PROPOSERS; \* to remain unique
                        index := NUM_PROPOSERS;
PReSendReqVotes:        Broadcast(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL], index, NUM_PROPOSERS+NUM_ACCEPTORS-1);
                    } else {
PCheckElected:          if (resp.bal = b) {
                            promises := promises + 1;
                            \* Check if a majority of acceptors think that this proposer is the distinguished proposer, if so, become the leader
PBecomeLeader:              if (promises*2 > Cardinality(Acceptor)) {
                                elected := TRUE;
                            };
                        };
                    };
                };
            };
        };
   }
  }
    variables
        network = [id \in AllNodes |-> <<>>];

    fair process (proposer \in Proposer) == instance AProposer(ref network)
        mapping network[_] via FIFOChannel;

    fair process (acceptor \in Acceptor) == instance AAcceptor(ref network)
        mapping network[_] via FIFOChannel;

    fair process (learner \in Learner) == instance ALearner(ref network, [slot \in Slots |-> NULL])
        mapping @2[_] via Log
        mapping network[_] via FIFOChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm Paxos {
    variables network = [id \in AllNodes |-> <<>>], mailboxesWrite, mailboxesWrite0, mailboxesRead, mailboxesWrite1, mailboxesWrite2, mailboxesWrite3, mailboxesWrite4, mailboxesWrite5, mailboxesWrite6, mailboxesWrite7, mailboxesRead0, mailboxesWrite8, mailboxesWrite9, mailboxesWrite10, mailboxesWrite11, mailboxesWrite12, mailboxesWrite13, mailboxesRead1, mailboxesWrite14, decidedWrite, decidedWrite0, decidedWrite1, decidedWrite2, decidedWrite3;
    define {
        Proposer == (0) .. ((NUM_PROPOSERS) - (1))
        Acceptor == (NUM_PROPOSERS) .. ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))
        Learner == ((NUM_PROPOSERS) + (NUM_ACCEPTORS)) .. (((NUM_PROPOSERS) + (NUM_ACCEPTORS)) + ((NUM_LEARNERS) - (1)))
        Slots == (1) .. (NUM_SLOTS)
        Ballots == (0) .. (MAX_BALLOTS)
        PREPARE_MSG == 0
        PROMISE_MSG == 1
        PROPOSE_MSG == 2
        ACCEPT_MSG == 3
        REJECT_MSG == 4
    }
    fair process (proposer \in Proposer)
    variables b, s = 1, elected = FALSE, acceptedValues = <<>>, max = [slot |-> -(1), bal |-> -(1), val |-> -(1)], index, entry, promises, accepts = 0, value, resp;
    {
        Pre:
            b := self;
        P:
            if ((s) \in (Slots)) {
                PLeaderCheck:
                    if (elected) {
                        accepts := 0;
                        value := self;
                        index := 1;
                        PFindMaxVal:
                            if ((index) <= (Len(acceptedValues))) {
                                entry := acceptedValues[index];
                                if ((((entry).slot) = (s)) /\ (((entry).bal) >= ((max).bal))) {
                                    value := (entry).val;
                                    max := entry;
                                };
                                index := (index) + (1);
                                goto PFindMaxVal;
                            } else {
                                index := NUM_PROPOSERS;
                            };

                        PSendProposes:
                            if ((index) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))) {
                                mailboxesWrite := [network EXCEPT ![index] = Append(network[index], [type |-> PROPOSE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> value])];
                                index := (index) + (1);
                                mailboxesWrite0 := mailboxesWrite;
                                network := mailboxesWrite0;
                                goto PSendProposes;
                            } else {
                                mailboxesWrite0 := network;
                                network := mailboxesWrite0;
                            };

                        PSearchAccs:
                            if ((((accepts) * (2)) < (Cardinality(Acceptor))) /\ (elected)) {
                                await (Len(network[self])) > (0);
                                with (msg0 = Head(network[self])) {
                                    mailboxesWrite := [network EXCEPT ![self] = Tail(network[self])];
                                    mailboxesRead := msg0;
                                };
                                resp := mailboxesRead;
                                if (((resp).type) = (ACCEPT_MSG)) {
                                    if (((((resp).bal) = (b)) /\ (((resp).slot) = (s))) /\ (((resp).val) = (value))) {
                                        accepts := (accepts) + (1);
                                        network := mailboxesWrite;
                                        goto PSearchAccs;
                                    } else {
                                        network := mailboxesWrite;
                                        goto PSearchAccs;
                                    };
                                } else {
                                    if (((resp).type) = (REJECT_MSG)) {
                                        elected := FALSE;
                                        network := mailboxesWrite;
                                        goto PSearchAccs;
                                    } else {
                                        network := mailboxesWrite;
                                        goto PSearchAccs;
                                    };
                                };
                            } else {
                                network := mailboxesWrite;
                            };

                        PIncSlot:
                            if (elected) {
                                s := (s) + (1);
                                goto P;
                            } else {
                                goto P;
                            };

                    } else {
                        index := NUM_PROPOSERS;
                        PReqVotes:
                            if ((index) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))) {
                                mailboxesWrite := [network EXCEPT ![index] = Append(network[index], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL])];
                                index := (index) + (1);
                                mailboxesWrite1 := mailboxesWrite;
                                network := mailboxesWrite1;
                                goto PReqVotes;
                            } else {
                                promises := 0;
                                mailboxesWrite1 := network;
                                network := mailboxesWrite1;
                            };

                        PCandidate:
                            if (~(elected)) {
                                await (Len(network[self])) > (0);
                                with (msg1 = Head(network[self])) {
                                    mailboxesWrite := [network EXCEPT ![self] = Tail(network[self])];
                                    mailboxesRead := msg1;
                                };
                                resp := mailboxesRead;
                                if (((resp).type) = (PROMISE_MSG)) {
                                    acceptedValues := (acceptedValues) \o ((resp).accepted);
                                    network := mailboxesWrite;
                                    PGotPromise:
                                        if (((resp).bal) > (b)) {
                                            b := (b) + (NUM_PROPOSERS);
                                            index := NUM_PROPOSERS;
                                            PReSendReqVotes:
                                                if ((index) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))) {
                                                    mailboxesWrite := [network EXCEPT ![index] = Append(network[index], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL])];
                                                    index := (index) + (1);
                                                    mailboxesWrite2 := mailboxesWrite;
                                                    network := mailboxesWrite2;
                                                    goto PReSendReqVotes;
                                                } else {
                                                    mailboxesWrite2 := network;
                                                    network := mailboxesWrite2;
                                                    goto PCandidate;
                                                };

                                        } else {
                                            PCheckElected:
                                                if (((resp).bal) = (b)) {
                                                    promises := (promises) + (1);
                                                    PBecomeLeader:
                                                        if (((promises) * (2)) > (Cardinality(Acceptor))) {
                                                            elected := TRUE;
                                                            goto PCandidate;
                                                        } else {
                                                            goto PCandidate;
                                                        };

                                                } else {
                                                    goto PCandidate;
                                                };

                                        };

                                } else {
                                    mailboxesWrite4 := network;
                                    mailboxesWrite5 := mailboxesWrite4;
                                    network := mailboxesWrite5;
                                    goto PCandidate;
                                };
                            } else {
                                mailboxesWrite5 := network;
                                network := mailboxesWrite5;
                                goto P;
                            };

                    };

            } else {
                mailboxesWrite7 := network;
                network := mailboxesWrite7;
            };

    }
    fair process (acceptor \in Acceptor)
    variables maxBal = -(1), loopIndex, acceptedValues = <<>>, payload, msg;
    {
        A:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg2 = Head(network[self])) {
                    mailboxesWrite8 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead0 := msg2;
                };
                msg := mailboxesRead0;
                network := mailboxesWrite8;
                AMsgSwitch:
                    if ((((msg).type) = (PREPARE_MSG)) /\ (((msg).bal) > (maxBal))) {
                        APrepare:
                            maxBal := (msg).bal;
                            mailboxesWrite8 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal, slot |-> NULL, val |-> NULL, accepted |-> acceptedValues])];
                            network := mailboxesWrite8;
                            goto A;

                    } else {
                        if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) >= (maxBal))) {
                            APropose:
                                maxBal := (msg).bal;
                                payload := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, accepted |-> <<>>];
                                acceptedValues := Append(acceptedValues, [slot |-> (msg).slot, bal |-> (msg).bal, val |-> (msg).val]);
                                mailboxesWrite8 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], payload)];
                                loopIndex := (NUM_PROPOSERS) + (NUM_ACCEPTORS);
                                network := mailboxesWrite8;

                            ANotifyLearners:
                                if ((loopIndex) <= (((NUM_PROPOSERS) + (NUM_ACCEPTORS)) + ((NUM_LEARNERS) - (1)))) {
                                    mailboxesWrite8 := [network EXCEPT ![loopIndex] = Append(network[loopIndex], payload)];
                                    loopIndex := (loopIndex) + (1);
                                    mailboxesWrite9 := mailboxesWrite8;
                                    network := mailboxesWrite9;
                                    goto ANotifyLearners;
                                } else {
                                    mailboxesWrite9 := network;
                                    network := mailboxesWrite9;
                                    goto A;
                                };

                        } else {
                            if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) < (maxBal))) {
                                ABadPropose:
                                    mailboxesWrite8 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, accepted |-> <<>>])];
                                    network := mailboxesWrite8;
                                    goto A;

                            } else {
                                mailboxesWrite10 := network;
                                mailboxesWrite11 := mailboxesWrite10;
                                mailboxesWrite12 := mailboxesWrite11;
                                network := mailboxesWrite12;
                                goto A;
                            };
                        };
                    };

            } else {
                mailboxesWrite13 := network;
                network := mailboxesWrite13;
            };

    }
    fair process (learner \in Learner)
    variables decidedLocal = [slot \in Slots |-> NULL], accepts = <<>>, numAccepted = 0, iterator, entry, msg;
    {
        L:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg3 = Head(network[self])) {
                    mailboxesWrite14 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead1 := msg3;
                };
                msg := mailboxesRead1;
                network := mailboxesWrite14;
                LGotAcc:
                    if (((msg).type) = (ACCEPT_MSG)) {
                        accepts := Append(accepts, msg);
                        iterator := 1;
                        numAccepted := 0;
                        LCheckMajority:
                            if ((iterator) <= (Len(accepts))) {
                                entry := accepts[iterator];
                                if (((((entry).slot) = ((msg).slot)) /\ (((entry).bal) = ((msg).bal))) /\ (((entry).val) = ((msg).val))) {
                                    numAccepted := (numAccepted) + (1);
                                };
                                iterator := (iterator) + (1);
                                decidedWrite1 := decidedLocal;
                                decidedLocal := decidedWrite1;
                                goto LCheckMajority;
                            } else {
                                if (((numAccepted) * (2)) > (Cardinality(Acceptor))) {
                                    assert ((decidedLocal[(msg).slot]) = (NULL)) \/ ((decidedLocal[(msg).slot]) = ((msg).val));
                                    decidedWrite := [decidedLocal EXCEPT ![(msg).slot] = (msg).val];
                                    accepts := <<>>;
                                    decidedWrite0 := decidedWrite;
                                    decidedWrite1 := decidedWrite0;
                                    decidedLocal := decidedWrite1;
                                    goto L;
                                } else {
                                    decidedWrite0 := decidedLocal;
                                    decidedWrite1 := decidedWrite0;
                                    decidedLocal := decidedWrite1;
                                    goto L;
                                };
                            };

                    } else {
                        decidedWrite2 := decidedLocal;
                        decidedLocal := decidedWrite2;
                        goto L;
                    };

            } else {
                decidedWrite3 := decidedLocal;
                decidedLocal := decidedWrite3;
            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)

\* BEGIN TRANSLATION
\* Process variable acceptedValues of process proposer at line 266 col 42 changed to acceptedValues_
\* Process variable entry of process proposer at line 266 col 123 changed to entry_
\* Process variable accepts of process proposer at line 266 col 140 changed to accepts_
\* Process variable msg of process acceptor at line 423 col 73 changed to msg_
CONSTANT defaultInitValue
VARIABLES network, mailboxesWrite, mailboxesWrite0, mailboxesRead,
          mailboxesWrite1, mailboxesWrite2, mailboxesWrite3, mailboxesWrite4,
          mailboxesWrite5, mailboxesWrite6, mailboxesWrite7, mailboxesRead0,
          mailboxesWrite8, mailboxesWrite9, mailboxesWrite10,
          mailboxesWrite11, mailboxesWrite12, mailboxesWrite13,
          mailboxesRead1, mailboxesWrite14, decidedWrite, decidedWrite0,
          decidedWrite1, decidedWrite2, decidedWrite3, pc

(* define statement *)
Proposer == (0) .. ((NUM_PROPOSERS) - (1))
Acceptor == (NUM_PROPOSERS) .. ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))
Learner == ((NUM_PROPOSERS) + (NUM_ACCEPTORS)) .. (((NUM_PROPOSERS) + (NUM_ACCEPTORS)) + ((NUM_LEARNERS) - (1)))
Slots == (1) .. (NUM_SLOTS)
Ballots == (0) .. (MAX_BALLOTS)
PREPARE_MSG == 0
PROMISE_MSG == 1
PROPOSE_MSG == 2
ACCEPT_MSG == 3
REJECT_MSG == 4

VARIABLES b, s, elected, acceptedValues_, max, index, entry_, promises,
          accepts_, value, resp, maxBal, loopIndex, acceptedValues, payload,
          msg_, decidedLocal, accepts, numAccepted, iterator, entry, msg

vars == << network, mailboxesWrite, mailboxesWrite0, mailboxesRead,
           mailboxesWrite1, mailboxesWrite2, mailboxesWrite3, mailboxesWrite4,
           mailboxesWrite5, mailboxesWrite6, mailboxesWrite7, mailboxesRead0,
           mailboxesWrite8, mailboxesWrite9, mailboxesWrite10,
           mailboxesWrite11, mailboxesWrite12, mailboxesWrite13,
           mailboxesRead1, mailboxesWrite14, decidedWrite, decidedWrite0,
           decidedWrite1, decidedWrite2, decidedWrite3, pc, b, s, elected,
           acceptedValues_, max, index, entry_, promises, accepts_, value,
           resp, maxBal, loopIndex, acceptedValues, payload, msg_,
           decidedLocal, accepts, numAccepted, iterator, entry, msg >>

ProcSet == (Proposer) \cup (Acceptor) \cup (Learner)

Init == (* Global variables *)
        /\ network = [id \in AllNodes |-> <<>>]
        /\ mailboxesWrite = defaultInitValue
        /\ mailboxesWrite0 = defaultInitValue
        /\ mailboxesRead = defaultInitValue
        /\ mailboxesWrite1 = defaultInitValue
        /\ mailboxesWrite2 = defaultInitValue
        /\ mailboxesWrite3 = defaultInitValue
        /\ mailboxesWrite4 = defaultInitValue
        /\ mailboxesWrite5 = defaultInitValue
        /\ mailboxesWrite6 = defaultInitValue
        /\ mailboxesWrite7 = defaultInitValue
        /\ mailboxesRead0 = defaultInitValue
        /\ mailboxesWrite8 = defaultInitValue
        /\ mailboxesWrite9 = defaultInitValue
        /\ mailboxesWrite10 = defaultInitValue
        /\ mailboxesWrite11 = defaultInitValue
        /\ mailboxesWrite12 = defaultInitValue
        /\ mailboxesWrite13 = defaultInitValue
        /\ mailboxesRead1 = defaultInitValue
        /\ mailboxesWrite14 = defaultInitValue
        /\ decidedWrite = defaultInitValue
        /\ decidedWrite0 = defaultInitValue
        /\ decidedWrite1 = defaultInitValue
        /\ decidedWrite2 = defaultInitValue
        /\ decidedWrite3 = defaultInitValue
        (* Process proposer *)
        /\ b = [self \in Proposer |-> defaultInitValue]
        /\ s = [self \in Proposer |-> 1]
        /\ elected = [self \in Proposer |-> FALSE]
        /\ acceptedValues_ = [self \in Proposer |-> <<>>]
        /\ max = [self \in Proposer |-> [slot |-> -(1), bal |-> -(1), val |-> -(1)]]
        /\ index = [self \in Proposer |-> defaultInitValue]
        /\ entry_ = [self \in Proposer |-> defaultInitValue]
        /\ promises = [self \in Proposer |-> defaultInitValue]
        /\ accepts_ = [self \in Proposer |-> 0]
        /\ value = [self \in Proposer |-> defaultInitValue]
        /\ resp = [self \in Proposer |-> defaultInitValue]
        (* Process acceptor *)
        /\ maxBal = [self \in Acceptor |-> -(1)]
        /\ loopIndex = [self \in Acceptor |-> defaultInitValue]
        /\ acceptedValues = [self \in Acceptor |-> <<>>]
        /\ payload = [self \in Acceptor |-> defaultInitValue]
        /\ msg_ = [self \in Acceptor |-> defaultInitValue]
        (* Process learner *)
        /\ decidedLocal = [self \in Learner |-> [slot \in Slots |-> NULL]]
        /\ accepts = [self \in Learner |-> <<>>]
        /\ numAccepted = [self \in Learner |-> 0]
        /\ iterator = [self \in Learner |-> defaultInitValue]
        /\ entry = [self \in Learner |-> defaultInitValue]
        /\ msg = [self \in Learner |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposer -> "Pre"
                                        [] self \in Acceptor -> "A"
                                        [] self \in Learner -> "L"]

Pre(self) == /\ pc[self] = "Pre"
             /\ b' = [b EXCEPT ![self] = self]
             /\ pc' = [pc EXCEPT ![self] = "P"]
             /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                             mailboxesRead, mailboxesWrite1, mailboxesWrite2,
                             mailboxesWrite3, mailboxesWrite4, mailboxesWrite5,
                             mailboxesWrite6, mailboxesWrite7, mailboxesRead0,
                             mailboxesWrite8, mailboxesWrite9,
                             mailboxesWrite10, mailboxesWrite11,
                             mailboxesWrite12, mailboxesWrite13,
                             mailboxesRead1, mailboxesWrite14, decidedWrite,
                             decidedWrite0, decidedWrite1, decidedWrite2,
                             decidedWrite3, s, elected, acceptedValues_, max,
                             index, entry_, promises, accepts_, value, resp,
                             maxBal, loopIndex, acceptedValues, payload, msg_,
                             decidedLocal, accepts, numAccepted, iterator,
                             entry, msg >>

P(self) == /\ pc[self] = "P"
           /\ IF (s[self]) \in (Slots)
                 THEN /\ pc' = [pc EXCEPT ![self] = "PLeaderCheck"]
                      /\ UNCHANGED << network, mailboxesWrite7 >>
                 ELSE /\ mailboxesWrite7' = network
                      /\ network' = mailboxesWrite7'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead,
                           mailboxesWrite1, mailboxesWrite2, mailboxesWrite3,
                           mailboxesWrite4, mailboxesWrite5, mailboxesWrite6,
                           mailboxesRead0, mailboxesWrite8, mailboxesWrite9,
                           mailboxesWrite10, mailboxesWrite11,
                           mailboxesWrite12, mailboxesWrite13, mailboxesRead1,
                           mailboxesWrite14, decidedWrite, decidedWrite0,
                           decidedWrite1, decidedWrite2, decidedWrite3, b, s,
                           elected, acceptedValues_, max, index, entry_,
                           promises, accepts_, value, resp, maxBal, loopIndex,
                           acceptedValues, payload, msg_, decidedLocal,
                           accepts, numAccepted, iterator, entry, msg >>

PLeaderCheck(self) == /\ pc[self] = "PLeaderCheck"
                      /\ IF elected[self]
                            THEN /\ accepts_' = [accepts_ EXCEPT ![self] = 0]
                                 /\ value' = [value EXCEPT ![self] = self]
                                 /\ index' = [index EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "PFindMaxVal"]
                            ELSE /\ index' = [index EXCEPT ![self] = NUM_PROPOSERS]
                                 /\ pc' = [pc EXCEPT ![self] = "PReqVotes"]
                                 /\ UNCHANGED << accepts_, value >>
                      /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                                      mailboxesRead, mailboxesWrite1,
                                      mailboxesWrite2, mailboxesWrite3,
                                      mailboxesWrite4, mailboxesWrite5,
                                      mailboxesWrite6, mailboxesWrite7,
                                      mailboxesRead0, mailboxesWrite8,
                                      mailboxesWrite9, mailboxesWrite10,
                                      mailboxesWrite11, mailboxesWrite12,
                                      mailboxesWrite13, mailboxesRead1,
                                      mailboxesWrite14, decidedWrite,
                                      decidedWrite0, decidedWrite1,
                                      decidedWrite2, decidedWrite3, b, s,
                                      elected, acceptedValues_, max, entry_,
                                      promises, resp, maxBal, loopIndex,
                                      acceptedValues, payload, msg_,
                                      decidedLocal, accepts, numAccepted,
                                      iterator, entry, msg >>

PFindMaxVal(self) == /\ pc[self] = "PFindMaxVal"
                     /\ IF (index[self]) <= (Len(acceptedValues_[self]))
                           THEN /\ entry_' = [entry_ EXCEPT ![self] = acceptedValues_[self][index[self]]]
                                /\ IF (((entry_'[self]).slot) = (s[self])) /\ (((entry_'[self]).bal) >= ((max[self]).bal))
                                      THEN /\ value' = [value EXCEPT ![self] = (entry_'[self]).val]
                                           /\ max' = [max EXCEPT ![self] = entry_'[self]]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << max, value >>
                                /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                                /\ pc' = [pc EXCEPT ![self] = "PFindMaxVal"]
                           ELSE /\ index' = [index EXCEPT ![self] = NUM_PROPOSERS]
                                /\ pc' = [pc EXCEPT ![self] = "PSendProposes"]
                                /\ UNCHANGED << max, entry_, value >>
                     /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                                     mailboxesRead, mailboxesWrite1,
                                     mailboxesWrite2, mailboxesWrite3,
                                     mailboxesWrite4, mailboxesWrite5,
                                     mailboxesWrite6, mailboxesWrite7,
                                     mailboxesRead0, mailboxesWrite8,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesRead1,
                                     mailboxesWrite14, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, decidedWrite3, b, s,
                                     elected, acceptedValues_, promises,
                                     accepts_, resp, maxBal, loopIndex,
                                     acceptedValues, payload, msg_,
                                     decidedLocal, accepts, numAccepted,
                                     iterator, entry, msg >>

PSendProposes(self) == /\ pc[self] = "PSendProposes"
                       /\ IF (index[self]) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))
                             THEN /\ mailboxesWrite' = [network EXCEPT ![index[self]] = Append(network[index[self]], [type |-> PROPOSE_MSG, bal |-> b[self], sender |-> self, slot |-> s[self], val |-> value[self]])]
                                  /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                                  /\ mailboxesWrite0' = mailboxesWrite'
                                  /\ network' = mailboxesWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "PSendProposes"]
                             ELSE /\ mailboxesWrite0' = network
                                  /\ network' = mailboxesWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                  /\ UNCHANGED << mailboxesWrite, index >>
                       /\ UNCHANGED << mailboxesRead, mailboxesWrite1,
                                       mailboxesWrite2, mailboxesWrite3,
                                       mailboxesWrite4, mailboxesWrite5,
                                       mailboxesWrite6, mailboxesWrite7,
                                       mailboxesRead0, mailboxesWrite8,
                                       mailboxesWrite9, mailboxesWrite10,
                                       mailboxesWrite11, mailboxesWrite12,
                                       mailboxesWrite13, mailboxesRead1,
                                       mailboxesWrite14, decidedWrite,
                                       decidedWrite0, decidedWrite1,
                                       decidedWrite2, decidedWrite3, b, s,
                                       elected, acceptedValues_, max, entry_,
                                       promises, accepts_, value, resp, maxBal,
                                       loopIndex, acceptedValues, payload,
                                       msg_, decidedLocal, accepts,
                                       numAccepted, iterator, entry, msg >>

PSearchAccs(self) == /\ pc[self] = "PSearchAccs"
                     /\ IF (((accepts_[self]) * (2)) < (Cardinality(Acceptor))) /\ (elected[self])
                           THEN /\ (Len(network[self])) > (0)
                                /\ LET msg0 == Head(network[self]) IN
                                     /\ mailboxesWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                     /\ mailboxesRead' = msg0
                                /\ resp' = [resp EXCEPT ![self] = mailboxesRead']
                                /\ IF ((resp'[self]).type) = (ACCEPT_MSG)
                                      THEN /\ IF ((((resp'[self]).bal) = (b[self])) /\ (((resp'[self]).slot) = (s[self]))) /\ (((resp'[self]).val) = (value[self]))
                                                 THEN /\ accepts_' = [accepts_ EXCEPT ![self] = (accepts_[self]) + (1)]
                                                      /\ network' = mailboxesWrite'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                 ELSE /\ network' = mailboxesWrite'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                      /\ UNCHANGED accepts_
                                           /\ UNCHANGED elected
                                      ELSE /\ IF ((resp'[self]).type) = (REJECT_MSG)
                                                 THEN /\ elected' = [elected EXCEPT ![self] = FALSE]
                                                      /\ network' = mailboxesWrite'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                 ELSE /\ network' = mailboxesWrite'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                      /\ UNCHANGED elected
                                           /\ UNCHANGED accepts_
                           ELSE /\ network' = mailboxesWrite
                                /\ pc' = [pc EXCEPT ![self] = "PIncSlot"]
                                /\ UNCHANGED << mailboxesWrite, mailboxesRead,
                                                elected, accepts_, resp >>
                     /\ UNCHANGED << mailboxesWrite0, mailboxesWrite1,
                                     mailboxesWrite2, mailboxesWrite3,
                                     mailboxesWrite4, mailboxesWrite5,
                                     mailboxesWrite6, mailboxesWrite7,
                                     mailboxesRead0, mailboxesWrite8,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesRead1,
                                     mailboxesWrite14, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, decidedWrite3, b, s,
                                     acceptedValues_, max, index, entry_,
                                     promises, value, maxBal, loopIndex,
                                     acceptedValues, payload, msg_,
                                     decidedLocal, accepts, numAccepted,
                                     iterator, entry, msg >>

PIncSlot(self) == /\ pc[self] = "PIncSlot"
                  /\ IF elected[self]
                        THEN /\ s' = [s EXCEPT ![self] = (s[self]) + (1)]
                             /\ pc' = [pc EXCEPT ![self] = "P"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "P"]
                             /\ s' = s
                  /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                                  mailboxesRead, mailboxesWrite1,
                                  mailboxesWrite2, mailboxesWrite3,
                                  mailboxesWrite4, mailboxesWrite5,
                                  mailboxesWrite6, mailboxesWrite7,
                                  mailboxesRead0, mailboxesWrite8,
                                  mailboxesWrite9, mailboxesWrite10,
                                  mailboxesWrite11, mailboxesWrite12,
                                  mailboxesWrite13, mailboxesRead1,
                                  mailboxesWrite14, decidedWrite,
                                  decidedWrite0, decidedWrite1, decidedWrite2,
                                  decidedWrite3, b, elected, acceptedValues_,
                                  max, index, entry_, promises, accepts_,
                                  value, resp, maxBal, loopIndex,
                                  acceptedValues, payload, msg_, decidedLocal,
                                  accepts, numAccepted, iterator, entry, msg >>

PReqVotes(self) == /\ pc[self] = "PReqVotes"
                   /\ IF (index[self]) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))
                         THEN /\ mailboxesWrite' = [network EXCEPT ![index[self]] = Append(network[index[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> NULL, val |-> NULL])]
                              /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                              /\ mailboxesWrite1' = mailboxesWrite'
                              /\ network' = mailboxesWrite1'
                              /\ pc' = [pc EXCEPT ![self] = "PReqVotes"]
                              /\ UNCHANGED promises
                         ELSE /\ promises' = [promises EXCEPT ![self] = 0]
                              /\ mailboxesWrite1' = network
                              /\ network' = mailboxesWrite1'
                              /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                              /\ UNCHANGED << mailboxesWrite, index >>
                   /\ UNCHANGED << mailboxesWrite0, mailboxesRead,
                                   mailboxesWrite2, mailboxesWrite3,
                                   mailboxesWrite4, mailboxesWrite5,
                                   mailboxesWrite6, mailboxesWrite7,
                                   mailboxesRead0, mailboxesWrite8,
                                   mailboxesWrite9, mailboxesWrite10,
                                   mailboxesWrite11, mailboxesWrite12,
                                   mailboxesWrite13, mailboxesRead1,
                                   mailboxesWrite14, decidedWrite,
                                   decidedWrite0, decidedWrite1, decidedWrite2,
                                   decidedWrite3, b, s, elected,
                                   acceptedValues_, max, entry_, accepts_,
                                   value, resp, maxBal, loopIndex,
                                   acceptedValues, payload, msg_, decidedLocal,
                                   accepts, numAccepted, iterator, entry, msg >>

PCandidate(self) == /\ pc[self] = "PCandidate"
                    /\ IF ~(elected[self])
                          THEN /\ (Len(network[self])) > (0)
                               /\ LET msg1 == Head(network[self]) IN
                                    /\ mailboxesWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                    /\ mailboxesRead' = msg1
                               /\ resp' = [resp EXCEPT ![self] = mailboxesRead']
                               /\ IF ((resp'[self]).type) = (PROMISE_MSG)
                                     THEN /\ acceptedValues_' = [acceptedValues_ EXCEPT ![self] = (acceptedValues_[self]) \o ((resp'[self]).accepted)]
                                          /\ network' = mailboxesWrite'
                                          /\ pc' = [pc EXCEPT ![self] = "PGotPromise"]
                                          /\ UNCHANGED << mailboxesWrite4,
                                                          mailboxesWrite5 >>
                                     ELSE /\ mailboxesWrite4' = network
                                          /\ mailboxesWrite5' = mailboxesWrite4'
                                          /\ network' = mailboxesWrite5'
                                          /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                          /\ UNCHANGED acceptedValues_
                          ELSE /\ mailboxesWrite5' = network
                               /\ network' = mailboxesWrite5'
                               /\ pc' = [pc EXCEPT ![self] = "P"]
                               /\ UNCHANGED << mailboxesWrite, mailboxesRead,
                                               mailboxesWrite4,
                                               acceptedValues_, resp >>
                    /\ UNCHANGED << mailboxesWrite0, mailboxesWrite1,
                                    mailboxesWrite2, mailboxesWrite3,
                                    mailboxesWrite6, mailboxesWrite7,
                                    mailboxesRead0, mailboxesWrite8,
                                    mailboxesWrite9, mailboxesWrite10,
                                    mailboxesWrite11, mailboxesWrite12,
                                    mailboxesWrite13, mailboxesRead1,
                                    mailboxesWrite14, decidedWrite,
                                    decidedWrite0, decidedWrite1,
                                    decidedWrite2, decidedWrite3, b, s,
                                    elected, max, index, entry_, promises,
                                    accepts_, value, maxBal, loopIndex,
                                    acceptedValues, payload, msg_,
                                    decidedLocal, accepts, numAccepted,
                                    iterator, entry, msg >>

PGotPromise(self) == /\ pc[self] = "PGotPromise"
                     /\ IF ((resp[self]).bal) > (b[self])
                           THEN /\ b' = [b EXCEPT ![self] = (b[self]) + (NUM_PROPOSERS)]
                                /\ index' = [index EXCEPT ![self] = NUM_PROPOSERS]
                                /\ pc' = [pc EXCEPT ![self] = "PReSendReqVotes"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "PCheckElected"]
                                /\ UNCHANGED << b, index >>
                     /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                                     mailboxesRead, mailboxesWrite1,
                                     mailboxesWrite2, mailboxesWrite3,
                                     mailboxesWrite4, mailboxesWrite5,
                                     mailboxesWrite6, mailboxesWrite7,
                                     mailboxesRead0, mailboxesWrite8,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesRead1,
                                     mailboxesWrite14, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, decidedWrite3, s, elected,
                                     acceptedValues_, max, entry_, promises,
                                     accepts_, value, resp, maxBal, loopIndex,
                                     acceptedValues, payload, msg_,
                                     decidedLocal, accepts, numAccepted,
                                     iterator, entry, msg >>

PReSendReqVotes(self) == /\ pc[self] = "PReSendReqVotes"
                         /\ IF (index[self]) <= ((NUM_PROPOSERS) + ((NUM_ACCEPTORS) - (1)))
                               THEN /\ mailboxesWrite' = [network EXCEPT ![index[self]] = Append(network[index[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> NULL, val |-> NULL])]
                                    /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                                    /\ mailboxesWrite2' = mailboxesWrite'
                                    /\ network' = mailboxesWrite2'
                                    /\ pc' = [pc EXCEPT ![self] = "PReSendReqVotes"]
                               ELSE /\ mailboxesWrite2' = network
                                    /\ network' = mailboxesWrite2'
                                    /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                    /\ UNCHANGED << mailboxesWrite, index >>
                         /\ UNCHANGED << mailboxesWrite0, mailboxesRead,
                                         mailboxesWrite1, mailboxesWrite3,
                                         mailboxesWrite4, mailboxesWrite5,
                                         mailboxesWrite6, mailboxesWrite7,
                                         mailboxesRead0, mailboxesWrite8,
                                         mailboxesWrite9, mailboxesWrite10,
                                         mailboxesWrite11, mailboxesWrite12,
                                         mailboxesWrite13, mailboxesRead1,
                                         mailboxesWrite14, decidedWrite,
                                         decidedWrite0, decidedWrite1,
                                         decidedWrite2, decidedWrite3, b, s,
                                         elected, acceptedValues_, max, entry_,
                                         promises, accepts_, value, resp,
                                         maxBal, loopIndex, acceptedValues,
                                         payload, msg_, decidedLocal, accepts,
                                         numAccepted, iterator, entry, msg >>

PCheckElected(self) == /\ pc[self] = "PCheckElected"
                       /\ IF ((resp[self]).bal) = (b[self])
                             THEN /\ promises' = [promises EXCEPT ![self] = (promises[self]) + (1)]
                                  /\ pc' = [pc EXCEPT ![self] = "PBecomeLeader"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                  /\ UNCHANGED promises
                       /\ UNCHANGED << network, mailboxesWrite,
                                       mailboxesWrite0, mailboxesRead,
                                       mailboxesWrite1, mailboxesWrite2,
                                       mailboxesWrite3, mailboxesWrite4,
                                       mailboxesWrite5, mailboxesWrite6,
                                       mailboxesWrite7, mailboxesRead0,
                                       mailboxesWrite8, mailboxesWrite9,
                                       mailboxesWrite10, mailboxesWrite11,
                                       mailboxesWrite12, mailboxesWrite13,
                                       mailboxesRead1, mailboxesWrite14,
                                       decidedWrite, decidedWrite0,
                                       decidedWrite1, decidedWrite2,
                                       decidedWrite3, b, s, elected,
                                       acceptedValues_, max, index, entry_,
                                       accepts_, value, resp, maxBal,
                                       loopIndex, acceptedValues, payload,
                                       msg_, decidedLocal, accepts,
                                       numAccepted, iterator, entry, msg >>

PBecomeLeader(self) == /\ pc[self] = "PBecomeLeader"
                       /\ IF ((promises[self]) * (2)) > (Cardinality(Acceptor))
                             THEN /\ elected' = [elected EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                  /\ UNCHANGED elected
                       /\ UNCHANGED << network, mailboxesWrite,
                                       mailboxesWrite0, mailboxesRead,
                                       mailboxesWrite1, mailboxesWrite2,
                                       mailboxesWrite3, mailboxesWrite4,
                                       mailboxesWrite5, mailboxesWrite6,
                                       mailboxesWrite7, mailboxesRead0,
                                       mailboxesWrite8, mailboxesWrite9,
                                       mailboxesWrite10, mailboxesWrite11,
                                       mailboxesWrite12, mailboxesWrite13,
                                       mailboxesRead1, mailboxesWrite14,
                                       decidedWrite, decidedWrite0,
                                       decidedWrite1, decidedWrite2,
                                       decidedWrite3, b, s, acceptedValues_,
                                       max, index, entry_, promises, accepts_,
                                       value, resp, maxBal, loopIndex,
                                       acceptedValues, payload, msg_,
                                       decidedLocal, accepts, numAccepted,
                                       iterator, entry, msg >>

proposer(self) == Pre(self) \/ P(self) \/ PLeaderCheck(self)
                     \/ PFindMaxVal(self) \/ PSendProposes(self)
                     \/ PSearchAccs(self) \/ PIncSlot(self)
                     \/ PReqVotes(self) \/ PCandidate(self)
                     \/ PGotPromise(self) \/ PReSendReqVotes(self)
                     \/ PCheckElected(self) \/ PBecomeLeader(self)

A(self) == /\ pc[self] = "A"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg2 == Head(network[self]) IN
                           /\ mailboxesWrite8' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead0' = msg2
                      /\ msg_' = [msg_ EXCEPT ![self] = mailboxesRead0']
                      /\ network' = mailboxesWrite8'
                      /\ pc' = [pc EXCEPT ![self] = "AMsgSwitch"]
                      /\ UNCHANGED mailboxesWrite13
                 ELSE /\ mailboxesWrite13' = network
                      /\ network' = mailboxesWrite13'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << mailboxesRead0, mailboxesWrite8, msg_ >>
           /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead,
                           mailboxesWrite1, mailboxesWrite2, mailboxesWrite3,
                           mailboxesWrite4, mailboxesWrite5, mailboxesWrite6,
                           mailboxesWrite7, mailboxesWrite9, mailboxesWrite10,
                           mailboxesWrite11, mailboxesWrite12, mailboxesRead1,
                           mailboxesWrite14, decidedWrite, decidedWrite0,
                           decidedWrite1, decidedWrite2, decidedWrite3, b, s,
                           elected, acceptedValues_, max, index, entry_,
                           promises, accepts_, value, resp, maxBal, loopIndex,
                           acceptedValues, payload, decidedLocal, accepts,
                           numAccepted, iterator, entry, msg >>

AMsgSwitch(self) == /\ pc[self] = "AMsgSwitch"
                    /\ IF (((msg_[self]).type) = (PREPARE_MSG)) /\ (((msg_[self]).bal) > (maxBal[self]))
                          THEN /\ pc' = [pc EXCEPT ![self] = "APrepare"]
                               /\ UNCHANGED << network, mailboxesWrite10,
                                               mailboxesWrite11,
                                               mailboxesWrite12 >>
                          ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) >= (maxBal[self]))
                                     THEN /\ pc' = [pc EXCEPT ![self] = "APropose"]
                                          /\ UNCHANGED << network,
                                                          mailboxesWrite10,
                                                          mailboxesWrite11,
                                                          mailboxesWrite12 >>
                                     ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) < (maxBal[self]))
                                                THEN /\ pc' = [pc EXCEPT ![self] = "ABadPropose"]
                                                     /\ UNCHANGED << network,
                                                                     mailboxesWrite10,
                                                                     mailboxesWrite11,
                                                                     mailboxesWrite12 >>
                                                ELSE /\ mailboxesWrite10' = network
                                                     /\ mailboxesWrite11' = mailboxesWrite10'
                                                     /\ mailboxesWrite12' = mailboxesWrite11'
                                                     /\ network' = mailboxesWrite12'
                                                     /\ pc' = [pc EXCEPT ![self] = "A"]
                    /\ UNCHANGED << mailboxesWrite, mailboxesWrite0,
                                    mailboxesRead, mailboxesWrite1,
                                    mailboxesWrite2, mailboxesWrite3,
                                    mailboxesWrite4, mailboxesWrite5,
                                    mailboxesWrite6, mailboxesWrite7,
                                    mailboxesRead0, mailboxesWrite8,
                                    mailboxesWrite9, mailboxesWrite13,
                                    mailboxesRead1, mailboxesWrite14,
                                    decidedWrite, decidedWrite0, decidedWrite1,
                                    decidedWrite2, decidedWrite3, b, s,
                                    elected, acceptedValues_, max, index,
                                    entry_, promises, accepts_, value, resp,
                                    maxBal, loopIndex, acceptedValues, payload,
                                    msg_, decidedLocal, accepts, numAccepted,
                                    iterator, entry, msg >>

APrepare(self) == /\ pc[self] = "APrepare"
                  /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
                  /\ mailboxesWrite8' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> NULL, val |-> NULL, accepted |-> acceptedValues[self]])]
                  /\ network' = mailboxesWrite8'
                  /\ pc' = [pc EXCEPT ![self] = "A"]
                  /\ UNCHANGED << mailboxesWrite, mailboxesWrite0,
                                  mailboxesRead, mailboxesWrite1,
                                  mailboxesWrite2, mailboxesWrite3,
                                  mailboxesWrite4, mailboxesWrite5,
                                  mailboxesWrite6, mailboxesWrite7,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesRead1, mailboxesWrite14,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, decidedWrite3, b, s, elected,
                                  acceptedValues_, max, index, entry_,
                                  promises, accepts_, value, resp, loopIndex,
                                  acceptedValues, payload, msg_, decidedLocal,
                                  accepts, numAccepted, iterator, entry, msg >>

APropose(self) == /\ pc[self] = "APropose"
                  /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
                  /\ payload' = [payload EXCEPT ![self] = [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, accepted |-> <<>>]]
                  /\ acceptedValues' = [acceptedValues EXCEPT ![self] = Append(acceptedValues[self], [slot |-> (msg_[self]).slot, bal |-> (msg_[self]).bal, val |-> (msg_[self]).val])]
                  /\ mailboxesWrite8' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], payload'[self])]
                  /\ loopIndex' = [loopIndex EXCEPT ![self] = (NUM_PROPOSERS) + (NUM_ACCEPTORS)]
                  /\ network' = mailboxesWrite8'
                  /\ pc' = [pc EXCEPT ![self] = "ANotifyLearners"]
                  /\ UNCHANGED << mailboxesWrite, mailboxesWrite0,
                                  mailboxesRead, mailboxesWrite1,
                                  mailboxesWrite2, mailboxesWrite3,
                                  mailboxesWrite4, mailboxesWrite5,
                                  mailboxesWrite6, mailboxesWrite7,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesRead1, mailboxesWrite14,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, decidedWrite3, b, s, elected,
                                  acceptedValues_, max, index, entry_,
                                  promises, accepts_, value, resp, msg_,
                                  decidedLocal, accepts, numAccepted, iterator,
                                  entry, msg >>

ANotifyLearners(self) == /\ pc[self] = "ANotifyLearners"
                         /\ IF (loopIndex[self]) <= (((NUM_PROPOSERS) + (NUM_ACCEPTORS)) + ((NUM_LEARNERS) - (1)))
                               THEN /\ mailboxesWrite8' = [network EXCEPT ![loopIndex[self]] = Append(network[loopIndex[self]], payload[self])]
                                    /\ loopIndex' = [loopIndex EXCEPT ![self] = (loopIndex[self]) + (1)]
                                    /\ mailboxesWrite9' = mailboxesWrite8'
                                    /\ network' = mailboxesWrite9'
                                    /\ pc' = [pc EXCEPT ![self] = "ANotifyLearners"]
                               ELSE /\ mailboxesWrite9' = network
                                    /\ network' = mailboxesWrite9'
                                    /\ pc' = [pc EXCEPT ![self] = "A"]
                                    /\ UNCHANGED << mailboxesWrite8, loopIndex >>
                         /\ UNCHANGED << mailboxesWrite, mailboxesWrite0,
                                         mailboxesRead, mailboxesWrite1,
                                         mailboxesWrite2, mailboxesWrite3,
                                         mailboxesWrite4, mailboxesWrite5,
                                         mailboxesWrite6, mailboxesWrite7,
                                         mailboxesRead0, mailboxesWrite10,
                                         mailboxesWrite11, mailboxesWrite12,
                                         mailboxesWrite13, mailboxesRead1,
                                         mailboxesWrite14, decidedWrite,
                                         decidedWrite0, decidedWrite1,
                                         decidedWrite2, decidedWrite3, b, s,
                                         elected, acceptedValues_, max, index,
                                         entry_, promises, accepts_, value,
                                         resp, maxBal, acceptedValues, payload,
                                         msg_, decidedLocal, accepts,
                                         numAccepted, iterator, entry, msg >>

ABadPropose(self) == /\ pc[self] = "ABadPropose"
                     /\ mailboxesWrite8' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, accepted |-> <<>>])]
                     /\ network' = mailboxesWrite8'
                     /\ pc' = [pc EXCEPT ![self] = "A"]
                     /\ UNCHANGED << mailboxesWrite, mailboxesWrite0,
                                     mailboxesRead, mailboxesWrite1,
                                     mailboxesWrite2, mailboxesWrite3,
                                     mailboxesWrite4, mailboxesWrite5,
                                     mailboxesWrite6, mailboxesWrite7,
                                     mailboxesRead0, mailboxesWrite9,
                                     mailboxesWrite10, mailboxesWrite11,
                                     mailboxesWrite12, mailboxesWrite13,
                                     mailboxesRead1, mailboxesWrite14,
                                     decidedWrite, decidedWrite0,
                                     decidedWrite1, decidedWrite2,
                                     decidedWrite3, b, s, elected,
                                     acceptedValues_, max, index, entry_,
                                     promises, accepts_, value, resp, maxBal,
                                     loopIndex, acceptedValues, payload, msg_,
                                     decidedLocal, accepts, numAccepted,
                                     iterator, entry, msg >>

acceptor(self) == A(self) \/ AMsgSwitch(self) \/ APrepare(self)
                     \/ APropose(self) \/ ANotifyLearners(self)
                     \/ ABadPropose(self)

L(self) == /\ pc[self] = "L"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg3 == Head(network[self]) IN
                           /\ mailboxesWrite14' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead1' = msg3
                      /\ msg' = [msg EXCEPT ![self] = mailboxesRead1']
                      /\ network' = mailboxesWrite14'
                      /\ pc' = [pc EXCEPT ![self] = "LGotAcc"]
                      /\ UNCHANGED << decidedWrite3, decidedLocal >>
                 ELSE /\ decidedWrite3' = decidedLocal[self]
                      /\ decidedLocal' = [decidedLocal EXCEPT ![self] = decidedWrite3']
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << network, mailboxesRead1,
                                      mailboxesWrite14, msg >>
           /\ UNCHANGED << mailboxesWrite, mailboxesWrite0, mailboxesRead,
                           mailboxesWrite1, mailboxesWrite2, mailboxesWrite3,
                           mailboxesWrite4, mailboxesWrite5, mailboxesWrite6,
                           mailboxesWrite7, mailboxesRead0, mailboxesWrite8,
                           mailboxesWrite9, mailboxesWrite10, mailboxesWrite11,
                           mailboxesWrite12, mailboxesWrite13, decidedWrite,
                           decidedWrite0, decidedWrite1, decidedWrite2, b, s,
                           elected, acceptedValues_, max, index, entry_,
                           promises, accepts_, value, resp, maxBal, loopIndex,
                           acceptedValues, payload, msg_, accepts, numAccepted,
                           iterator, entry >>

LGotAcc(self) == /\ pc[self] = "LGotAcc"
                 /\ IF ((msg[self]).type) = (ACCEPT_MSG)
                       THEN /\ accepts' = [accepts EXCEPT ![self] = Append(accepts[self], msg[self])]
                            /\ iterator' = [iterator EXCEPT ![self] = 1]
                            /\ numAccepted' = [numAccepted EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "LCheckMajority"]
                            /\ UNCHANGED << decidedWrite2, decidedLocal >>
                       ELSE /\ decidedWrite2' = decidedLocal[self]
                            /\ decidedLocal' = [decidedLocal EXCEPT ![self] = decidedWrite2']
                            /\ pc' = [pc EXCEPT ![self] = "L"]
                            /\ UNCHANGED << accepts, numAccepted, iterator >>
                 /\ UNCHANGED << network, mailboxesWrite, mailboxesWrite0,
                                 mailboxesRead, mailboxesWrite1,
                                 mailboxesWrite2, mailboxesWrite3,
                                 mailboxesWrite4, mailboxesWrite5,
                                 mailboxesWrite6, mailboxesWrite7,
                                 mailboxesRead0, mailboxesWrite8,
                                 mailboxesWrite9, mailboxesWrite10,
                                 mailboxesWrite11, mailboxesWrite12,
                                 mailboxesWrite13, mailboxesRead1,
                                 mailboxesWrite14, decidedWrite, decidedWrite0,
                                 decidedWrite1, decidedWrite3, b, s, elected,
                                 acceptedValues_, max, index, entry_, promises,
                                 accepts_, value, resp, maxBal, loopIndex,
                                 acceptedValues, payload, msg_, entry, msg >>

LCheckMajority(self) == /\ pc[self] = "LCheckMajority"
                        /\ IF (iterator[self]) <= (Len(accepts[self]))
                              THEN /\ entry' = [entry EXCEPT ![self] = accepts[self][iterator[self]]]
                                   /\ IF ((((entry'[self]).slot) = ((msg[self]).slot)) /\ (((entry'[self]).bal) = ((msg[self]).bal))) /\ (((entry'[self]).val) = ((msg[self]).val))
                                         THEN /\ numAccepted' = [numAccepted EXCEPT ![self] = (numAccepted[self]) + (1)]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED numAccepted
                                   /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                   /\ decidedWrite1' = decidedLocal[self]
                                   /\ decidedLocal' = [decidedLocal EXCEPT ![self] = decidedWrite1']
                                   /\ pc' = [pc EXCEPT ![self] = "LCheckMajority"]
                                   /\ UNCHANGED << decidedWrite, decidedWrite0,
                                                   accepts >>
                              ELSE /\ IF ((numAccepted[self]) * (2)) > (Cardinality(Acceptor))
                                         THEN /\ Assert(((decidedLocal[self][(msg[self]).slot]) = (NULL)) \/ ((decidedLocal[self][(msg[self]).slot]) = ((msg[self]).val)),
                                                        "Failure of assertion at line 517, column 37.")
                                              /\ decidedWrite' = [decidedLocal[self] EXCEPT ![(msg[self]).slot] = (msg[self]).val]
                                              /\ accepts' = [accepts EXCEPT ![self] = <<>>]
                                              /\ decidedWrite0' = decidedWrite'
                                              /\ decidedWrite1' = decidedWrite0'
                                              /\ decidedLocal' = [decidedLocal EXCEPT ![self] = decidedWrite1']
                                              /\ pc' = [pc EXCEPT ![self] = "L"]
                                         ELSE /\ decidedWrite0' = decidedLocal[self]
                                              /\ decidedWrite1' = decidedWrite0'
                                              /\ decidedLocal' = [decidedLocal EXCEPT ![self] = decidedWrite1']
                                              /\ pc' = [pc EXCEPT ![self] = "L"]
                                              /\ UNCHANGED << decidedWrite,
                                                              accepts >>
                                   /\ UNCHANGED << numAccepted, iterator,
                                                   entry >>
                        /\ UNCHANGED << network, mailboxesWrite,
                                        mailboxesWrite0, mailboxesRead,
                                        mailboxesWrite1, mailboxesWrite2,
                                        mailboxesWrite3, mailboxesWrite4,
                                        mailboxesWrite5, mailboxesWrite6,
                                        mailboxesWrite7, mailboxesRead0,
                                        mailboxesWrite8, mailboxesWrite9,
                                        mailboxesWrite10, mailboxesWrite11,
                                        mailboxesWrite12, mailboxesWrite13,
                                        mailboxesRead1, mailboxesWrite14,
                                        decidedWrite2, decidedWrite3, b, s,
                                        elected, acceptedValues_, max, index,
                                        entry_, promises, accepts_, value,
                                        resp, maxBal, loopIndex,
                                        acceptedValues, payload, msg_, msg >>

learner(self) == L(self) \/ LGotAcc(self) \/ LCheckMajority(self)

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

\*  No acceptor could have finalized/decided 2 different vals for same slot
\*  check the two below as invariant
Agreement == \A l1, l2 \in Learner, slot \in Slots :
                     decidedLocal[l1][slot] # NULL
                  /\ decidedLocal[l2][slot] # NULL => decidedLocal[l1][slot] = decidedLocal[l2][slot]

\* SlotSafety == \A l \in Learner, slot \in Slots : decidedLocal[l][slot]) \in {0, 1}

EventuallyLearned == \E l \in Learner : \E slot \in Slots : <>(decidedLocal[l][slot] # NULL)

=========================================================
