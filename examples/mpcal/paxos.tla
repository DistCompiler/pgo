----------------------------------- MODULE paxos ---------------------------------------
(***************************************************************************************)
(*                               Paxos Algorithm                                       *)
(***************************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NUM_NODES
ASSUME NUM_NODES \in Nat

CONSTANT BUFFER_SIZE
ASSUME BUFFER_SIZE \in Nat

CONSTANT NULL
ASSUME NULL \notin Nat

CONSTANTS GetSet, PutSet
ASSUME IsFiniteSet(GetSet) /\ IsFiniteSet(PutSet)

\* maximum amount of leader failures tested in a behavior
CONSTANT MAX_FAILURES
ASSUME MAX_FAILURES \in Nat

(***************************************************************************
--mpcal Paxos {
  define {
      Proposer       == 0..NUM_NODES-1
      Acceptor       == NUM_NODES..(2*NUM_NODES-1)
      Learner        == (2*NUM_NODES)..(3*NUM_NODES-1)
      Heartbeat      == (3*NUM_NODES)..(4*NUM_NODES-1)
      LeaderMonitor  == (4*NUM_NODES)..(5*NUM_NODES-1)
      KVRequests     == (5*NUM_NODES)..(6*NUM_NODES-1)
      KVPaxosManager == (6*NUM_NODES)..(7*NUM_NODES-1)
      AllNodes       == 0..(4*NUM_NODES-1)

      PREPARE_MSG        == 0
      PROMISE_MSG        == 1
      PROPOSE_MSG        == 2
      ACCEPT_MSG         == 3
      REJECT_MSG         == 4
      HEARTBEAT_MSG      == 5
      GET_MSG            == 6
      PUT_MSG            == 7
      GET_RESPONSE_MSG   == 8
      PUT_NOT_LEADER_MSG == 9
      PUT_OK_MSG         == 10

  }

  \* Broadcasts to nodes in range i..stop.
  macro Broadcast(mailboxes, msg, i, stop) {
      while (i <= stop) {
          mailboxes[i] := msg;
          i := i + 1;
      };
  }

  macro BroadcastLearners(mailboxes, msg, i) {
      Broadcast(mailboxes, msg, i, 3*NUM_NODES-1);
  }

  macro BroadcastAcceptors(mailboxes, msg, i) {
      Broadcast(mailboxes, msg, i, 2*NUM_NODES-1);
  }

  macro BroadcastHeartbeats(mailboxes,  msg, i, me) {
      while (i <= 4*NUM_NODES-1) {
          if (i # me) {
              mailboxes[i] := msg;
              i := i + 1;
          };
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

  mapping macro Self {
      read  { yield self; }
      write { assert(FALSE); yield $value; }
  }

  mapping macro SelfManager {
      read  { yield self - NUM_NODES; }
      write { assert(FALSE); yield $value; }
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

  mapping macro NextRequest {
     read {
         await Cardinality($variable) > 0;
         with (req \in $variable) {
             $variable := $variable \ {req};
             yield req;
         }
     }

     write { assert(FALSE); yield $value; }
  }

  mapping macro LeaderFailures {
      read {
          \* if we have failed less than MAX_FAILURES so far, non-deterministically
          \* choose whether to fail now
          if ($variable < MAX_FAILURES) {
              either {
                  $variable := $variable + 1;
                  yield TRUE;
              } or {
                  yield FALSE;
              }
          } else {
              yield FALSE;
          }
      }

      write { assert(FALSE); yield $value; }
  }

  mapping macro Identity {
      read  { yield $variable; }
      write { yield $value; }
  }

  mapping macro BlockingUntilTrue {
      read  { await $variable = TRUE; yield $variable; }
      write { yield $value; }
  }

  archetype ALearner(ref mailboxes, ref decided)
  variables accepts = <<>>,
            newAccepts,
            numAccepted,
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
                decided[self] := msg.val;

                \* garbage collection: accepted values related to the slot just
                \* decided can be discarded
                newAccepts := <<>>;
                iterator := 1;

                garbageCollection:
                  while (iterator <= Len(accepts)) {
                      entry := accepts[iterator];

                      if (entry.slot # msg.slot) {
                          newAccepts := Append(newAccepts, entry);
                      };

                      iterator := iterator + 1;
                  };

                  accepts := newAccepts;
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

        } elseif (msg.type = PREPARE_MSG /\ msg.bal <= maxBal) { \* Reject invalid prepares so candidates don't hang waiting for messages
ABadPrepare: mailboxes[msg.sender] := [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> NULL, val |-> NULL, accepted |-> <<>>];
        } elseif (msg.type = PROPOSE_MSG /\ msg.bal >= maxBal) { \* Accept valid proposals. Invariants are maintained by the proposer so no need to check the value
            \* Update max ballot
APropose:   maxBal := msg.bal;
            payload := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, accepted |-> <<>>];

            \* Add the value to the list of accepted values
            acceptedValues := Append(acceptedValues, [slot |-> msg.slot, bal |-> msg.bal, val |-> msg.val]);
            \* Respond that the proposal was accepted
            mailboxes[msg.sender] := payload;

            loopIndex := 2*NUM_NODES;
            \* Inform the learners of the accept
ANotifyLearners: BroadcastLearners(mailboxes, payload, loopIndex);

        } elseif (msg.type = PROPOSE_MSG /\ msg.bal < maxBal) { \* Reject invalid proposals to maintain promises
ABadPropose: mailboxes[msg.sender] := [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> msg.slot, val |-> msg.val, accepted |-> <<>>];
        }
    }
  }

  \* Key idea: Proposer must have received promises from majority, so it knows about every chosen value before it attempts to propose a value for a given slot
  archetype AProposer(ref mailboxes, valueStream, ref leaderFailure, ref electionInProgress, ref iAmTheLeader)
  variables b, \* local ballot
            s = 1, \* current slot
            elected = FALSE,
            acceptedValues = <<>>,
            max = [slot |-> -1, bal |-> -1, val |-> -1],
            index, \* temporary variable for iteration
            entry,
            promises,
            heartbeatMonitorId,
            accepts = 0,
            value,
            repropose,
            resp;
  {
Pre:b := self;
    heartbeatMonitorId := self + 3*NUM_NODES;
P:  while (TRUE) {
PLeaderCheck: if (elected) { \* This proposer thinks it is the distinguished proposer
            \***********
            \* PHASE 2
            \***********
            accepts := 0;

            \* whether proposing a previously accepted value is necessary
            repropose := FALSE;

            index := 1;
            \* Make sure the value proposed is the same as the value of the accepted proposal with the highest ballot (if such a value exists)
PFindMaxVal: while (index <= Len(acceptedValues)) {
                entry := acceptedValues[index];
                if (entry.slot = s /\ entry.bal >= max.bal) {
                    repropose := TRUE;
                    value := entry.val;
                    max := entry;
                };
                index := index + 1;
            };

            \* if we do not need to propose a previously accepted value, read
            \* next proposal from client stream
            if (~repropose) {
                value := valueStream[self];
            };

            index := NUM_NODES;
            \* Send Propose message to every acceptor
PSendProposes: BroadcastAcceptors(mailboxes, [type |-> PROPOSE_MSG, bal |-> b, sender |-> self, slot |-> s, val |-> value], index);

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
                    iAmTheLeader[heartbeatMonitorId] := FALSE;
                    electionInProgress[heartbeatMonitorId] := FALSE;
                    assert(leaderFailure[heartbeatMonitorId] = TRUE);
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
            index := NUM_NODES;
            \* Send prepares to every acceptor
PReqVotes:  BroadcastAcceptors(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL], index);
            promises := 0;
            iAmTheLeader[heartbeatMonitorId] := FALSE;
            electionInProgress[heartbeatMonitorId] := TRUE;

            \* Wait for response from majority of acceptors
PCandidate: while (~elected) {
                \* Wait for promise
                resp := mailboxes[self];
                if (resp.type = PROMISE_MSG /\ resp.bal = b) {
                    acceptedValues := acceptedValues \o resp.accepted;
                    \* Is it still from a current term?
                    promises := promises + 1;
                    \* Check if a majority of acceptors think that this proposer is the distinguished proposer, if so, become the leader
                    if (promises*2 > Cardinality(Acceptor)) {
                        elected := TRUE;
                        iAmTheLeader[heartbeatMonitorId] := TRUE;
                        electionInProgress[heartbeatMonitorId] := FALSE;
                    };
                } elseif (resp.type = REJECT_MSG \/ resp.bal > b) {
                    \* Pre-empted, try again for election
                    electionInProgress[heartbeatMonitorId] := FALSE;
                    assert(leaderFailure[heartbeatMonitorId] = TRUE);
                    b := b + NUM_NODES; \* to remain unique
                    index := NUM_NODES;
PReSendReqVotes:    BroadcastAcceptors(mailboxes, [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL], index);
                }
            };
        };
   }
  }

  archetype HeartbeatAction(ref mailboxes, ref lastSeen, ref sleeper, electionInProgress, iAmTheLeader, heartbeatFrequency)
  variables msg, index;
  {
      mainLoop:
        while (TRUE) {
          leaderLoop:
             while (~electionInProgress[self] /\ iAmTheLeader[self]) {
                 index := 3*NUM_NODES;

                 heartbeatBroadcast:
                   BroadcastHeartbeats(mailboxes, [type |-> HEARTBEAT_MSG, leader |-> self - 3*NUM_NODES], index, self);

                 sleeper := heartbeatFrequency;
             };

          followerLoop:
            while (~electionInProgress[self] /\ ~iAmTheLeader[self]) {
                msg := mailboxes[self];
                assert(msg.type = HEARTBEAT_MSG);
                lastSeen := msg;
            };
     }
  }

  archetype LeaderStatusMonitor(timeoutChecker, lastSeen, ref leaderFailure, ref electionInProgress, ref iAmTheLeader, ref sleeper, monitorFrequency)
  variables heartbeatId;
  {
    findId:
      heartbeatId := self - NUM_NODES;

    monitorLoop:
      while (TRUE) {
          \* if an election is not in progress and I am a follower, check
          \* if the leader has timed out.
          if (~electionInProgress[heartbeatId] /\ ~iAmTheLeader[heartbeatId]) {
              if (timeoutChecker[lastSeen]) {
                  leaderFailure[heartbeatId] := TRUE;
                  electionInProgress[heartbeatId] := TRUE;
              }
          };

          sleeper := monitorFrequency;
      }
  }


  archetype KeyValueRequests(requests, ref upstream, iAmTheLeader, ref proposerChan, paxosChan, db, myId)
  variables msg, null, heartbeatId, proposerId, counter = 0, requestId, putOk, confirmedRequestId;
  {
      kvInit:
        heartbeatId := self - 2*NUM_NODES;
        proposerId := self - 5*NUM_NODES;

      kvLoop:
        while (TRUE) {
            msg := requests;
            assert(msg.type = GET_MSG \/ msg.type = PUT_MSG);

            checkGet:
              if (msg.type = GET_MSG) {
                  upstream := [type |-> GET_RESPONSE_MSG, result |-> db[<< myId, msg.key >>]];
              };

            checkPut:
              if (msg.type = PUT_MSG) {
                  if (iAmTheLeader[heartbeatId]) {
                      \* unique request identifier
                      requestId := << self, counter >>;

                      \* request that this operation be proposed by the underlying proposer
                      proposerChan[proposerId] := [id |-> requestId, key |-> msg.key, value |-> msg.value];

                      putConfirm:
                        putOk := paxosChan[self];

                        \* ensure that confirmation is for value requested above
                        confirmedRequestId := putOk.id;
                        assert(confirmedRequestId[1] = self /\ confirmedRequestId[2] = counter);

                        \* send result upstream
                        upstream := [type |-> PUT_OK_MSG, result |-> null];

                        counter := counter + 1;

                  } else {
                      upstream := [type |-> PUT_NOT_LEADER_MSG, result |-> null];
                  }
              };
        }
  }

  archetype KeyValuePaxosManager(ref requestService, learnerChan, ref db, kvId)
  variables learnerId, operation, requestId;
  {
      findId:
        learnerId := self - 4*NUM_NODES;

      kvManagerLoop:
        while (TRUE) {
            \* wait for a value to be informed by the learner
            operation := learnerChan[learnerId];
            requestId := operation.id;

            \* update our database
            db[<< kvId, operation.key >>] := operation.value;

            \* if the request was issued by the running instance, send the operation back
            \* to the request service.
            if (requestId[1] = kvId) {
                requestService[kvId] := operation;
            };
        }
  }

  variables
        network = [id \in AllNodes |-> <<>>],

        \* values to be proposed by the distinguished proposer
        values = [p \in Proposer |-> [value |-> NULL]],

        \* keeps track when a leader was last seen (last received heartbeat). Abstraction
        lastSeenAbstract,

        \* this allow the mapping macro to fail as many as MAX_FAILURES times in a behavior
        monitorLastSeen = 0,
        timeoutCheckerAbstract = [monitorLastseen |-> 0],

        \* sleeps for a given amount of time. Abstraction
        sleeperAbstract,

        \* where operation results will be sent to
        kvClient,

        idAbstract,

        \* requests to be sent by the client
        requestSet = { [type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet } \union { [type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet},

        learnedChan = [l \in Learner |-> [value |-> NULL]],
        paxosLayerChan = [p \in KVRequests |-> [value |-> NULL]],

        database = [p \in KVRequests, k \in PutSet |-> NULL],

        electionInProgresssAbstract = [h \in Heartbeat |-> TRUE],
        iAmTheLeaderAbstract = [h \in Heartbeat |-> FALSE],
        leaderFailureAbstract = [h \in Heartbeat |-> FALSE];

    fair process (proposer \in Proposer) == instance AProposer(ref network, values, ref leaderFailureAbstract, ref electionInProgresssAbstract, ref iAmTheLeaderAbstract)
        mapping network[_] via FIFOChannel
        mapping values[_] via UnbufferedChannel
        mapping leaderFailureAbstract[_] via BlockingUntilTrue
        mapping electionInProgresssAbstract[_] via Identity
        mapping iAmTheLeaderAbstract[_] via Identity;

    fair process (acceptor \in Acceptor) == instance AAcceptor(ref network)
        mapping network[_] via FIFOChannel;

    fair process (learner \in Learner) == instance ALearner(ref network, learnedChan)
        mapping network[_] via FIFOChannel
        mapping learnedChan[_] via UnbufferedChannel;

    fair process (heartbeatAction \in Heartbeat) == instance HeartbeatAction(ref network, lastSeenAbstract, ref sleeperAbstract, electionInProgresssAbstract, iAmTheLeaderAbstract, 100) \* frequency is irrelevant in model checking
        mapping electionInProgresssAbstract[_] via Identity
        mapping iAmTheLeaderAbstract[_] via Identity
        mapping network[_] via FIFOChannel;

    fair process (leaderStatusMonitor \in LeaderMonitor) == instance LeaderStatusMonitor(timeoutCheckerAbstract, monitorLastSeen, ref leaderFailureAbstract, ref electionInProgresssAbstract, ref iAmTheLeaderAbstract, ref sleeperAbstract, 100) \* frequency is irrelevant in model checking
        mapping timeoutCheckerAbstract[_] via LeaderFailures
        mapping leaderFailureAbstract[_] via Identity
        mapping electionInProgresssAbstract[_] via Identity
        mapping iAmTheLeaderAbstract[_] via Identity;

    fair process (kvRequests \in KVRequests) == instance KeyValueRequests(requestSet, ref kvClient, iAmTheLeaderAbstract, values, paxosLayerChan, database, idAbstract)
        mapping requestSet via NextRequest
        mapping iAmTheLeaderAbstract[_] via Identity
        mapping values[_] via UnbufferedChannel
        mapping paxosLayerChan[_] via UnbufferedChannel
        mapping database[_] via Identity
        mapping idAbstract via Self;

    fair process (kvPaxosManager \in KVPaxosManager) == instance KeyValuePaxosManager(ref paxosLayerChan, learnedChan, ref database, idAbstract)
        mapping paxosLayerChan[_] via UnbufferedChannel
        mapping learnedChan[_] via UnbufferedChannel
        mapping database[_] via Identity
        mapping idAbstract via SelfManager;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm Paxos {
    variables network = [id \in AllNodes |-> <<>>], values = [p \in Proposer |-> [value |-> NULL]], lastSeenAbstract, monitorLastSeen = 0, timeoutCheckerAbstract = [monitorLastseen |-> 0], sleeperAbstract, kvClient, idAbstract, requestSet = ({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \cup ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}), learnedChan = [l \in Learner |-> [value |-> NULL]], paxosLayerChan = [p \in KVRequests |-> [value |-> NULL]], database = [p \in KVRequests, k \in PutSet |-> NULL], electionInProgresssAbstract = [h \in Heartbeat |-> TRUE], iAmTheLeaderAbstract = [h \in Heartbeat |-> FALSE], leaderFailureAbstract = [h \in Heartbeat |-> FALSE], valueStreamRead, mailboxesWrite, mailboxesWrite0, mailboxesRead, iAmTheLeaderWrite, electionInProgressWrite, leaderFailureRead, iAmTheLeaderWrite0, electionInProgressWrite0, iAmTheLeaderWrite1, electionInProgressWrite1, mailboxesWrite1, iAmTheLeaderWrite2, electionInProgressWrite2, mailboxesWrite2, iAmTheLeaderWrite3, electionInProgressWrite3, iAmTheLeaderWrite4, electionInProgressWrite4, mailboxesWrite3, electionInProgressWrite5, mailboxesWrite4, iAmTheLeaderWrite5, electionInProgressWrite6, mailboxesWrite5, mailboxesWrite6, iAmTheLeaderWrite6, electionInProgressWrite7, mailboxesWrite7, iAmTheLeaderWrite7, electionInProgressWrite8, mailboxesWrite8, iAmTheLeaderWrite8, electionInProgressWrite9, mailboxesRead0, mailboxesWrite9, mailboxesWrite10, mailboxesWrite11, mailboxesWrite12, mailboxesWrite13, mailboxesWrite14, mailboxesWrite15, mailboxesRead1, mailboxesWrite16, decidedWrite, decidedWrite0, decidedWrite1, decidedWrite2, mailboxesWrite17, decidedWrite3, electionInProgressRead, iAmTheLeaderRead, mailboxesWrite18, mailboxesWrite19, heartbeatFrequencyRead, sleeperWrite, mailboxesWrite20, sleeperWrite0, mailboxesWrite21, sleeperWrite1, mailboxesRead2, lastSeenWrite, mailboxesWrite22, lastSeenWrite0, mailboxesWrite23, sleeperWrite2, lastSeenWrite1, electionInProgressRead0, iAmTheLeaderRead0, lastSeenRead, timeoutCheckerRead, timeoutCheckerWrite, timeoutCheckerWrite0, timeoutCheckerWrite1, leaderFailureWrite, electionInProgressWrite10, leaderFailureWrite0, electionInProgressWrite11, timeoutCheckerWrite2, leaderFailureWrite1, electionInProgressWrite12, monitorFrequencyRead, sleeperWrite3, timeoutCheckerWrite3, leaderFailureWrite2, electionInProgressWrite13, sleeperWrite4, requestsRead, requestsWrite, myIdRead, dbRead, upstreamWrite, upstreamWrite0, iAmTheLeaderRead1, proposerChanWrite, paxosChanRead, proposerChanWrite0, upstreamWrite1, proposerChanWrite1, upstreamWrite2, requestsWrite0, upstreamWrite3, proposerChanWrite2, learnerChanRead, kvIdRead, dbWrite, kvIdRead0, kvIdRead1, requestServiceWrite, requestServiceWrite0, dbWrite0, requestServiceWrite1;
    define {
        Proposer == (0) .. ((NUM_NODES) - (1))
        Acceptor == (NUM_NODES) .. (((2) * (NUM_NODES)) - (1))
        Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
        Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
        LeaderMonitor == ((4) * (NUM_NODES)) .. (((5) * (NUM_NODES)) - (1))
        KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
        KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
        AllNodes == (0) .. (((4) * (NUM_NODES)) - (1))
        PREPARE_MSG == 0
        PROMISE_MSG == 1
        PROPOSE_MSG == 2
        ACCEPT_MSG == 3
        REJECT_MSG == 4
        HEARTBEAT_MSG == 5
        GET_MSG == 6
        PUT_MSG == 7
        GET_RESPONSE_MSG == 8
        PUT_NOT_LEADER_MSG == 9
        PUT_OK_MSG == 10
    }
    fair process (proposer \in Proposer)
    variables b, s = 1, elected = FALSE, acceptedValues = <<>>, max = [slot |-> -(1), bal |-> -(1), val |-> -(1)], index, entry, promises, heartbeatMonitorId, accepts = 0, value, repropose, resp;
    {
        Pre:
            b := self;
            heartbeatMonitorId := (self) + ((3) * (NUM_NODES));
        P:
            if (TRUE) {
                PLeaderCheck:
                    if (elected) {
                        accepts := 0;
                        repropose := FALSE;
                        index := 1;
                        PFindMaxVal:
                            if ((index) <= (Len(acceptedValues))) {
                                entry := acceptedValues[index];
                                if ((((entry).slot) = (s)) /\ (((entry).bal) >= ((max).bal))) {
                                    repropose := TRUE;
                                    value := (entry).val;
                                    max := entry;
                                };
                                index := (index) + (1);
                                goto PFindMaxVal;
                            } else {
                                if (~(repropose)) {
                                    await ((values[self]).value) # (NULL);
                                    with (v0 = values[self]) {
                                        values[self].value := NULL;
                                        valueStreamRead := v0;
                                    };
                                    value := valueStreamRead;
                                };
                                index := NUM_NODES;
                            };

                        PSendProposes:
                            if ((index) <= (((2) * (NUM_NODES)) - (1))) {
                                await (Len(network[index])) < (BUFFER_SIZE);
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
                                        iAmTheLeaderWrite1 := iAmTheLeaderAbstract;
                                        electionInProgressWrite1 := electionInProgresssAbstract;
                                        mailboxesWrite1 := mailboxesWrite;
                                        iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                        electionInProgressWrite2 := electionInProgressWrite1;
                                        network := mailboxesWrite1;
                                        electionInProgresssAbstract := electionInProgressWrite2;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite2;
                                        goto PSearchAccs;
                                    } else {
                                        iAmTheLeaderWrite1 := iAmTheLeaderAbstract;
                                        electionInProgressWrite1 := electionInProgresssAbstract;
                                        mailboxesWrite1 := mailboxesWrite;
                                        iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                        electionInProgressWrite2 := electionInProgressWrite1;
                                        network := mailboxesWrite1;
                                        electionInProgresssAbstract := electionInProgressWrite2;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite2;
                                        goto PSearchAccs;
                                    };
                                } else {
                                    if (((resp).type) = (REJECT_MSG)) {
                                        elected := FALSE;
                                        iAmTheLeaderWrite := [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId] = FALSE];
                                        electionInProgressWrite := [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId] = FALSE];
                                        await (leaderFailureAbstract[heartbeatMonitorId]) = (TRUE);
                                        leaderFailureRead := leaderFailureAbstract[heartbeatMonitorId];
                                        assert (leaderFailureRead) = (TRUE);
                                        iAmTheLeaderWrite0 := iAmTheLeaderWrite;
                                        electionInProgressWrite0 := electionInProgressWrite;
                                        iAmTheLeaderWrite1 := iAmTheLeaderWrite0;
                                        electionInProgressWrite1 := electionInProgressWrite0;
                                        mailboxesWrite1 := mailboxesWrite;
                                        iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                        electionInProgressWrite2 := electionInProgressWrite1;
                                        network := mailboxesWrite1;
                                        electionInProgresssAbstract := electionInProgressWrite2;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite2;
                                        goto PSearchAccs;
                                    } else {
                                        iAmTheLeaderWrite0 := iAmTheLeaderAbstract;
                                        electionInProgressWrite0 := electionInProgresssAbstract;
                                        iAmTheLeaderWrite1 := iAmTheLeaderWrite0;
                                        electionInProgressWrite1 := electionInProgressWrite0;
                                        mailboxesWrite1 := mailboxesWrite;
                                        iAmTheLeaderWrite2 := iAmTheLeaderWrite1;
                                        electionInProgressWrite2 := electionInProgressWrite1;
                                        network := mailboxesWrite1;
                                        electionInProgresssAbstract := electionInProgressWrite2;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite2;
                                        goto PSearchAccs;
                                    };
                                };
                            } else {
                                mailboxesWrite1 := network;
                                iAmTheLeaderWrite2 := iAmTheLeaderAbstract;
                                electionInProgressWrite2 := electionInProgresssAbstract;
                                network := mailboxesWrite1;
                                electionInProgresssAbstract := electionInProgressWrite2;
                                iAmTheLeaderAbstract := iAmTheLeaderWrite2;
                            };

                        PIncSlot:
                            if (elected) {
                                s := (s) + (1);
                                goto P;
                            } else {
                                goto P;
                            };

                    } else {
                        index := NUM_NODES;
                        PReqVotes:
                            if ((index) <= (((2) * (NUM_NODES)) - (1))) {
                                await (Len(network[index])) < (BUFFER_SIZE);
                                mailboxesWrite := [network EXCEPT ![index] = Append(network[index], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL])];
                                index := (index) + (1);
                                mailboxesWrite2 := mailboxesWrite;
                                iAmTheLeaderWrite3 := iAmTheLeaderAbstract;
                                electionInProgressWrite3 := electionInProgresssAbstract;
                                network := mailboxesWrite2;
                                electionInProgresssAbstract := electionInProgressWrite3;
                                iAmTheLeaderAbstract := iAmTheLeaderWrite3;
                                goto PReqVotes;
                            } else {
                                promises := 0;
                                iAmTheLeaderWrite := [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId] = FALSE];
                                electionInProgressWrite := [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId] = TRUE];
                                mailboxesWrite2 := network;
                                iAmTheLeaderWrite3 := iAmTheLeaderWrite;
                                electionInProgressWrite3 := electionInProgressWrite;
                                network := mailboxesWrite2;
                                electionInProgresssAbstract := electionInProgressWrite3;
                                iAmTheLeaderAbstract := iAmTheLeaderWrite3;
                            };

                        PCandidate:
                            if (~(elected)) {
                                await (Len(network[self])) > (0);
                                with (msg1 = Head(network[self])) {
                                    mailboxesWrite := [network EXCEPT ![self] = Tail(network[self])];
                                    mailboxesRead := msg1;
                                };
                                resp := mailboxesRead;
                                if ((((resp).type) = (PROMISE_MSG)) /\ (((resp).bal) = (b))) {
                                    acceptedValues := (acceptedValues) \o ((resp).accepted);
                                    promises := (promises) + (1);
                                    if (((promises) * (2)) > (Cardinality(Acceptor))) {
                                        elected := TRUE;
                                        iAmTheLeaderWrite := [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId] = TRUE];
                                        electionInProgressWrite := [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId] = FALSE];
                                        iAmTheLeaderWrite4 := iAmTheLeaderWrite;
                                        electionInProgressWrite4 := electionInProgressWrite;
                                        iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                        electionInProgressWrite6 := electionInProgressWrite4;
                                        mailboxesWrite5 := network;
                                        mailboxesWrite6 := mailboxesWrite5;
                                        iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                        electionInProgressWrite7 := electionInProgressWrite6;
                                        network := mailboxesWrite6;
                                        electionInProgresssAbstract := electionInProgressWrite7;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite6;
                                        goto PCandidate;
                                    } else {
                                        iAmTheLeaderWrite4 := iAmTheLeaderAbstract;
                                        electionInProgressWrite4 := electionInProgresssAbstract;
                                        iAmTheLeaderWrite5 := iAmTheLeaderWrite4;
                                        electionInProgressWrite6 := electionInProgressWrite4;
                                        mailboxesWrite5 := network;
                                        mailboxesWrite6 := mailboxesWrite5;
                                        iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                        electionInProgressWrite7 := electionInProgressWrite6;
                                        network := mailboxesWrite6;
                                        electionInProgresssAbstract := electionInProgressWrite7;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite6;
                                        goto PCandidate;
                                    };
                                } else {
                                    if ((((resp).type) = (REJECT_MSG)) \/ (((resp).bal) > (b))) {
                                        electionInProgressWrite := [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId] = FALSE];
                                        await (leaderFailureAbstract[heartbeatMonitorId]) = (TRUE);
                                        leaderFailureRead := leaderFailureAbstract[heartbeatMonitorId];
                                        assert (leaderFailureRead) = (TRUE);
                                        b := (b) + (NUM_NODES);
                                        index := NUM_NODES;
                                        network := mailboxesWrite;
                                        electionInProgresssAbstract := electionInProgressWrite;
                                        PReSendReqVotes:
                                            if ((index) <= (((2) * (NUM_NODES)) - (1))) {
                                                await (Len(network[index])) < (BUFFER_SIZE);
                                                mailboxesWrite := [network EXCEPT ![index] = Append(network[index], [type |-> PREPARE_MSG, bal |-> b, sender |-> self, slot |-> NULL, val |-> NULL])];
                                                index := (index) + (1);
                                                mailboxesWrite3 := mailboxesWrite;
                                                network := mailboxesWrite3;
                                                goto PReSendReqVotes;
                                            } else {
                                                mailboxesWrite3 := network;
                                                network := mailboxesWrite3;
                                                goto PCandidate;
                                            };

                                    } else {
                                        electionInProgressWrite5 := electionInProgresssAbstract;
                                        mailboxesWrite4 := network;
                                        iAmTheLeaderWrite5 := iAmTheLeaderAbstract;
                                        electionInProgressWrite6 := electionInProgressWrite5;
                                        mailboxesWrite5 := mailboxesWrite4;
                                        mailboxesWrite6 := mailboxesWrite5;
                                        iAmTheLeaderWrite6 := iAmTheLeaderWrite5;
                                        electionInProgressWrite7 := electionInProgressWrite6;
                                        network := mailboxesWrite6;
                                        electionInProgresssAbstract := electionInProgressWrite7;
                                        iAmTheLeaderAbstract := iAmTheLeaderWrite6;
                                        goto PCandidate;
                                    };
                                };
                            } else {
                                mailboxesWrite6 := network;
                                iAmTheLeaderWrite6 := iAmTheLeaderAbstract;
                                electionInProgressWrite7 := electionInProgresssAbstract;
                                network := mailboxesWrite6;
                                electionInProgresssAbstract := electionInProgressWrite7;
                                iAmTheLeaderAbstract := iAmTheLeaderWrite6;
                                goto P;
                            };

                    };

            } else {
                mailboxesWrite8 := network;
                iAmTheLeaderWrite8 := iAmTheLeaderAbstract;
                electionInProgressWrite9 := electionInProgresssAbstract;
                network := mailboxesWrite8;
                electionInProgresssAbstract := electionInProgressWrite9;
                iAmTheLeaderAbstract := iAmTheLeaderWrite8;
            };

    }
    fair process (acceptor \in Acceptor)
    variables maxBal = -(1), loopIndex, acceptedValues = <<>>, payload, msg;
    {
        A:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg2 = Head(network[self])) {
                    mailboxesWrite9 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead0 := msg2;
                };
                msg := mailboxesRead0;
                network := mailboxesWrite9;
                AMsgSwitch:
                    if ((((msg).type) = (PREPARE_MSG)) /\ (((msg).bal) > (maxBal))) {
                        APrepare:
                            maxBal := (msg).bal;
                            await (Len(network[(msg).sender])) < (BUFFER_SIZE);
                            mailboxesWrite9 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal, slot |-> NULL, val |-> NULL, accepted |-> acceptedValues])];
                            network := mailboxesWrite9;
                            goto A;

                    } else {
                        if ((((msg).type) = (PREPARE_MSG)) /\ (((msg).bal) <= (maxBal))) {
                            ABadPrepare:
                                await (Len(network[(msg).sender])) < (BUFFER_SIZE);
                                mailboxesWrite9 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> NULL, val |-> NULL, accepted |-> <<>>])];
                                network := mailboxesWrite9;
                                goto A;

                        } else {
                            if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) >= (maxBal))) {
                                APropose:
                                    maxBal := (msg).bal;
                                    payload := [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, accepted |-> <<>>];
                                    acceptedValues := Append(acceptedValues, [slot |-> (msg).slot, bal |-> (msg).bal, val |-> (msg).val]);
                                    await (Len(network[(msg).sender])) < (BUFFER_SIZE);
                                    mailboxesWrite9 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], payload)];
                                    loopIndex := (2) * (NUM_NODES);
                                    network := mailboxesWrite9;

                                ANotifyLearners:
                                    if ((loopIndex) <= (((3) * (NUM_NODES)) - (1))) {
                                        await (Len(network[loopIndex])) < (BUFFER_SIZE);
                                        mailboxesWrite9 := [network EXCEPT ![loopIndex] = Append(network[loopIndex], payload)];
                                        loopIndex := (loopIndex) + (1);
                                        mailboxesWrite10 := mailboxesWrite9;
                                        network := mailboxesWrite10;
                                        goto ANotifyLearners;
                                    } else {
                                        mailboxesWrite10 := network;
                                        network := mailboxesWrite10;
                                        goto A;
                                    };

                            } else {
                                if ((((msg).type) = (PROPOSE_MSG)) /\ (((msg).bal) < (maxBal))) {
                                    ABadPropose:
                                        await (Len(network[(msg).sender])) < (BUFFER_SIZE);
                                        mailboxesWrite9 := [network EXCEPT ![(msg).sender] = Append(network[(msg).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal, slot |-> (msg).slot, val |-> (msg).val, accepted |-> <<>>])];
                                        network := mailboxesWrite9;
                                        goto A;

                                } else {
                                    mailboxesWrite11 := network;
                                    mailboxesWrite12 := mailboxesWrite11;
                                    mailboxesWrite13 := mailboxesWrite12;
                                    mailboxesWrite14 := mailboxesWrite13;
                                    network := mailboxesWrite14;
                                    goto A;
                                };
                            };
                        };
                    };

            } else {
                mailboxesWrite15 := network;
                network := mailboxesWrite15;
            };

    }
    fair process (learner \in Learner)
    variables accepts = <<>>, newAccepts, numAccepted, iterator, entry, msg;
    {
        L:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg3 = Head(network[self])) {
                    mailboxesWrite16 := [network EXCEPT ![self] = Tail(network[self])];
                    mailboxesRead1 := msg3;
                };
                msg := mailboxesRead1;
                network := mailboxesWrite16;
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
                                decidedWrite1 := learnedChan;
                                learnedChan := decidedWrite1;
                                goto LCheckMajority;
                            } else {
                                if (((numAccepted) * (2)) > (Cardinality(Acceptor))) {
                                    await ((learnedChan[self]).value) = (NULL);
                                    decidedWrite := [learnedChan EXCEPT ![self] = (msg).val];
                                    newAccepts := <<>>;
                                    iterator := 1;
                                    learnedChan := decidedWrite;
                                    garbageCollection:
                                        if ((iterator) <= (Len(accepts))) {
                                            entry := accepts[iterator];
                                            if (((entry).slot) # ((msg).slot)) {
                                                newAccepts := Append(newAccepts, entry);
                                            };
                                            iterator := (iterator) + (1);
                                            goto garbageCollection;
                                        } else {
                                            accepts := newAccepts;
                                            goto L;
                                        };

                                } else {
                                    decidedWrite0 := learnedChan;
                                    decidedWrite1 := decidedWrite0;
                                    learnedChan := decidedWrite1;
                                    goto L;
                                };
                            };

                    } else {
                        decidedWrite2 := learnedChan;
                        learnedChan := decidedWrite2;
                        goto L;
                    };

            } else {
                mailboxesWrite17 := network;
                decidedWrite3 := learnedChan;
                network := mailboxesWrite17;
                learnedChan := decidedWrite3;
            };

    }
    fair process (heartbeatAction \in Heartbeat)
    variables heartbeatFrequencyLocal = 100, msg, index;
    {
        mainLoop:
            if (TRUE) {
                leaderLoop:
                    electionInProgressRead := electionInProgresssAbstract[self];
                    iAmTheLeaderRead := iAmTheLeaderAbstract[self];
                    if ((~(electionInProgressRead)) /\ (iAmTheLeaderRead)) {
                        index := (3) * (NUM_NODES);
                        heartbeatBroadcast:
                            if ((index) <= (((4) * (NUM_NODES)) - (1))) {
                                if ((index) # (self)) {
                                    await (Len(network[index])) < (BUFFER_SIZE);
                                    mailboxesWrite18 := [network EXCEPT ![index] = Append(network[index], [type |-> HEARTBEAT_MSG, leader |-> (self) - ((3) * (NUM_NODES))])];
                                    index := (index) + (1);
                                    mailboxesWrite19 := mailboxesWrite18;
                                    mailboxesWrite20 := mailboxesWrite19;
                                    sleeperWrite0 := sleeperAbstract;
                                    network := mailboxesWrite20;
                                    sleeperAbstract := sleeperWrite0;
                                    goto heartbeatBroadcast;
                                } else {
                                    mailboxesWrite19 := network;
                                    mailboxesWrite20 := mailboxesWrite19;
                                    sleeperWrite0 := sleeperAbstract;
                                    network := mailboxesWrite20;
                                    sleeperAbstract := sleeperWrite0;
                                    goto heartbeatBroadcast;
                                };
                            } else {
                                heartbeatFrequencyRead := heartbeatFrequencyLocal;
                                sleeperWrite := heartbeatFrequencyRead;
                                mailboxesWrite20 := network;
                                sleeperWrite0 := sleeperWrite;
                                network := mailboxesWrite20;
                                sleeperAbstract := sleeperWrite0;
                                goto leaderLoop;
                            };

                    } else {
                        mailboxesWrite21 := network;
                        sleeperWrite1 := sleeperAbstract;
                        network := mailboxesWrite21;
                        sleeperAbstract := sleeperWrite1;
                    };

                followerLoop:
                    electionInProgressRead := electionInProgresssAbstract[self];
                    iAmTheLeaderRead := iAmTheLeaderAbstract[self];
                    if ((~(electionInProgressRead)) /\ (~(iAmTheLeaderRead))) {
                        await (Len(network[self])) > (0);
                        with (msg4 = Head(network[self])) {
                            mailboxesWrite18 := [network EXCEPT ![self] = Tail(network[self])];
                            mailboxesRead2 := msg4;
                        };
                        msg := mailboxesRead2;
                        assert ((msg).type) = (HEARTBEAT_MSG);
                        lastSeenWrite := msg;
                        mailboxesWrite22 := mailboxesWrite18;
                        lastSeenWrite0 := lastSeenWrite;
                        network := mailboxesWrite22;
                        lastSeenAbstract := lastSeenWrite0;
                        goto followerLoop;
                    } else {
                        mailboxesWrite22 := network;
                        lastSeenWrite0 := lastSeenAbstract;
                        network := mailboxesWrite22;
                        lastSeenAbstract := lastSeenWrite0;
                        goto mainLoop;
                    };

            } else {
                mailboxesWrite23 := network;
                sleeperWrite2 := sleeperAbstract;
                lastSeenWrite1 := lastSeenAbstract;
                network := mailboxesWrite23;
                lastSeenAbstract := lastSeenWrite1;
                sleeperAbstract := sleeperWrite2;
            };

    }
    fair process (leaderStatusMonitor \in LeaderMonitor)
    variables monitorFrequencyLocal = 100, heartbeatId;
    {
        findId:
            heartbeatId := (self) - (NUM_NODES);
        monitorLoop:
            if (TRUE) {
                electionInProgressRead0 := electionInProgresssAbstract[heartbeatId];
                iAmTheLeaderRead0 := iAmTheLeaderAbstract[heartbeatId];
                if ((~(electionInProgressRead0)) /\ (~(iAmTheLeaderRead0))) {
                    lastSeenRead := monitorLastSeen;
                    if ((timeoutCheckerAbstract[lastSeenRead]) < (MAX_FAILURES)) {
                        either {
                            timeoutCheckerWrite := [timeoutCheckerAbstract EXCEPT ![lastSeenRead] = (timeoutCheckerAbstract[lastSeenRead]) + (1)];
                            timeoutCheckerRead := TRUE;
                            timeoutCheckerWrite0 := timeoutCheckerWrite;
                            timeoutCheckerWrite1 := timeoutCheckerWrite0;
                        } or {
                            timeoutCheckerRead := FALSE;
                            timeoutCheckerWrite0 := timeoutCheckerAbstract;
                            timeoutCheckerWrite1 := timeoutCheckerWrite0;
                        };
                    } else {
                        timeoutCheckerRead := FALSE;
                        timeoutCheckerWrite1 := timeoutCheckerAbstract;
                    };
                    if (timeoutCheckerRead) {
                        leaderFailureWrite := [leaderFailureAbstract EXCEPT ![heartbeatId] = TRUE];
                        electionInProgressWrite10 := [electionInProgresssAbstract EXCEPT ![heartbeatId] = TRUE];
                        leaderFailureWrite0 := leaderFailureWrite;
                        electionInProgressWrite11 := electionInProgressWrite10;
                        timeoutCheckerWrite2 := timeoutCheckerWrite1;
                        leaderFailureWrite1 := leaderFailureWrite0;
                        electionInProgressWrite12 := electionInProgressWrite11;
                    } else {
                        leaderFailureWrite0 := leaderFailureAbstract;
                        electionInProgressWrite11 := electionInProgresssAbstract;
                        timeoutCheckerWrite2 := timeoutCheckerWrite1;
                        leaderFailureWrite1 := leaderFailureWrite0;
                        electionInProgressWrite12 := electionInProgressWrite11;
                    };
                } else {
                    timeoutCheckerWrite2 := timeoutCheckerAbstract;
                    leaderFailureWrite1 := leaderFailureAbstract;
                    electionInProgressWrite12 := electionInProgresssAbstract;
                };
                monitorFrequencyRead := monitorFrequencyLocal;
                sleeperWrite3 := monitorFrequencyRead;
                timeoutCheckerWrite3 := timeoutCheckerWrite2;
                leaderFailureWrite2 := leaderFailureWrite1;
                electionInProgressWrite13 := electionInProgressWrite12;
                sleeperWrite4 := sleeperWrite3;
                timeoutCheckerAbstract := timeoutCheckerWrite3;
                leaderFailureAbstract := leaderFailureWrite2;
                electionInProgresssAbstract := electionInProgressWrite13;
                sleeperAbstract := sleeperWrite4;
                goto monitorLoop;
            } else {
                timeoutCheckerWrite3 := timeoutCheckerAbstract;
                leaderFailureWrite2 := leaderFailureAbstract;
                electionInProgressWrite13 := electionInProgresssAbstract;
                sleeperWrite4 := sleeperAbstract;
                timeoutCheckerAbstract := timeoutCheckerWrite3;
                leaderFailureAbstract := leaderFailureWrite2;
                electionInProgresssAbstract := electionInProgressWrite13;
                sleeperAbstract := sleeperWrite4;
            };

    }
    fair process (kvRequests \in KVRequests)
    variables msg, null, heartbeatId, proposerId, counter = 0, requestId, putOk, confirmedRequestId;
    {
        kvInit:
            heartbeatId := (self) - ((2) * (NUM_NODES));
            proposerId := (self) - ((5) * (NUM_NODES));
        kvLoop:
            if (TRUE) {
                await (Cardinality(requestSet)) > (0);
                with (req0 \in requestSet) {
                    requestsWrite := (requestSet) \ ({req0});
                    requestsRead := req0;
                };
                msg := requestsRead;
                assert (((msg).type) = (GET_MSG)) \/ (((msg).type) = (PUT_MSG));
                requestSet := requestsWrite;
                checkGet:
                    if (((msg).type) = (GET_MSG)) {
                        myIdRead := self;
                        dbRead := database[<<myIdRead, (msg).key>>];
                        upstreamWrite := [type |-> GET_RESPONSE_MSG, result |-> dbRead];
                        upstreamWrite0 := upstreamWrite;
                        kvClient := upstreamWrite0;
                    } else {
                        upstreamWrite0 := kvClient;
                        kvClient := upstreamWrite0;
                    };

                checkPut:
                    if (((msg).type) = (PUT_MSG)) {
                        iAmTheLeaderRead1 := iAmTheLeaderAbstract[heartbeatId];
                        if (iAmTheLeaderRead1) {
                            requestId := <<self, counter>>;
                            await ((values[proposerId]).value) = (NULL);
                            proposerChanWrite := [values EXCEPT ![proposerId] = [id |-> requestId, key |-> (msg).key, value |-> (msg).value]];
                            values := proposerChanWrite;
                            putConfirm:
                                await ((paxosLayerChan[self]).value) # (NULL);
                                with (v1 = paxosLayerChan[self]) {
                                    paxosLayerChan[self].value := NULL;
                                    paxosChanRead := v1;
                                };
                                putOk := paxosChanRead;
                                confirmedRequestId := (putOk).id;
                                assert ((confirmedRequestId[1]) = (self)) /\ ((confirmedRequestId[2]) = (counter));
                                upstreamWrite := [type |-> PUT_OK_MSG, result |-> null];
                                counter := (counter) + (1);
                                kvClient := upstreamWrite;
                                goto kvLoop;

                        } else {
                            upstreamWrite := [type |-> PUT_NOT_LEADER_MSG, result |-> null];
                            proposerChanWrite0 := values;
                            upstreamWrite1 := upstreamWrite;
                            proposerChanWrite1 := proposerChanWrite0;
                            upstreamWrite2 := upstreamWrite1;
                            kvClient := upstreamWrite2;
                            values := proposerChanWrite1;
                            goto kvLoop;
                        };
                    } else {
                        proposerChanWrite1 := values;
                        upstreamWrite2 := kvClient;
                        kvClient := upstreamWrite2;
                        values := proposerChanWrite1;
                        goto kvLoop;
                    };

            } else {
                requestsWrite0 := requestSet;
                upstreamWrite3 := kvClient;
                proposerChanWrite2 := values;
                requestSet := requestsWrite0;
                kvClient := upstreamWrite3;
                values := proposerChanWrite2;
            };

    }
    fair process (kvPaxosManager \in KVPaxosManager)
    variables learnerId, operation, requestId;
    {
        findId:
            learnerId := (self) - ((4) * (NUM_NODES));
        kvManagerLoop:
            if (TRUE) {
                await ((learnedChan[learnerId]).value) # (NULL);
                with (v2 = learnedChan[learnerId]) {
                    learnedChan[learnerId].value := NULL;
                    learnerChanRead := v2;
                };
                operation := learnerChanRead;
                requestId := (operation).id;
                kvIdRead := (self) - (NUM_NODES);
                dbWrite := [database EXCEPT ![<<kvIdRead, (operation).key>>] = (operation).value];
                kvIdRead0 := (self) - (NUM_NODES);
                if ((requestId[1]) = (kvIdRead0)) {
                    kvIdRead1 := (self) - (NUM_NODES);
                    await ((paxosLayerChan[kvIdRead1]).value) = (NULL);
                    requestServiceWrite := [paxosLayerChan EXCEPT ![kvIdRead1] = operation];
                    requestServiceWrite0 := requestServiceWrite;
                    dbWrite0 := dbWrite;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    database := dbWrite0;
                    goto kvManagerLoop;
                } else {
                    requestServiceWrite0 := paxosLayerChan;
                    dbWrite0 := dbWrite;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    database := dbWrite0;
                    goto kvManagerLoop;
                };
            } else {
                dbWrite0 := database;
                requestServiceWrite1 := paxosLayerChan;
                paxosLayerChan := requestServiceWrite1;
                database := dbWrite0;
            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)

\* BEGIN TRANSLATION
\* Label findId of process leaderStatusMonitor at line 1057 col 13 changed to findId_
\* Process variable acceptedValues of process proposer at line 566 col 42 changed to acceptedValues_
\* Process variable index of process proposer at line 566 col 116 changed to index_
\* Process variable entry of process proposer at line 566 col 123 changed to entry_
\* Process variable accepts of process proposer at line 566 col 160 changed to accepts_
\* Process variable msg of process acceptor at line 823 col 73 changed to msg_
\* Process variable msg of process learner at line 903 col 73 changed to msg_l
\* Process variable msg of process heartbeatAction at line 972 col 46 changed to msg_h
\* Process variable heartbeatId of process leaderStatusMonitor at line 1054 col 44 changed to heartbeatId_
\* Process variable requestId of process kvRequests at line 1123 col 64 changed to requestId_
CONSTANT defaultInitValue
VARIABLES network, values, lastSeenAbstract, monitorLastSeen,
          timeoutCheckerAbstract, sleeperAbstract, kvClient, idAbstract,
          requestSet, learnedChan, paxosLayerChan, database,
          electionInProgresssAbstract, iAmTheLeaderAbstract,
          leaderFailureAbstract, valueStreamRead, mailboxesWrite,
          mailboxesWrite0, mailboxesRead, iAmTheLeaderWrite,
          electionInProgressWrite, leaderFailureRead, iAmTheLeaderWrite0,
          electionInProgressWrite0, iAmTheLeaderWrite1,
          electionInProgressWrite1, mailboxesWrite1, iAmTheLeaderWrite2,
          electionInProgressWrite2, mailboxesWrite2, iAmTheLeaderWrite3,
          electionInProgressWrite3, iAmTheLeaderWrite4,
          electionInProgressWrite4, mailboxesWrite3, electionInProgressWrite5,
          mailboxesWrite4, iAmTheLeaderWrite5, electionInProgressWrite6,
          mailboxesWrite5, mailboxesWrite6, iAmTheLeaderWrite6,
          electionInProgressWrite7, mailboxesWrite7, iAmTheLeaderWrite7,
          electionInProgressWrite8, mailboxesWrite8, iAmTheLeaderWrite8,
          electionInProgressWrite9, mailboxesRead0, mailboxesWrite9,
          mailboxesWrite10, mailboxesWrite11, mailboxesWrite12,
          mailboxesWrite13, mailboxesWrite14, mailboxesWrite15,
          mailboxesRead1, mailboxesWrite16, decidedWrite, decidedWrite0,
          decidedWrite1, decidedWrite2, mailboxesWrite17, decidedWrite3,
          electionInProgressRead, iAmTheLeaderRead, mailboxesWrite18,
          mailboxesWrite19, heartbeatFrequencyRead, sleeperWrite,
          mailboxesWrite20, sleeperWrite0, mailboxesWrite21, sleeperWrite1,
          mailboxesRead2, lastSeenWrite, mailboxesWrite22, lastSeenWrite0,
          mailboxesWrite23, sleeperWrite2, lastSeenWrite1,
          electionInProgressRead0, iAmTheLeaderRead0, lastSeenRead,
          timeoutCheckerRead, timeoutCheckerWrite, timeoutCheckerWrite0,
          timeoutCheckerWrite1, leaderFailureWrite, electionInProgressWrite10,
          leaderFailureWrite0, electionInProgressWrite11,
          timeoutCheckerWrite2, leaderFailureWrite1,
          electionInProgressWrite12, monitorFrequencyRead, sleeperWrite3,
          timeoutCheckerWrite3, leaderFailureWrite2,
          electionInProgressWrite13, sleeperWrite4, requestsRead,
          requestsWrite, myIdRead, dbRead, upstreamWrite, upstreamWrite0,
          iAmTheLeaderRead1, proposerChanWrite, paxosChanRead,
          proposerChanWrite0, upstreamWrite1, proposerChanWrite1,
          upstreamWrite2, requestsWrite0, upstreamWrite3, proposerChanWrite2,
          learnerChanRead, kvIdRead, dbWrite, kvIdRead0, kvIdRead1,
          requestServiceWrite, requestServiceWrite0, dbWrite0,
          requestServiceWrite1, pc

(* define statement *)
Proposer == (0) .. ((NUM_NODES) - (1))
Acceptor == (NUM_NODES) .. (((2) * (NUM_NODES)) - (1))
Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
LeaderMonitor == ((4) * (NUM_NODES)) .. (((5) * (NUM_NODES)) - (1))
KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
AllNodes == (0) .. (((4) * (NUM_NODES)) - (1))
PREPARE_MSG == 0
PROMISE_MSG == 1
PROPOSE_MSG == 2
ACCEPT_MSG == 3
REJECT_MSG == 4
HEARTBEAT_MSG == 5
GET_MSG == 6
PUT_MSG == 7
GET_RESPONSE_MSG == 8
PUT_NOT_LEADER_MSG == 9
PUT_OK_MSG == 10

VARIABLES b, s, elected, acceptedValues_, max, index_, entry_, promises,
          heartbeatMonitorId, accepts_, value, repropose, resp, maxBal,
          loopIndex, acceptedValues, payload, msg_, accepts, newAccepts,
          numAccepted, iterator, entry, msg_l, heartbeatFrequencyLocal, msg_h,
          index, monitorFrequencyLocal, heartbeatId_, msg, null, heartbeatId,
          proposerId, counter, requestId_, putOk, confirmedRequestId,
          learnerId, operation, requestId

vars == << network, values, lastSeenAbstract, monitorLastSeen,
           timeoutCheckerAbstract, sleeperAbstract, kvClient, idAbstract,
           requestSet, learnedChan, paxosLayerChan, database,
           electionInProgresssAbstract, iAmTheLeaderAbstract,
           leaderFailureAbstract, valueStreamRead, mailboxesWrite,
           mailboxesWrite0, mailboxesRead, iAmTheLeaderWrite,
           electionInProgressWrite, leaderFailureRead, iAmTheLeaderWrite0,
           electionInProgressWrite0, iAmTheLeaderWrite1,
           electionInProgressWrite1, mailboxesWrite1, iAmTheLeaderWrite2,
           electionInProgressWrite2, mailboxesWrite2, iAmTheLeaderWrite3,
           electionInProgressWrite3, iAmTheLeaderWrite4,
           electionInProgressWrite4, mailboxesWrite3,
           electionInProgressWrite5, mailboxesWrite4, iAmTheLeaderWrite5,
           electionInProgressWrite6, mailboxesWrite5, mailboxesWrite6,
           iAmTheLeaderWrite6, electionInProgressWrite7, mailboxesWrite7,
           iAmTheLeaderWrite7, electionInProgressWrite8, mailboxesWrite8,
           iAmTheLeaderWrite8, electionInProgressWrite9, mailboxesRead0,
           mailboxesWrite9, mailboxesWrite10, mailboxesWrite11,
           mailboxesWrite12, mailboxesWrite13, mailboxesWrite14,
           mailboxesWrite15, mailboxesRead1, mailboxesWrite16, decidedWrite,
           decidedWrite0, decidedWrite1, decidedWrite2, mailboxesWrite17,
           decidedWrite3, electionInProgressRead, iAmTheLeaderRead,
           mailboxesWrite18, mailboxesWrite19, heartbeatFrequencyRead,
           sleeperWrite, mailboxesWrite20, sleeperWrite0, mailboxesWrite21,
           sleeperWrite1, mailboxesRead2, lastSeenWrite, mailboxesWrite22,
           lastSeenWrite0, mailboxesWrite23, sleeperWrite2, lastSeenWrite1,
           electionInProgressRead0, iAmTheLeaderRead0, lastSeenRead,
           timeoutCheckerRead, timeoutCheckerWrite, timeoutCheckerWrite0,
           timeoutCheckerWrite1, leaderFailureWrite,
           electionInProgressWrite10, leaderFailureWrite0,
           electionInProgressWrite11, timeoutCheckerWrite2,
           leaderFailureWrite1, electionInProgressWrite12,
           monitorFrequencyRead, sleeperWrite3, timeoutCheckerWrite3,
           leaderFailureWrite2, electionInProgressWrite13, sleeperWrite4,
           requestsRead, requestsWrite, myIdRead, dbRead, upstreamWrite,
           upstreamWrite0, iAmTheLeaderRead1, proposerChanWrite,
           paxosChanRead, proposerChanWrite0, upstreamWrite1,
           proposerChanWrite1, upstreamWrite2, requestsWrite0, upstreamWrite3,
           proposerChanWrite2, learnerChanRead, kvIdRead, dbWrite, kvIdRead0,
           kvIdRead1, requestServiceWrite, requestServiceWrite0, dbWrite0,
           requestServiceWrite1, pc, b, s, elected, acceptedValues_, max,
           index_, entry_, promises, heartbeatMonitorId, accepts_, value,
           repropose, resp, maxBal, loopIndex, acceptedValues, payload, msg_,
           accepts, newAccepts, numAccepted, iterator, entry, msg_l,
           heartbeatFrequencyLocal, msg_h, index, monitorFrequencyLocal,
           heartbeatId_, msg, null, heartbeatId, proposerId, counter,
           requestId_, putOk, confirmedRequestId, learnerId, operation,
           requestId >>

ProcSet == (Proposer) \cup (Acceptor) \cup (Learner) \cup (Heartbeat) \cup (LeaderMonitor) \cup (KVRequests) \cup (KVPaxosManager)

Init == (* Global variables *)
        /\ network = [id \in AllNodes |-> <<>>]
        /\ values = [p \in Proposer |-> [value |-> NULL]]
        /\ lastSeenAbstract = defaultInitValue
        /\ monitorLastSeen = 0
        /\ timeoutCheckerAbstract = [monitorLastseen |-> 0]
        /\ sleeperAbstract = defaultInitValue
        /\ kvClient = defaultInitValue
        /\ idAbstract = defaultInitValue
        /\ requestSet = (({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \cup ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}))
        /\ learnedChan = [l \in Learner |-> [value |-> NULL]]
        /\ paxosLayerChan = [p \in KVRequests |-> [value |-> NULL]]
        /\ database = [p \in KVRequests, k \in PutSet |-> NULL]
        /\ electionInProgresssAbstract = [h \in Heartbeat |-> TRUE]
        /\ iAmTheLeaderAbstract = [h \in Heartbeat |-> FALSE]
        /\ leaderFailureAbstract = [h \in Heartbeat |-> FALSE]
        /\ valueStreamRead = defaultInitValue
        /\ mailboxesWrite = defaultInitValue
        /\ mailboxesWrite0 = defaultInitValue
        /\ mailboxesRead = defaultInitValue
        /\ iAmTheLeaderWrite = defaultInitValue
        /\ electionInProgressWrite = defaultInitValue
        /\ leaderFailureRead = defaultInitValue
        /\ iAmTheLeaderWrite0 = defaultInitValue
        /\ electionInProgressWrite0 = defaultInitValue
        /\ iAmTheLeaderWrite1 = defaultInitValue
        /\ electionInProgressWrite1 = defaultInitValue
        /\ mailboxesWrite1 = defaultInitValue
        /\ iAmTheLeaderWrite2 = defaultInitValue
        /\ electionInProgressWrite2 = defaultInitValue
        /\ mailboxesWrite2 = defaultInitValue
        /\ iAmTheLeaderWrite3 = defaultInitValue
        /\ electionInProgressWrite3 = defaultInitValue
        /\ iAmTheLeaderWrite4 = defaultInitValue
        /\ electionInProgressWrite4 = defaultInitValue
        /\ mailboxesWrite3 = defaultInitValue
        /\ electionInProgressWrite5 = defaultInitValue
        /\ mailboxesWrite4 = defaultInitValue
        /\ iAmTheLeaderWrite5 = defaultInitValue
        /\ electionInProgressWrite6 = defaultInitValue
        /\ mailboxesWrite5 = defaultInitValue
        /\ mailboxesWrite6 = defaultInitValue
        /\ iAmTheLeaderWrite6 = defaultInitValue
        /\ electionInProgressWrite7 = defaultInitValue
        /\ mailboxesWrite7 = defaultInitValue
        /\ iAmTheLeaderWrite7 = defaultInitValue
        /\ electionInProgressWrite8 = defaultInitValue
        /\ mailboxesWrite8 = defaultInitValue
        /\ iAmTheLeaderWrite8 = defaultInitValue
        /\ electionInProgressWrite9 = defaultInitValue
        /\ mailboxesRead0 = defaultInitValue
        /\ mailboxesWrite9 = defaultInitValue
        /\ mailboxesWrite10 = defaultInitValue
        /\ mailboxesWrite11 = defaultInitValue
        /\ mailboxesWrite12 = defaultInitValue
        /\ mailboxesWrite13 = defaultInitValue
        /\ mailboxesWrite14 = defaultInitValue
        /\ mailboxesWrite15 = defaultInitValue
        /\ mailboxesRead1 = defaultInitValue
        /\ mailboxesWrite16 = defaultInitValue
        /\ decidedWrite = defaultInitValue
        /\ decidedWrite0 = defaultInitValue
        /\ decidedWrite1 = defaultInitValue
        /\ decidedWrite2 = defaultInitValue
        /\ mailboxesWrite17 = defaultInitValue
        /\ decidedWrite3 = defaultInitValue
        /\ electionInProgressRead = defaultInitValue
        /\ iAmTheLeaderRead = defaultInitValue
        /\ mailboxesWrite18 = defaultInitValue
        /\ mailboxesWrite19 = defaultInitValue
        /\ heartbeatFrequencyRead = defaultInitValue
        /\ sleeperWrite = defaultInitValue
        /\ mailboxesWrite20 = defaultInitValue
        /\ sleeperWrite0 = defaultInitValue
        /\ mailboxesWrite21 = defaultInitValue
        /\ sleeperWrite1 = defaultInitValue
        /\ mailboxesRead2 = defaultInitValue
        /\ lastSeenWrite = defaultInitValue
        /\ mailboxesWrite22 = defaultInitValue
        /\ lastSeenWrite0 = defaultInitValue
        /\ mailboxesWrite23 = defaultInitValue
        /\ sleeperWrite2 = defaultInitValue
        /\ lastSeenWrite1 = defaultInitValue
        /\ electionInProgressRead0 = defaultInitValue
        /\ iAmTheLeaderRead0 = defaultInitValue
        /\ lastSeenRead = defaultInitValue
        /\ timeoutCheckerRead = defaultInitValue
        /\ timeoutCheckerWrite = defaultInitValue
        /\ timeoutCheckerWrite0 = defaultInitValue
        /\ timeoutCheckerWrite1 = defaultInitValue
        /\ leaderFailureWrite = defaultInitValue
        /\ electionInProgressWrite10 = defaultInitValue
        /\ leaderFailureWrite0 = defaultInitValue
        /\ electionInProgressWrite11 = defaultInitValue
        /\ timeoutCheckerWrite2 = defaultInitValue
        /\ leaderFailureWrite1 = defaultInitValue
        /\ electionInProgressWrite12 = defaultInitValue
        /\ monitorFrequencyRead = defaultInitValue
        /\ sleeperWrite3 = defaultInitValue
        /\ timeoutCheckerWrite3 = defaultInitValue
        /\ leaderFailureWrite2 = defaultInitValue
        /\ electionInProgressWrite13 = defaultInitValue
        /\ sleeperWrite4 = defaultInitValue
        /\ requestsRead = defaultInitValue
        /\ requestsWrite = defaultInitValue
        /\ myIdRead = defaultInitValue
        /\ dbRead = defaultInitValue
        /\ upstreamWrite = defaultInitValue
        /\ upstreamWrite0 = defaultInitValue
        /\ iAmTheLeaderRead1 = defaultInitValue
        /\ proposerChanWrite = defaultInitValue
        /\ paxosChanRead = defaultInitValue
        /\ proposerChanWrite0 = defaultInitValue
        /\ upstreamWrite1 = defaultInitValue
        /\ proposerChanWrite1 = defaultInitValue
        /\ upstreamWrite2 = defaultInitValue
        /\ requestsWrite0 = defaultInitValue
        /\ upstreamWrite3 = defaultInitValue
        /\ proposerChanWrite2 = defaultInitValue
        /\ learnerChanRead = defaultInitValue
        /\ kvIdRead = defaultInitValue
        /\ dbWrite = defaultInitValue
        /\ kvIdRead0 = defaultInitValue
        /\ kvIdRead1 = defaultInitValue
        /\ requestServiceWrite = defaultInitValue
        /\ requestServiceWrite0 = defaultInitValue
        /\ dbWrite0 = defaultInitValue
        /\ requestServiceWrite1 = defaultInitValue
        (* Process proposer *)
        /\ b = [self \in Proposer |-> defaultInitValue]
        /\ s = [self \in Proposer |-> 1]
        /\ elected = [self \in Proposer |-> FALSE]
        /\ acceptedValues_ = [self \in Proposer |-> <<>>]
        /\ max = [self \in Proposer |-> [slot |-> -(1), bal |-> -(1), val |-> -(1)]]
        /\ index_ = [self \in Proposer |-> defaultInitValue]
        /\ entry_ = [self \in Proposer |-> defaultInitValue]
        /\ promises = [self \in Proposer |-> defaultInitValue]
        /\ heartbeatMonitorId = [self \in Proposer |-> defaultInitValue]
        /\ accepts_ = [self \in Proposer |-> 0]
        /\ value = [self \in Proposer |-> defaultInitValue]
        /\ repropose = [self \in Proposer |-> defaultInitValue]
        /\ resp = [self \in Proposer |-> defaultInitValue]
        (* Process acceptor *)
        /\ maxBal = [self \in Acceptor |-> -(1)]
        /\ loopIndex = [self \in Acceptor |-> defaultInitValue]
        /\ acceptedValues = [self \in Acceptor |-> <<>>]
        /\ payload = [self \in Acceptor |-> defaultInitValue]
        /\ msg_ = [self \in Acceptor |-> defaultInitValue]
        (* Process learner *)
        /\ accepts = [self \in Learner |-> <<>>]
        /\ newAccepts = [self \in Learner |-> defaultInitValue]
        /\ numAccepted = [self \in Learner |-> defaultInitValue]
        /\ iterator = [self \in Learner |-> defaultInitValue]
        /\ entry = [self \in Learner |-> defaultInitValue]
        /\ msg_l = [self \in Learner |-> defaultInitValue]
        (* Process heartbeatAction *)
        /\ heartbeatFrequencyLocal = [self \in Heartbeat |-> 100]
        /\ msg_h = [self \in Heartbeat |-> defaultInitValue]
        /\ index = [self \in Heartbeat |-> defaultInitValue]
        (* Process leaderStatusMonitor *)
        /\ monitorFrequencyLocal = [self \in LeaderMonitor |-> 100]
        /\ heartbeatId_ = [self \in LeaderMonitor |-> defaultInitValue]
        (* Process kvRequests *)
        /\ msg = [self \in KVRequests |-> defaultInitValue]
        /\ null = [self \in KVRequests |-> defaultInitValue]
        /\ heartbeatId = [self \in KVRequests |-> defaultInitValue]
        /\ proposerId = [self \in KVRequests |-> defaultInitValue]
        /\ counter = [self \in KVRequests |-> 0]
        /\ requestId_ = [self \in KVRequests |-> defaultInitValue]
        /\ putOk = [self \in KVRequests |-> defaultInitValue]
        /\ confirmedRequestId = [self \in KVRequests |-> defaultInitValue]
        (* Process kvPaxosManager *)
        /\ learnerId = [self \in KVPaxosManager |-> defaultInitValue]
        /\ operation = [self \in KVPaxosManager |-> defaultInitValue]
        /\ requestId = [self \in KVPaxosManager |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposer -> "Pre"
                                        [] self \in Acceptor -> "A"
                                        [] self \in Learner -> "L"
                                        [] self \in Heartbeat -> "mainLoop"
                                        [] self \in LeaderMonitor -> "findId_"
                                        [] self \in KVRequests -> "kvInit"
                                        [] self \in KVPaxosManager -> "findId"]

Pre(self) == /\ pc[self] = "Pre"
             /\ b' = [b EXCEPT ![self] = self]
             /\ heartbeatMonitorId' = [heartbeatMonitorId EXCEPT ![self] = (self) + ((3) * (NUM_NODES))]
             /\ pc' = [pc EXCEPT ![self] = "P"]
             /\ UNCHANGED << network, values, lastSeenAbstract,
                             monitorLastSeen, timeoutCheckerAbstract,
                             sleeperAbstract, kvClient, idAbstract, requestSet,
                             learnedChan, paxosLayerChan, database,
                             electionInProgresssAbstract, iAmTheLeaderAbstract,
                             leaderFailureAbstract, valueStreamRead,
                             mailboxesWrite, mailboxesWrite0, mailboxesRead,
                             iAmTheLeaderWrite, electionInProgressWrite,
                             leaderFailureRead, iAmTheLeaderWrite0,
                             electionInProgressWrite0, iAmTheLeaderWrite1,
                             electionInProgressWrite1, mailboxesWrite1,
                             iAmTheLeaderWrite2, electionInProgressWrite2,
                             mailboxesWrite2, iAmTheLeaderWrite3,
                             electionInProgressWrite3, iAmTheLeaderWrite4,
                             electionInProgressWrite4, mailboxesWrite3,
                             electionInProgressWrite5, mailboxesWrite4,
                             iAmTheLeaderWrite5, electionInProgressWrite6,
                             mailboxesWrite5, mailboxesWrite6,
                             iAmTheLeaderWrite6, electionInProgressWrite7,
                             mailboxesWrite7, iAmTheLeaderWrite7,
                             electionInProgressWrite8, mailboxesWrite8,
                             iAmTheLeaderWrite8, electionInProgressWrite9,
                             mailboxesRead0, mailboxesWrite9, mailboxesWrite10,
                             mailboxesWrite11, mailboxesWrite12,
                             mailboxesWrite13, mailboxesWrite14,
                             mailboxesWrite15, mailboxesRead1,
                             mailboxesWrite16, decidedWrite, decidedWrite0,
                             decidedWrite1, decidedWrite2, mailboxesWrite17,
                             decidedWrite3, electionInProgressRead,
                             iAmTheLeaderRead, mailboxesWrite18,
                             mailboxesWrite19, heartbeatFrequencyRead,
                             sleeperWrite, mailboxesWrite20, sleeperWrite0,
                             mailboxesWrite21, sleeperWrite1, mailboxesRead2,
                             lastSeenWrite, mailboxesWrite22, lastSeenWrite0,
                             mailboxesWrite23, sleeperWrite2, lastSeenWrite1,
                             electionInProgressRead0, iAmTheLeaderRead0,
                             lastSeenRead, timeoutCheckerRead,
                             timeoutCheckerWrite, timeoutCheckerWrite0,
                             timeoutCheckerWrite1, leaderFailureWrite,
                             electionInProgressWrite10, leaderFailureWrite0,
                             electionInProgressWrite11, timeoutCheckerWrite2,
                             leaderFailureWrite1, electionInProgressWrite12,
                             monitorFrequencyRead, sleeperWrite3,
                             timeoutCheckerWrite3, leaderFailureWrite2,
                             electionInProgressWrite13, sleeperWrite4,
                             requestsRead, requestsWrite, myIdRead, dbRead,
                             upstreamWrite, upstreamWrite0, iAmTheLeaderRead1,
                             proposerChanWrite, paxosChanRead,
                             proposerChanWrite0, upstreamWrite1,
                             proposerChanWrite1, upstreamWrite2,
                             requestsWrite0, upstreamWrite3,
                             proposerChanWrite2, learnerChanRead, kvIdRead,
                             dbWrite, kvIdRead0, kvIdRead1,
                             requestServiceWrite, requestServiceWrite0,
                             dbWrite0, requestServiceWrite1, s, elected,
                             acceptedValues_, max, index_, entry_, promises,
                             accepts_, value, repropose, resp, maxBal,
                             loopIndex, acceptedValues, payload, msg_, accepts,
                             newAccepts, numAccepted, iterator, entry, msg_l,
                             heartbeatFrequencyLocal, msg_h, index,
                             monitorFrequencyLocal, heartbeatId_, msg, null,
                             heartbeatId, proposerId, counter, requestId_,
                             putOk, confirmedRequestId, learnerId, operation,
                             requestId >>

P(self) == /\ pc[self] = "P"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "PLeaderCheck"]
                      /\ UNCHANGED << network, electionInProgresssAbstract,
                                      iAmTheLeaderAbstract, mailboxesWrite8,
                                      iAmTheLeaderWrite8,
                                      electionInProgressWrite9 >>
                 ELSE /\ mailboxesWrite8' = network
                      /\ iAmTheLeaderWrite8' = iAmTheLeaderAbstract
                      /\ electionInProgressWrite9' = electionInProgresssAbstract
                      /\ network' = mailboxesWrite8'
                      /\ electionInProgresssAbstract' = electionInProgressWrite9'
                      /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite8'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                           timeoutCheckerAbstract, sleeperAbstract, kvClient,
                           idAbstract, requestSet, learnedChan, paxosLayerChan,
                           database, leaderFailureAbstract, valueStreamRead,
                           mailboxesWrite, mailboxesWrite0, mailboxesRead,
                           iAmTheLeaderWrite, electionInProgressWrite,
                           leaderFailureRead, iAmTheLeaderWrite0,
                           electionInProgressWrite0, iAmTheLeaderWrite1,
                           electionInProgressWrite1, mailboxesWrite1,
                           iAmTheLeaderWrite2, electionInProgressWrite2,
                           mailboxesWrite2, iAmTheLeaderWrite3,
                           electionInProgressWrite3, iAmTheLeaderWrite4,
                           electionInProgressWrite4, mailboxesWrite3,
                           electionInProgressWrite5, mailboxesWrite4,
                           iAmTheLeaderWrite5, electionInProgressWrite6,
                           mailboxesWrite5, mailboxesWrite6,
                           iAmTheLeaderWrite6, electionInProgressWrite7,
                           mailboxesWrite7, iAmTheLeaderWrite7,
                           electionInProgressWrite8, mailboxesRead0,
                           mailboxesWrite9, mailboxesWrite10, mailboxesWrite11,
                           mailboxesWrite12, mailboxesWrite13,
                           mailboxesWrite14, mailboxesWrite15, mailboxesRead1,
                           mailboxesWrite16, decidedWrite, decidedWrite0,
                           decidedWrite1, decidedWrite2, mailboxesWrite17,
                           decidedWrite3, electionInProgressRead,
                           iAmTheLeaderRead, mailboxesWrite18,
                           mailboxesWrite19, heartbeatFrequencyRead,
                           sleeperWrite, mailboxesWrite20, sleeperWrite0,
                           mailboxesWrite21, sleeperWrite1, mailboxesRead2,
                           lastSeenWrite, mailboxesWrite22, lastSeenWrite0,
                           mailboxesWrite23, sleeperWrite2, lastSeenWrite1,
                           electionInProgressRead0, iAmTheLeaderRead0,
                           lastSeenRead, timeoutCheckerRead,
                           timeoutCheckerWrite, timeoutCheckerWrite0,
                           timeoutCheckerWrite1, leaderFailureWrite,
                           electionInProgressWrite10, leaderFailureWrite0,
                           electionInProgressWrite11, timeoutCheckerWrite2,
                           leaderFailureWrite1, electionInProgressWrite12,
                           monitorFrequencyRead, sleeperWrite3,
                           timeoutCheckerWrite3, leaderFailureWrite2,
                           electionInProgressWrite13, sleeperWrite4,
                           requestsRead, requestsWrite, myIdRead, dbRead,
                           upstreamWrite, upstreamWrite0, iAmTheLeaderRead1,
                           proposerChanWrite, paxosChanRead,
                           proposerChanWrite0, upstreamWrite1,
                           proposerChanWrite1, upstreamWrite2, requestsWrite0,
                           upstreamWrite3, proposerChanWrite2, learnerChanRead,
                           kvIdRead, dbWrite, kvIdRead0, kvIdRead1,
                           requestServiceWrite, requestServiceWrite0, dbWrite0,
                           requestServiceWrite1, b, s, elected,
                           acceptedValues_, max, index_, entry_, promises,
                           heartbeatMonitorId, accepts_, value, repropose,
                           resp, maxBal, loopIndex, acceptedValues, payload,
                           msg_, accepts, newAccepts, numAccepted, iterator,
                           entry, msg_l, heartbeatFrequencyLocal, msg_h, index,
                           monitorFrequencyLocal, heartbeatId_, msg, null,
                           heartbeatId, proposerId, counter, requestId_, putOk,
                           confirmedRequestId, learnerId, operation, requestId >>

PLeaderCheck(self) == /\ pc[self] = "PLeaderCheck"
                      /\ IF elected[self]
                            THEN /\ accepts_' = [accepts_ EXCEPT ![self] = 0]
                                 /\ repropose' = [repropose EXCEPT ![self] = FALSE]
                                 /\ index_' = [index_ EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "PFindMaxVal"]
                            ELSE /\ index_' = [index_ EXCEPT ![self] = NUM_NODES]
                                 /\ pc' = [pc EXCEPT ![self] = "PReqVotes"]
                                 /\ UNCHANGED << accepts_, repropose >>
                      /\ UNCHANGED << network, values, lastSeenAbstract,
                                      monitorLastSeen, timeoutCheckerAbstract,
                                      sleeperAbstract, kvClient, idAbstract,
                                      requestSet, learnedChan, paxosLayerChan,
                                      database, electionInProgresssAbstract,
                                      iAmTheLeaderAbstract,
                                      leaderFailureAbstract, valueStreamRead,
                                      mailboxesWrite, mailboxesWrite0,
                                      mailboxesRead, iAmTheLeaderWrite,
                                      electionInProgressWrite,
                                      leaderFailureRead, iAmTheLeaderWrite0,
                                      electionInProgressWrite0,
                                      iAmTheLeaderWrite1,
                                      electionInProgressWrite1,
                                      mailboxesWrite1, iAmTheLeaderWrite2,
                                      electionInProgressWrite2,
                                      mailboxesWrite2, iAmTheLeaderWrite3,
                                      electionInProgressWrite3,
                                      iAmTheLeaderWrite4,
                                      electionInProgressWrite4,
                                      mailboxesWrite3,
                                      electionInProgressWrite5,
                                      mailboxesWrite4, iAmTheLeaderWrite5,
                                      electionInProgressWrite6,
                                      mailboxesWrite5, mailboxesWrite6,
                                      iAmTheLeaderWrite6,
                                      electionInProgressWrite7,
                                      mailboxesWrite7, iAmTheLeaderWrite7,
                                      electionInProgressWrite8,
                                      mailboxesWrite8, iAmTheLeaderWrite8,
                                      electionInProgressWrite9, mailboxesRead0,
                                      mailboxesWrite9, mailboxesWrite10,
                                      mailboxesWrite11, mailboxesWrite12,
                                      mailboxesWrite13, mailboxesWrite14,
                                      mailboxesWrite15, mailboxesRead1,
                                      mailboxesWrite16, decidedWrite,
                                      decidedWrite0, decidedWrite1,
                                      decidedWrite2, mailboxesWrite17,
                                      decidedWrite3, electionInProgressRead,
                                      iAmTheLeaderRead, mailboxesWrite18,
                                      mailboxesWrite19, heartbeatFrequencyRead,
                                      sleeperWrite, mailboxesWrite20,
                                      sleeperWrite0, mailboxesWrite21,
                                      sleeperWrite1, mailboxesRead2,
                                      lastSeenWrite, mailboxesWrite22,
                                      lastSeenWrite0, mailboxesWrite23,
                                      sleeperWrite2, lastSeenWrite1,
                                      electionInProgressRead0,
                                      iAmTheLeaderRead0, lastSeenRead,
                                      timeoutCheckerRead, timeoutCheckerWrite,
                                      timeoutCheckerWrite0,
                                      timeoutCheckerWrite1, leaderFailureWrite,
                                      electionInProgressWrite10,
                                      leaderFailureWrite0,
                                      electionInProgressWrite11,
                                      timeoutCheckerWrite2,
                                      leaderFailureWrite1,
                                      electionInProgressWrite12,
                                      monitorFrequencyRead, sleeperWrite3,
                                      timeoutCheckerWrite3,
                                      leaderFailureWrite2,
                                      electionInProgressWrite13, sleeperWrite4,
                                      requestsRead, requestsWrite, myIdRead,
                                      dbRead, upstreamWrite, upstreamWrite0,
                                      iAmTheLeaderRead1, proposerChanWrite,
                                      paxosChanRead, proposerChanWrite0,
                                      upstreamWrite1, proposerChanWrite1,
                                      upstreamWrite2, requestsWrite0,
                                      upstreamWrite3, proposerChanWrite2,
                                      learnerChanRead, kvIdRead, dbWrite,
                                      kvIdRead0, kvIdRead1,
                                      requestServiceWrite,
                                      requestServiceWrite0, dbWrite0,
                                      requestServiceWrite1, b, s, elected,
                                      acceptedValues_, max, entry_, promises,
                                      heartbeatMonitorId, value, resp, maxBal,
                                      loopIndex, acceptedValues, payload, msg_,
                                      accepts, newAccepts, numAccepted,
                                      iterator, entry, msg_l,
                                      heartbeatFrequencyLocal, msg_h, index,
                                      monitorFrequencyLocal, heartbeatId_, msg,
                                      null, heartbeatId, proposerId, counter,
                                      requestId_, putOk, confirmedRequestId,
                                      learnerId, operation, requestId >>

PFindMaxVal(self) == /\ pc[self] = "PFindMaxVal"
                     /\ IF (index_[self]) <= (Len(acceptedValues_[self]))
                           THEN /\ entry_' = [entry_ EXCEPT ![self] = acceptedValues_[self][index_[self]]]
                                /\ IF (((entry_'[self]).slot) = (s[self])) /\ (((entry_'[self]).bal) >= ((max[self]).bal))
                                      THEN /\ repropose' = [repropose EXCEPT ![self] = TRUE]
                                           /\ value' = [value EXCEPT ![self] = (entry_'[self]).val]
                                           /\ max' = [max EXCEPT ![self] = entry_'[self]]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << max, value,
                                                           repropose >>
                                /\ index_' = [index_ EXCEPT ![self] = (index_[self]) + (1)]
                                /\ pc' = [pc EXCEPT ![self] = "PFindMaxVal"]
                                /\ UNCHANGED << values, valueStreamRead >>
                           ELSE /\ IF ~(repropose[self])
                                      THEN /\ ((values[self]).value) # (NULL)
                                           /\ LET v0 == values[self] IN
                                                /\ values' = [values EXCEPT ![self].value = NULL]
                                                /\ valueStreamRead' = v0
                                           /\ value' = [value EXCEPT ![self] = valueStreamRead']
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << values,
                                                           valueStreamRead,
                                                           value >>
                                /\ index_' = [index_ EXCEPT ![self] = NUM_NODES]
                                /\ pc' = [pc EXCEPT ![self] = "PSendProposes"]
                                /\ UNCHANGED << max, entry_, repropose >>
                     /\ UNCHANGED << network, lastSeenAbstract,
                                     monitorLastSeen, timeoutCheckerAbstract,
                                     sleeperAbstract, kvClient, idAbstract,
                                     requestSet, learnedChan, paxosLayerChan,
                                     database, electionInProgresssAbstract,
                                     iAmTheLeaderAbstract,
                                     leaderFailureAbstract, mailboxesWrite,
                                     mailboxesWrite0, mailboxesRead,
                                     iAmTheLeaderWrite,
                                     electionInProgressWrite,
                                     leaderFailureRead, iAmTheLeaderWrite0,
                                     electionInProgressWrite0,
                                     iAmTheLeaderWrite1,
                                     electionInProgressWrite1, mailboxesWrite1,
                                     iAmTheLeaderWrite2,
                                     electionInProgressWrite2, mailboxesWrite2,
                                     iAmTheLeaderWrite3,
                                     electionInProgressWrite3,
                                     iAmTheLeaderWrite4,
                                     electionInProgressWrite4, mailboxesWrite3,
                                     electionInProgressWrite5, mailboxesWrite4,
                                     iAmTheLeaderWrite5,
                                     electionInProgressWrite6, mailboxesWrite5,
                                     mailboxesWrite6, iAmTheLeaderWrite6,
                                     electionInProgressWrite7, mailboxesWrite7,
                                     iAmTheLeaderWrite7,
                                     electionInProgressWrite8, mailboxesWrite8,
                                     iAmTheLeaderWrite8,
                                     electionInProgressWrite9, mailboxesRead0,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesWrite14,
                                     mailboxesWrite15, mailboxesRead1,
                                     mailboxesWrite16, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, mailboxesWrite17,
                                     decidedWrite3, electionInProgressRead,
                                     iAmTheLeaderRead, mailboxesWrite18,
                                     mailboxesWrite19, heartbeatFrequencyRead,
                                     sleeperWrite, mailboxesWrite20,
                                     sleeperWrite0, mailboxesWrite21,
                                     sleeperWrite1, mailboxesRead2,
                                     lastSeenWrite, mailboxesWrite22,
                                     lastSeenWrite0, mailboxesWrite23,
                                     sleeperWrite2, lastSeenWrite1,
                                     electionInProgressRead0,
                                     iAmTheLeaderRead0, lastSeenRead,
                                     timeoutCheckerRead, timeoutCheckerWrite,
                                     timeoutCheckerWrite0,
                                     timeoutCheckerWrite1, leaderFailureWrite,
                                     electionInProgressWrite10,
                                     leaderFailureWrite0,
                                     electionInProgressWrite11,
                                     timeoutCheckerWrite2, leaderFailureWrite1,
                                     electionInProgressWrite12,
                                     monitorFrequencyRead, sleeperWrite3,
                                     timeoutCheckerWrite3, leaderFailureWrite2,
                                     electionInProgressWrite13, sleeperWrite4,
                                     requestsRead, requestsWrite, myIdRead,
                                     dbRead, upstreamWrite, upstreamWrite0,
                                     iAmTheLeaderRead1, proposerChanWrite,
                                     paxosChanRead, proposerChanWrite0,
                                     upstreamWrite1, proposerChanWrite1,
                                     upstreamWrite2, requestsWrite0,
                                     upstreamWrite3, proposerChanWrite2,
                                     learnerChanRead, kvIdRead, dbWrite,
                                     kvIdRead0, kvIdRead1, requestServiceWrite,
                                     requestServiceWrite0, dbWrite0,
                                     requestServiceWrite1, b, s, elected,
                                     acceptedValues_, promises,
                                     heartbeatMonitorId, accepts_, resp,
                                     maxBal, loopIndex, acceptedValues,
                                     payload, msg_, accepts, newAccepts,
                                     numAccepted, iterator, entry, msg_l,
                                     heartbeatFrequencyLocal, msg_h, index,
                                     monitorFrequencyLocal, heartbeatId_, msg,
                                     null, heartbeatId, proposerId, counter,
                                     requestId_, putOk, confirmedRequestId,
                                     learnerId, operation, requestId >>

PSendProposes(self) == /\ pc[self] = "PSendProposes"
                       /\ IF (index_[self]) <= (((2) * (NUM_NODES)) - (1))
                             THEN /\ (Len(network[index_[self]])) < (BUFFER_SIZE)
                                  /\ mailboxesWrite' = [network EXCEPT ![index_[self]] = Append(network[index_[self]], [type |-> PROPOSE_MSG, bal |-> b[self], sender |-> self, slot |-> s[self], val |-> value[self]])]
                                  /\ index_' = [index_ EXCEPT ![self] = (index_[self]) + (1)]
                                  /\ mailboxesWrite0' = mailboxesWrite'
                                  /\ network' = mailboxesWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "PSendProposes"]
                             ELSE /\ mailboxesWrite0' = network
                                  /\ network' = mailboxesWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                  /\ UNCHANGED << mailboxesWrite, index_ >>
                       /\ UNCHANGED << values, lastSeenAbstract,
                                       monitorLastSeen, timeoutCheckerAbstract,
                                       sleeperAbstract, kvClient, idAbstract,
                                       requestSet, learnedChan, paxosLayerChan,
                                       database, electionInProgresssAbstract,
                                       iAmTheLeaderAbstract,
                                       leaderFailureAbstract, valueStreamRead,
                                       mailboxesRead, iAmTheLeaderWrite,
                                       electionInProgressWrite,
                                       leaderFailureRead, iAmTheLeaderWrite0,
                                       electionInProgressWrite0,
                                       iAmTheLeaderWrite1,
                                       electionInProgressWrite1,
                                       mailboxesWrite1, iAmTheLeaderWrite2,
                                       electionInProgressWrite2,
                                       mailboxesWrite2, iAmTheLeaderWrite3,
                                       electionInProgressWrite3,
                                       iAmTheLeaderWrite4,
                                       electionInProgressWrite4,
                                       mailboxesWrite3,
                                       electionInProgressWrite5,
                                       mailboxesWrite4, iAmTheLeaderWrite5,
                                       electionInProgressWrite6,
                                       mailboxesWrite5, mailboxesWrite6,
                                       iAmTheLeaderWrite6,
                                       electionInProgressWrite7,
                                       mailboxesWrite7, iAmTheLeaderWrite7,
                                       electionInProgressWrite8,
                                       mailboxesWrite8, iAmTheLeaderWrite8,
                                       electionInProgressWrite9,
                                       mailboxesRead0, mailboxesWrite9,
                                       mailboxesWrite10, mailboxesWrite11,
                                       mailboxesWrite12, mailboxesWrite13,
                                       mailboxesWrite14, mailboxesWrite15,
                                       mailboxesRead1, mailboxesWrite16,
                                       decidedWrite, decidedWrite0,
                                       decidedWrite1, decidedWrite2,
                                       mailboxesWrite17, decidedWrite3,
                                       electionInProgressRead,
                                       iAmTheLeaderRead, mailboxesWrite18,
                                       mailboxesWrite19,
                                       heartbeatFrequencyRead, sleeperWrite,
                                       mailboxesWrite20, sleeperWrite0,
                                       mailboxesWrite21, sleeperWrite1,
                                       mailboxesRead2, lastSeenWrite,
                                       mailboxesWrite22, lastSeenWrite0,
                                       mailboxesWrite23, sleeperWrite2,
                                       lastSeenWrite1, electionInProgressRead0,
                                       iAmTheLeaderRead0, lastSeenRead,
                                       timeoutCheckerRead, timeoutCheckerWrite,
                                       timeoutCheckerWrite0,
                                       timeoutCheckerWrite1,
                                       leaderFailureWrite,
                                       electionInProgressWrite10,
                                       leaderFailureWrite0,
                                       electionInProgressWrite11,
                                       timeoutCheckerWrite2,
                                       leaderFailureWrite1,
                                       electionInProgressWrite12,
                                       monitorFrequencyRead, sleeperWrite3,
                                       timeoutCheckerWrite3,
                                       leaderFailureWrite2,
                                       electionInProgressWrite13,
                                       sleeperWrite4, requestsRead,
                                       requestsWrite, myIdRead, dbRead,
                                       upstreamWrite, upstreamWrite0,
                                       iAmTheLeaderRead1, proposerChanWrite,
                                       paxosChanRead, proposerChanWrite0,
                                       upstreamWrite1, proposerChanWrite1,
                                       upstreamWrite2, requestsWrite0,
                                       upstreamWrite3, proposerChanWrite2,
                                       learnerChanRead, kvIdRead, dbWrite,
                                       kvIdRead0, kvIdRead1,
                                       requestServiceWrite,
                                       requestServiceWrite0, dbWrite0,
                                       requestServiceWrite1, b, s, elected,
                                       acceptedValues_, max, entry_, promises,
                                       heartbeatMonitorId, accepts_, value,
                                       repropose, resp, maxBal, loopIndex,
                                       acceptedValues, payload, msg_, accepts,
                                       newAccepts, numAccepted, iterator,
                                       entry, msg_l, heartbeatFrequencyLocal,
                                       msg_h, index, monitorFrequencyLocal,
                                       heartbeatId_, msg, null, heartbeatId,
                                       proposerId, counter, requestId_, putOk,
                                       confirmedRequestId, learnerId,
                                       operation, requestId >>

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
                                                      /\ iAmTheLeaderWrite1' = iAmTheLeaderAbstract
                                                      /\ electionInProgressWrite1' = electionInProgresssAbstract
                                                      /\ mailboxesWrite1' = mailboxesWrite'
                                                      /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                      /\ electionInProgressWrite2' = electionInProgressWrite1'
                                                      /\ network' = mailboxesWrite1'
                                                      /\ electionInProgresssAbstract' = electionInProgressWrite2'
                                                      /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite2'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                 ELSE /\ iAmTheLeaderWrite1' = iAmTheLeaderAbstract
                                                      /\ electionInProgressWrite1' = electionInProgresssAbstract
                                                      /\ mailboxesWrite1' = mailboxesWrite'
                                                      /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                      /\ electionInProgressWrite2' = electionInProgressWrite1'
                                                      /\ network' = mailboxesWrite1'
                                                      /\ electionInProgresssAbstract' = electionInProgressWrite2'
                                                      /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite2'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                      /\ UNCHANGED accepts_
                                           /\ UNCHANGED << iAmTheLeaderWrite,
                                                           electionInProgressWrite,
                                                           leaderFailureRead,
                                                           iAmTheLeaderWrite0,
                                                           electionInProgressWrite0,
                                                           elected >>
                                      ELSE /\ IF ((resp'[self]).type) = (REJECT_MSG)
                                                 THEN /\ elected' = [elected EXCEPT ![self] = FALSE]
                                                      /\ iAmTheLeaderWrite' = [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId[self]] = FALSE]
                                                      /\ electionInProgressWrite' = [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId[self]] = FALSE]
                                                      /\ (leaderFailureAbstract[heartbeatMonitorId[self]]) = (TRUE)
                                                      /\ leaderFailureRead' = leaderFailureAbstract[heartbeatMonitorId[self]]
                                                      /\ Assert((leaderFailureRead') = (TRUE),
                                                                "Failure of assertion at line 651, column 41.")
                                                      /\ iAmTheLeaderWrite0' = iAmTheLeaderWrite'
                                                      /\ electionInProgressWrite0' = electionInProgressWrite'
                                                      /\ iAmTheLeaderWrite1' = iAmTheLeaderWrite0'
                                                      /\ electionInProgressWrite1' = electionInProgressWrite0'
                                                      /\ mailboxesWrite1' = mailboxesWrite'
                                                      /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                      /\ electionInProgressWrite2' = electionInProgressWrite1'
                                                      /\ network' = mailboxesWrite1'
                                                      /\ electionInProgresssAbstract' = electionInProgressWrite2'
                                                      /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite2'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                 ELSE /\ iAmTheLeaderWrite0' = iAmTheLeaderAbstract
                                                      /\ electionInProgressWrite0' = electionInProgresssAbstract
                                                      /\ iAmTheLeaderWrite1' = iAmTheLeaderWrite0'
                                                      /\ electionInProgressWrite1' = electionInProgressWrite0'
                                                      /\ mailboxesWrite1' = mailboxesWrite'
                                                      /\ iAmTheLeaderWrite2' = iAmTheLeaderWrite1'
                                                      /\ electionInProgressWrite2' = electionInProgressWrite1'
                                                      /\ network' = mailboxesWrite1'
                                                      /\ electionInProgresssAbstract' = electionInProgressWrite2'
                                                      /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite2'
                                                      /\ pc' = [pc EXCEPT ![self] = "PSearchAccs"]
                                                      /\ UNCHANGED << iAmTheLeaderWrite,
                                                                      electionInProgressWrite,
                                                                      leaderFailureRead,
                                                                      elected >>
                                           /\ UNCHANGED accepts_
                           ELSE /\ mailboxesWrite1' = network
                                /\ iAmTheLeaderWrite2' = iAmTheLeaderAbstract
                                /\ electionInProgressWrite2' = electionInProgresssAbstract
                                /\ network' = mailboxesWrite1'
                                /\ electionInProgresssAbstract' = electionInProgressWrite2'
                                /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite2'
                                /\ pc' = [pc EXCEPT ![self] = "PIncSlot"]
                                /\ UNCHANGED << mailboxesWrite, mailboxesRead,
                                                iAmTheLeaderWrite,
                                                electionInProgressWrite,
                                                leaderFailureRead,
                                                iAmTheLeaderWrite0,
                                                electionInProgressWrite0,
                                                iAmTheLeaderWrite1,
                                                electionInProgressWrite1,
                                                elected, accepts_, resp >>
                     /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                     timeoutCheckerAbstract, sleeperAbstract,
                                     kvClient, idAbstract, requestSet,
                                     learnedChan, paxosLayerChan, database,
                                     leaderFailureAbstract, valueStreamRead,
                                     mailboxesWrite0, mailboxesWrite2,
                                     iAmTheLeaderWrite3,
                                     electionInProgressWrite3,
                                     iAmTheLeaderWrite4,
                                     electionInProgressWrite4, mailboxesWrite3,
                                     electionInProgressWrite5, mailboxesWrite4,
                                     iAmTheLeaderWrite5,
                                     electionInProgressWrite6, mailboxesWrite5,
                                     mailboxesWrite6, iAmTheLeaderWrite6,
                                     electionInProgressWrite7, mailboxesWrite7,
                                     iAmTheLeaderWrite7,
                                     electionInProgressWrite8, mailboxesWrite8,
                                     iAmTheLeaderWrite8,
                                     electionInProgressWrite9, mailboxesRead0,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesWrite14,
                                     mailboxesWrite15, mailboxesRead1,
                                     mailboxesWrite16, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, mailboxesWrite17,
                                     decidedWrite3, electionInProgressRead,
                                     iAmTheLeaderRead, mailboxesWrite18,
                                     mailboxesWrite19, heartbeatFrequencyRead,
                                     sleeperWrite, mailboxesWrite20,
                                     sleeperWrite0, mailboxesWrite21,
                                     sleeperWrite1, mailboxesRead2,
                                     lastSeenWrite, mailboxesWrite22,
                                     lastSeenWrite0, mailboxesWrite23,
                                     sleeperWrite2, lastSeenWrite1,
                                     electionInProgressRead0,
                                     iAmTheLeaderRead0, lastSeenRead,
                                     timeoutCheckerRead, timeoutCheckerWrite,
                                     timeoutCheckerWrite0,
                                     timeoutCheckerWrite1, leaderFailureWrite,
                                     electionInProgressWrite10,
                                     leaderFailureWrite0,
                                     electionInProgressWrite11,
                                     timeoutCheckerWrite2, leaderFailureWrite1,
                                     electionInProgressWrite12,
                                     monitorFrequencyRead, sleeperWrite3,
                                     timeoutCheckerWrite3, leaderFailureWrite2,
                                     electionInProgressWrite13, sleeperWrite4,
                                     requestsRead, requestsWrite, myIdRead,
                                     dbRead, upstreamWrite, upstreamWrite0,
                                     iAmTheLeaderRead1, proposerChanWrite,
                                     paxosChanRead, proposerChanWrite0,
                                     upstreamWrite1, proposerChanWrite1,
                                     upstreamWrite2, requestsWrite0,
                                     upstreamWrite3, proposerChanWrite2,
                                     learnerChanRead, kvIdRead, dbWrite,
                                     kvIdRead0, kvIdRead1, requestServiceWrite,
                                     requestServiceWrite0, dbWrite0,
                                     requestServiceWrite1, b, s,
                                     acceptedValues_, max, index_, entry_,
                                     promises, heartbeatMonitorId, value,
                                     repropose, maxBal, loopIndex,
                                     acceptedValues, payload, msg_, accepts,
                                     newAccepts, numAccepted, iterator, entry,
                                     msg_l, heartbeatFrequencyLocal, msg_h,
                                     index, monitorFrequencyLocal,
                                     heartbeatId_, msg, null, heartbeatId,
                                     proposerId, counter, requestId_, putOk,
                                     confirmedRequestId, learnerId, operation,
                                     requestId >>

PIncSlot(self) == /\ pc[self] = "PIncSlot"
                  /\ IF elected[self]
                        THEN /\ s' = [s EXCEPT ![self] = (s[self]) + (1)]
                             /\ pc' = [pc EXCEPT ![self] = "P"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "P"]
                             /\ s' = s
                  /\ UNCHANGED << network, values, lastSeenAbstract,
                                  monitorLastSeen, timeoutCheckerAbstract,
                                  sleeperAbstract, kvClient, idAbstract,
                                  requestSet, learnedChan, paxosLayerChan,
                                  database, electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesWrite14, mailboxesWrite15,
                                  mailboxesRead1, mailboxesWrite16,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, mailboxesWrite17,
                                  decidedWrite3, electionInProgressRead,
                                  iAmTheLeaderRead, mailboxesWrite18,
                                  mailboxesWrite19, heartbeatFrequencyRead,
                                  sleeperWrite, mailboxesWrite20,
                                  sleeperWrite0, mailboxesWrite21,
                                  sleeperWrite1, mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  mailboxesWrite23, sleeperWrite2,
                                  lastSeenWrite1, electionInProgressRead0,
                                  iAmTheLeaderRead0, lastSeenRead,
                                  timeoutCheckerRead, timeoutCheckerWrite,
                                  timeoutCheckerWrite0, timeoutCheckerWrite1,
                                  leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite, myIdRead,
                                  dbRead, upstreamWrite, upstreamWrite0,
                                  iAmTheLeaderRead1, proposerChanWrite,
                                  paxosChanRead, proposerChanWrite0,
                                  upstreamWrite1, proposerChanWrite1,
                                  upstreamWrite2, requestsWrite0,
                                  upstreamWrite3, proposerChanWrite2,
                                  learnerChanRead, kvIdRead, dbWrite,
                                  kvIdRead0, kvIdRead1, requestServiceWrite,
                                  requestServiceWrite0, dbWrite0,
                                  requestServiceWrite1, b, elected,
                                  acceptedValues_, max, index_, entry_,
                                  promises, heartbeatMonitorId, accepts_,
                                  value, repropose, resp, maxBal, loopIndex,
                                  acceptedValues, payload, msg_, accepts,
                                  newAccepts, numAccepted, iterator, entry,
                                  msg_l, heartbeatFrequencyLocal, msg_h, index,
                                  monitorFrequencyLocal, heartbeatId_, msg,
                                  null, heartbeatId, proposerId, counter,
                                  requestId_, putOk, confirmedRequestId,
                                  learnerId, operation, requestId >>

PReqVotes(self) == /\ pc[self] = "PReqVotes"
                   /\ IF (index_[self]) <= (((2) * (NUM_NODES)) - (1))
                         THEN /\ (Len(network[index_[self]])) < (BUFFER_SIZE)
                              /\ mailboxesWrite' = [network EXCEPT ![index_[self]] = Append(network[index_[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> NULL, val |-> NULL])]
                              /\ index_' = [index_ EXCEPT ![self] = (index_[self]) + (1)]
                              /\ mailboxesWrite2' = mailboxesWrite'
                              /\ iAmTheLeaderWrite3' = iAmTheLeaderAbstract
                              /\ electionInProgressWrite3' = electionInProgresssAbstract
                              /\ network' = mailboxesWrite2'
                              /\ electionInProgresssAbstract' = electionInProgressWrite3'
                              /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite3'
                              /\ pc' = [pc EXCEPT ![self] = "PReqVotes"]
                              /\ UNCHANGED << iAmTheLeaderWrite,
                                              electionInProgressWrite,
                                              promises >>
                         ELSE /\ promises' = [promises EXCEPT ![self] = 0]
                              /\ iAmTheLeaderWrite' = [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId[self]] = FALSE]
                              /\ electionInProgressWrite' = [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId[self]] = TRUE]
                              /\ mailboxesWrite2' = network
                              /\ iAmTheLeaderWrite3' = iAmTheLeaderWrite'
                              /\ electionInProgressWrite3' = electionInProgressWrite'
                              /\ network' = mailboxesWrite2'
                              /\ electionInProgresssAbstract' = electionInProgressWrite3'
                              /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite3'
                              /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                              /\ UNCHANGED << mailboxesWrite, index_ >>
                   /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                   timeoutCheckerAbstract, sleeperAbstract,
                                   kvClient, idAbstract, requestSet,
                                   learnedChan, paxosLayerChan, database,
                                   leaderFailureAbstract, valueStreamRead,
                                   mailboxesWrite0, mailboxesRead,
                                   leaderFailureRead, iAmTheLeaderWrite0,
                                   electionInProgressWrite0,
                                   iAmTheLeaderWrite1,
                                   electionInProgressWrite1, mailboxesWrite1,
                                   iAmTheLeaderWrite2,
                                   electionInProgressWrite2,
                                   iAmTheLeaderWrite4,
                                   electionInProgressWrite4, mailboxesWrite3,
                                   electionInProgressWrite5, mailboxesWrite4,
                                   iAmTheLeaderWrite5,
                                   electionInProgressWrite6, mailboxesWrite5,
                                   mailboxesWrite6, iAmTheLeaderWrite6,
                                   electionInProgressWrite7, mailboxesWrite7,
                                   iAmTheLeaderWrite7,
                                   electionInProgressWrite8, mailboxesWrite8,
                                   iAmTheLeaderWrite8,
                                   electionInProgressWrite9, mailboxesRead0,
                                   mailboxesWrite9, mailboxesWrite10,
                                   mailboxesWrite11, mailboxesWrite12,
                                   mailboxesWrite13, mailboxesWrite14,
                                   mailboxesWrite15, mailboxesRead1,
                                   mailboxesWrite16, decidedWrite,
                                   decidedWrite0, decidedWrite1, decidedWrite2,
                                   mailboxesWrite17, decidedWrite3,
                                   electionInProgressRead, iAmTheLeaderRead,
                                   mailboxesWrite18, mailboxesWrite19,
                                   heartbeatFrequencyRead, sleeperWrite,
                                   mailboxesWrite20, sleeperWrite0,
                                   mailboxesWrite21, sleeperWrite1,
                                   mailboxesRead2, lastSeenWrite,
                                   mailboxesWrite22, lastSeenWrite0,
                                   mailboxesWrite23, sleeperWrite2,
                                   lastSeenWrite1, electionInProgressRead0,
                                   iAmTheLeaderRead0, lastSeenRead,
                                   timeoutCheckerRead, timeoutCheckerWrite,
                                   timeoutCheckerWrite0, timeoutCheckerWrite1,
                                   leaderFailureWrite,
                                   electionInProgressWrite10,
                                   leaderFailureWrite0,
                                   electionInProgressWrite11,
                                   timeoutCheckerWrite2, leaderFailureWrite1,
                                   electionInProgressWrite12,
                                   monitorFrequencyRead, sleeperWrite3,
                                   timeoutCheckerWrite3, leaderFailureWrite2,
                                   electionInProgressWrite13, sleeperWrite4,
                                   requestsRead, requestsWrite, myIdRead,
                                   dbRead, upstreamWrite, upstreamWrite0,
                                   iAmTheLeaderRead1, proposerChanWrite,
                                   paxosChanRead, proposerChanWrite0,
                                   upstreamWrite1, proposerChanWrite1,
                                   upstreamWrite2, requestsWrite0,
                                   upstreamWrite3, proposerChanWrite2,
                                   learnerChanRead, kvIdRead, dbWrite,
                                   kvIdRead0, kvIdRead1, requestServiceWrite,
                                   requestServiceWrite0, dbWrite0,
                                   requestServiceWrite1, b, s, elected,
                                   acceptedValues_, max, entry_,
                                   heartbeatMonitorId, accepts_, value,
                                   repropose, resp, maxBal, loopIndex,
                                   acceptedValues, payload, msg_, accepts,
                                   newAccepts, numAccepted, iterator, entry,
                                   msg_l, heartbeatFrequencyLocal, msg_h,
                                   index, monitorFrequencyLocal, heartbeatId_,
                                   msg, null, heartbeatId, proposerId, counter,
                                   requestId_, putOk, confirmedRequestId,
                                   learnerId, operation, requestId >>

PCandidate(self) == /\ pc[self] = "PCandidate"
                    /\ IF ~(elected[self])
                          THEN /\ (Len(network[self])) > (0)
                               /\ LET msg1 == Head(network[self]) IN
                                    /\ mailboxesWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                    /\ mailboxesRead' = msg1
                               /\ resp' = [resp EXCEPT ![self] = mailboxesRead']
                               /\ IF (((resp'[self]).type) = (PROMISE_MSG)) /\ (((resp'[self]).bal) = (b[self]))
                                     THEN /\ acceptedValues_' = [acceptedValues_ EXCEPT ![self] = (acceptedValues_[self]) \o ((resp'[self]).accepted)]
                                          /\ promises' = [promises EXCEPT ![self] = (promises[self]) + (1)]
                                          /\ IF ((promises'[self]) * (2)) > (Cardinality(Acceptor))
                                                THEN /\ elected' = [elected EXCEPT ![self] = TRUE]
                                                     /\ iAmTheLeaderWrite' = [iAmTheLeaderAbstract EXCEPT ![heartbeatMonitorId[self]] = TRUE]
                                                     /\ electionInProgressWrite' = [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId[self]] = FALSE]
                                                     /\ iAmTheLeaderWrite4' = iAmTheLeaderWrite'
                                                     /\ electionInProgressWrite4' = electionInProgressWrite'
                                                     /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                     /\ electionInProgressWrite6' = electionInProgressWrite4'
                                                     /\ mailboxesWrite5' = network
                                                     /\ mailboxesWrite6' = mailboxesWrite5'
                                                     /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                     /\ electionInProgressWrite7' = electionInProgressWrite6'
                                                     /\ network' = mailboxesWrite6'
                                                     /\ electionInProgresssAbstract' = electionInProgressWrite7'
                                                     /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite6'
                                                     /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                                ELSE /\ iAmTheLeaderWrite4' = iAmTheLeaderAbstract
                                                     /\ electionInProgressWrite4' = electionInProgresssAbstract
                                                     /\ iAmTheLeaderWrite5' = iAmTheLeaderWrite4'
                                                     /\ electionInProgressWrite6' = electionInProgressWrite4'
                                                     /\ mailboxesWrite5' = network
                                                     /\ mailboxesWrite6' = mailboxesWrite5'
                                                     /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                     /\ electionInProgressWrite7' = electionInProgressWrite6'
                                                     /\ network' = mailboxesWrite6'
                                                     /\ electionInProgresssAbstract' = electionInProgressWrite7'
                                                     /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite6'
                                                     /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                                     /\ UNCHANGED << iAmTheLeaderWrite,
                                                                     electionInProgressWrite,
                                                                     elected >>
                                          /\ UNCHANGED << leaderFailureRead,
                                                          electionInProgressWrite5,
                                                          mailboxesWrite4, b,
                                                          index_ >>
                                     ELSE /\ IF (((resp'[self]).type) = (REJECT_MSG)) \/ (((resp'[self]).bal) > (b[self]))
                                                THEN /\ electionInProgressWrite' = [electionInProgresssAbstract EXCEPT ![heartbeatMonitorId[self]] = FALSE]
                                                     /\ (leaderFailureAbstract[heartbeatMonitorId[self]]) = (TRUE)
                                                     /\ leaderFailureRead' = leaderFailureAbstract[heartbeatMonitorId[self]]
                                                     /\ Assert((leaderFailureRead') = (TRUE),
                                                               "Failure of assertion at line 766, column 41.")
                                                     /\ b' = [b EXCEPT ![self] = (b[self]) + (NUM_NODES)]
                                                     /\ index_' = [index_ EXCEPT ![self] = NUM_NODES]
                                                     /\ network' = mailboxesWrite'
                                                     /\ electionInProgresssAbstract' = electionInProgressWrite'
                                                     /\ pc' = [pc EXCEPT ![self] = "PReSendReqVotes"]
                                                     /\ UNCHANGED << iAmTheLeaderAbstract,
                                                                     electionInProgressWrite5,
                                                                     mailboxesWrite4,
                                                                     iAmTheLeaderWrite5,
                                                                     electionInProgressWrite6,
                                                                     mailboxesWrite5,
                                                                     mailboxesWrite6,
                                                                     iAmTheLeaderWrite6,
                                                                     electionInProgressWrite7 >>
                                                ELSE /\ electionInProgressWrite5' = electionInProgresssAbstract
                                                     /\ mailboxesWrite4' = network
                                                     /\ iAmTheLeaderWrite5' = iAmTheLeaderAbstract
                                                     /\ electionInProgressWrite6' = electionInProgressWrite5'
                                                     /\ mailboxesWrite5' = mailboxesWrite4'
                                                     /\ mailboxesWrite6' = mailboxesWrite5'
                                                     /\ iAmTheLeaderWrite6' = iAmTheLeaderWrite5'
                                                     /\ electionInProgressWrite7' = electionInProgressWrite6'
                                                     /\ network' = mailboxesWrite6'
                                                     /\ electionInProgresssAbstract' = electionInProgressWrite7'
                                                     /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite6'
                                                     /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                                     /\ UNCHANGED << electionInProgressWrite,
                                                                     leaderFailureRead,
                                                                     b, index_ >>
                                          /\ UNCHANGED << iAmTheLeaderWrite,
                                                          iAmTheLeaderWrite4,
                                                          electionInProgressWrite4,
                                                          elected,
                                                          acceptedValues_,
                                                          promises >>
                          ELSE /\ mailboxesWrite6' = network
                               /\ iAmTheLeaderWrite6' = iAmTheLeaderAbstract
                               /\ electionInProgressWrite7' = electionInProgresssAbstract
                               /\ network' = mailboxesWrite6'
                               /\ electionInProgresssAbstract' = electionInProgressWrite7'
                               /\ iAmTheLeaderAbstract' = iAmTheLeaderWrite6'
                               /\ pc' = [pc EXCEPT ![self] = "P"]
                               /\ UNCHANGED << mailboxesWrite, mailboxesRead,
                                               iAmTheLeaderWrite,
                                               electionInProgressWrite,
                                               leaderFailureRead,
                                               iAmTheLeaderWrite4,
                                               electionInProgressWrite4,
                                               electionInProgressWrite5,
                                               mailboxesWrite4,
                                               iAmTheLeaderWrite5,
                                               electionInProgressWrite6,
                                               mailboxesWrite5, b, elected,
                                               acceptedValues_, index_,
                                               promises, resp >>
                    /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                    timeoutCheckerAbstract, sleeperAbstract,
                                    kvClient, idAbstract, requestSet,
                                    learnedChan, paxosLayerChan, database,
                                    leaderFailureAbstract, valueStreamRead,
                                    mailboxesWrite0, iAmTheLeaderWrite0,
                                    electionInProgressWrite0,
                                    iAmTheLeaderWrite1,
                                    electionInProgressWrite1, mailboxesWrite1,
                                    iAmTheLeaderWrite2,
                                    electionInProgressWrite2, mailboxesWrite2,
                                    iAmTheLeaderWrite3,
                                    electionInProgressWrite3, mailboxesWrite3,
                                    mailboxesWrite7, iAmTheLeaderWrite7,
                                    electionInProgressWrite8, mailboxesWrite8,
                                    iAmTheLeaderWrite8,
                                    electionInProgressWrite9, mailboxesRead0,
                                    mailboxesWrite9, mailboxesWrite10,
                                    mailboxesWrite11, mailboxesWrite12,
                                    mailboxesWrite13, mailboxesWrite14,
                                    mailboxesWrite15, mailboxesRead1,
                                    mailboxesWrite16, decidedWrite,
                                    decidedWrite0, decidedWrite1,
                                    decidedWrite2, mailboxesWrite17,
                                    decidedWrite3, electionInProgressRead,
                                    iAmTheLeaderRead, mailboxesWrite18,
                                    mailboxesWrite19, heartbeatFrequencyRead,
                                    sleeperWrite, mailboxesWrite20,
                                    sleeperWrite0, mailboxesWrite21,
                                    sleeperWrite1, mailboxesRead2,
                                    lastSeenWrite, mailboxesWrite22,
                                    lastSeenWrite0, mailboxesWrite23,
                                    sleeperWrite2, lastSeenWrite1,
                                    electionInProgressRead0, iAmTheLeaderRead0,
                                    lastSeenRead, timeoutCheckerRead,
                                    timeoutCheckerWrite, timeoutCheckerWrite0,
                                    timeoutCheckerWrite1, leaderFailureWrite,
                                    electionInProgressWrite10,
                                    leaderFailureWrite0,
                                    electionInProgressWrite11,
                                    timeoutCheckerWrite2, leaderFailureWrite1,
                                    electionInProgressWrite12,
                                    monitorFrequencyRead, sleeperWrite3,
                                    timeoutCheckerWrite3, leaderFailureWrite2,
                                    electionInProgressWrite13, sleeperWrite4,
                                    requestsRead, requestsWrite, myIdRead,
                                    dbRead, upstreamWrite, upstreamWrite0,
                                    iAmTheLeaderRead1, proposerChanWrite,
                                    paxosChanRead, proposerChanWrite0,
                                    upstreamWrite1, proposerChanWrite1,
                                    upstreamWrite2, requestsWrite0,
                                    upstreamWrite3, proposerChanWrite2,
                                    learnerChanRead, kvIdRead, dbWrite,
                                    kvIdRead0, kvIdRead1, requestServiceWrite,
                                    requestServiceWrite0, dbWrite0,
                                    requestServiceWrite1, s, max, entry_,
                                    heartbeatMonitorId, accepts_, value,
                                    repropose, maxBal, loopIndex,
                                    acceptedValues, payload, msg_, accepts,
                                    newAccepts, numAccepted, iterator, entry,
                                    msg_l, heartbeatFrequencyLocal, msg_h,
                                    index, monitorFrequencyLocal, heartbeatId_,
                                    msg, null, heartbeatId, proposerId,
                                    counter, requestId_, putOk,
                                    confirmedRequestId, learnerId, operation,
                                    requestId >>

PReSendReqVotes(self) == /\ pc[self] = "PReSendReqVotes"
                         /\ IF (index_[self]) <= (((2) * (NUM_NODES)) - (1))
                               THEN /\ (Len(network[index_[self]])) < (BUFFER_SIZE)
                                    /\ mailboxesWrite' = [network EXCEPT ![index_[self]] = Append(network[index_[self]], [type |-> PREPARE_MSG, bal |-> b[self], sender |-> self, slot |-> NULL, val |-> NULL])]
                                    /\ index_' = [index_ EXCEPT ![self] = (index_[self]) + (1)]
                                    /\ mailboxesWrite3' = mailboxesWrite'
                                    /\ network' = mailboxesWrite3'
                                    /\ pc' = [pc EXCEPT ![self] = "PReSendReqVotes"]
                               ELSE /\ mailboxesWrite3' = network
                                    /\ network' = mailboxesWrite3'
                                    /\ pc' = [pc EXCEPT ![self] = "PCandidate"]
                                    /\ UNCHANGED << mailboxesWrite, index_ >>
                         /\ UNCHANGED << values, lastSeenAbstract,
                                         monitorLastSeen,
                                         timeoutCheckerAbstract,
                                         sleeperAbstract, kvClient, idAbstract,
                                         requestSet, learnedChan,
                                         paxosLayerChan, database,
                                         electionInProgresssAbstract,
                                         iAmTheLeaderAbstract,
                                         leaderFailureAbstract,
                                         valueStreamRead, mailboxesWrite0,
                                         mailboxesRead, iAmTheLeaderWrite,
                                         electionInProgressWrite,
                                         leaderFailureRead, iAmTheLeaderWrite0,
                                         electionInProgressWrite0,
                                         iAmTheLeaderWrite1,
                                         electionInProgressWrite1,
                                         mailboxesWrite1, iAmTheLeaderWrite2,
                                         electionInProgressWrite2,
                                         mailboxesWrite2, iAmTheLeaderWrite3,
                                         electionInProgressWrite3,
                                         iAmTheLeaderWrite4,
                                         electionInProgressWrite4,
                                         electionInProgressWrite5,
                                         mailboxesWrite4, iAmTheLeaderWrite5,
                                         electionInProgressWrite6,
                                         mailboxesWrite5, mailboxesWrite6,
                                         iAmTheLeaderWrite6,
                                         electionInProgressWrite7,
                                         mailboxesWrite7, iAmTheLeaderWrite7,
                                         electionInProgressWrite8,
                                         mailboxesWrite8, iAmTheLeaderWrite8,
                                         electionInProgressWrite9,
                                         mailboxesRead0, mailboxesWrite9,
                                         mailboxesWrite10, mailboxesWrite11,
                                         mailboxesWrite12, mailboxesWrite13,
                                         mailboxesWrite14, mailboxesWrite15,
                                         mailboxesRead1, mailboxesWrite16,
                                         decidedWrite, decidedWrite0,
                                         decidedWrite1, decidedWrite2,
                                         mailboxesWrite17, decidedWrite3,
                                         electionInProgressRead,
                                         iAmTheLeaderRead, mailboxesWrite18,
                                         mailboxesWrite19,
                                         heartbeatFrequencyRead, sleeperWrite,
                                         mailboxesWrite20, sleeperWrite0,
                                         mailboxesWrite21, sleeperWrite1,
                                         mailboxesRead2, lastSeenWrite,
                                         mailboxesWrite22, lastSeenWrite0,
                                         mailboxesWrite23, sleeperWrite2,
                                         lastSeenWrite1,
                                         electionInProgressRead0,
                                         iAmTheLeaderRead0, lastSeenRead,
                                         timeoutCheckerRead,
                                         timeoutCheckerWrite,
                                         timeoutCheckerWrite0,
                                         timeoutCheckerWrite1,
                                         leaderFailureWrite,
                                         electionInProgressWrite10,
                                         leaderFailureWrite0,
                                         electionInProgressWrite11,
                                         timeoutCheckerWrite2,
                                         leaderFailureWrite1,
                                         electionInProgressWrite12,
                                         monitorFrequencyRead, sleeperWrite3,
                                         timeoutCheckerWrite3,
                                         leaderFailureWrite2,
                                         electionInProgressWrite13,
                                         sleeperWrite4, requestsRead,
                                         requestsWrite, myIdRead, dbRead,
                                         upstreamWrite, upstreamWrite0,
                                         iAmTheLeaderRead1, proposerChanWrite,
                                         paxosChanRead, proposerChanWrite0,
                                         upstreamWrite1, proposerChanWrite1,
                                         upstreamWrite2, requestsWrite0,
                                         upstreamWrite3, proposerChanWrite2,
                                         learnerChanRead, kvIdRead, dbWrite,
                                         kvIdRead0, kvIdRead1,
                                         requestServiceWrite,
                                         requestServiceWrite0, dbWrite0,
                                         requestServiceWrite1, b, s, elected,
                                         acceptedValues_, max, entry_,
                                         promises, heartbeatMonitorId,
                                         accepts_, value, repropose, resp,
                                         maxBal, loopIndex, acceptedValues,
                                         payload, msg_, accepts, newAccepts,
                                         numAccepted, iterator, entry, msg_l,
                                         heartbeatFrequencyLocal, msg_h, index,
                                         monitorFrequencyLocal, heartbeatId_,
                                         msg, null, heartbeatId, proposerId,
                                         counter, requestId_, putOk,
                                         confirmedRequestId, learnerId,
                                         operation, requestId >>

proposer(self) == Pre(self) \/ P(self) \/ PLeaderCheck(self)
                     \/ PFindMaxVal(self) \/ PSendProposes(self)
                     \/ PSearchAccs(self) \/ PIncSlot(self)
                     \/ PReqVotes(self) \/ PCandidate(self)
                     \/ PReSendReqVotes(self)

A(self) == /\ pc[self] = "A"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg2 == Head(network[self]) IN
                           /\ mailboxesWrite9' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead0' = msg2
                      /\ msg_' = [msg_ EXCEPT ![self] = mailboxesRead0']
                      /\ network' = mailboxesWrite9'
                      /\ pc' = [pc EXCEPT ![self] = "AMsgSwitch"]
                      /\ UNCHANGED mailboxesWrite15
                 ELSE /\ mailboxesWrite15' = network
                      /\ network' = mailboxesWrite15'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << mailboxesRead0, mailboxesWrite9, msg_ >>
           /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                           timeoutCheckerAbstract, sleeperAbstract, kvClient,
                           idAbstract, requestSet, learnedChan, paxosLayerChan,
                           database, electionInProgresssAbstract,
                           iAmTheLeaderAbstract, leaderFailureAbstract,
                           valueStreamRead, mailboxesWrite, mailboxesWrite0,
                           mailboxesRead, iAmTheLeaderWrite,
                           electionInProgressWrite, leaderFailureRead,
                           iAmTheLeaderWrite0, electionInProgressWrite0,
                           iAmTheLeaderWrite1, electionInProgressWrite1,
                           mailboxesWrite1, iAmTheLeaderWrite2,
                           electionInProgressWrite2, mailboxesWrite2,
                           iAmTheLeaderWrite3, electionInProgressWrite3,
                           iAmTheLeaderWrite4, electionInProgressWrite4,
                           mailboxesWrite3, electionInProgressWrite5,
                           mailboxesWrite4, iAmTheLeaderWrite5,
                           electionInProgressWrite6, mailboxesWrite5,
                           mailboxesWrite6, iAmTheLeaderWrite6,
                           electionInProgressWrite7, mailboxesWrite7,
                           iAmTheLeaderWrite7, electionInProgressWrite8,
                           mailboxesWrite8, iAmTheLeaderWrite8,
                           electionInProgressWrite9, mailboxesWrite10,
                           mailboxesWrite11, mailboxesWrite12,
                           mailboxesWrite13, mailboxesWrite14, mailboxesRead1,
                           mailboxesWrite16, decidedWrite, decidedWrite0,
                           decidedWrite1, decidedWrite2, mailboxesWrite17,
                           decidedWrite3, electionInProgressRead,
                           iAmTheLeaderRead, mailboxesWrite18,
                           mailboxesWrite19, heartbeatFrequencyRead,
                           sleeperWrite, mailboxesWrite20, sleeperWrite0,
                           mailboxesWrite21, sleeperWrite1, mailboxesRead2,
                           lastSeenWrite, mailboxesWrite22, lastSeenWrite0,
                           mailboxesWrite23, sleeperWrite2, lastSeenWrite1,
                           electionInProgressRead0, iAmTheLeaderRead0,
                           lastSeenRead, timeoutCheckerRead,
                           timeoutCheckerWrite, timeoutCheckerWrite0,
                           timeoutCheckerWrite1, leaderFailureWrite,
                           electionInProgressWrite10, leaderFailureWrite0,
                           electionInProgressWrite11, timeoutCheckerWrite2,
                           leaderFailureWrite1, electionInProgressWrite12,
                           monitorFrequencyRead, sleeperWrite3,
                           timeoutCheckerWrite3, leaderFailureWrite2,
                           electionInProgressWrite13, sleeperWrite4,
                           requestsRead, requestsWrite, myIdRead, dbRead,
                           upstreamWrite, upstreamWrite0, iAmTheLeaderRead1,
                           proposerChanWrite, paxosChanRead,
                           proposerChanWrite0, upstreamWrite1,
                           proposerChanWrite1, upstreamWrite2, requestsWrite0,
                           upstreamWrite3, proposerChanWrite2, learnerChanRead,
                           kvIdRead, dbWrite, kvIdRead0, kvIdRead1,
                           requestServiceWrite, requestServiceWrite0, dbWrite0,
                           requestServiceWrite1, b, s, elected,
                           acceptedValues_, max, index_, entry_, promises,
                           heartbeatMonitorId, accepts_, value, repropose,
                           resp, maxBal, loopIndex, acceptedValues, payload,
                           accepts, newAccepts, numAccepted, iterator, entry,
                           msg_l, heartbeatFrequencyLocal, msg_h, index,
                           monitorFrequencyLocal, heartbeatId_, msg, null,
                           heartbeatId, proposerId, counter, requestId_, putOk,
                           confirmedRequestId, learnerId, operation, requestId >>

AMsgSwitch(self) == /\ pc[self] = "AMsgSwitch"
                    /\ IF (((msg_[self]).type) = (PREPARE_MSG)) /\ (((msg_[self]).bal) > (maxBal[self]))
                          THEN /\ pc' = [pc EXCEPT ![self] = "APrepare"]
                               /\ UNCHANGED << network, mailboxesWrite11,
                                               mailboxesWrite12,
                                               mailboxesWrite13,
                                               mailboxesWrite14 >>
                          ELSE /\ IF (((msg_[self]).type) = (PREPARE_MSG)) /\ (((msg_[self]).bal) <= (maxBal[self]))
                                     THEN /\ pc' = [pc EXCEPT ![self] = "ABadPrepare"]
                                          /\ UNCHANGED << network,
                                                          mailboxesWrite11,
                                                          mailboxesWrite12,
                                                          mailboxesWrite13,
                                                          mailboxesWrite14 >>
                                     ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) >= (maxBal[self]))
                                                THEN /\ pc' = [pc EXCEPT ![self] = "APropose"]
                                                     /\ UNCHANGED << network,
                                                                     mailboxesWrite11,
                                                                     mailboxesWrite12,
                                                                     mailboxesWrite13,
                                                                     mailboxesWrite14 >>
                                                ELSE /\ IF (((msg_[self]).type) = (PROPOSE_MSG)) /\ (((msg_[self]).bal) < (maxBal[self]))
                                                           THEN /\ pc' = [pc EXCEPT ![self] = "ABadPropose"]
                                                                /\ UNCHANGED << network,
                                                                                mailboxesWrite11,
                                                                                mailboxesWrite12,
                                                                                mailboxesWrite13,
                                                                                mailboxesWrite14 >>
                                                           ELSE /\ mailboxesWrite11' = network
                                                                /\ mailboxesWrite12' = mailboxesWrite11'
                                                                /\ mailboxesWrite13' = mailboxesWrite12'
                                                                /\ mailboxesWrite14' = mailboxesWrite13'
                                                                /\ network' = mailboxesWrite14'
                                                                /\ pc' = [pc EXCEPT ![self] = "A"]
                    /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                    timeoutCheckerAbstract, sleeperAbstract,
                                    kvClient, idAbstract, requestSet,
                                    learnedChan, paxosLayerChan, database,
                                    electionInProgresssAbstract,
                                    iAmTheLeaderAbstract,
                                    leaderFailureAbstract, valueStreamRead,
                                    mailboxesWrite, mailboxesWrite0,
                                    mailboxesRead, iAmTheLeaderWrite,
                                    electionInProgressWrite, leaderFailureRead,
                                    iAmTheLeaderWrite0,
                                    electionInProgressWrite0,
                                    iAmTheLeaderWrite1,
                                    electionInProgressWrite1, mailboxesWrite1,
                                    iAmTheLeaderWrite2,
                                    electionInProgressWrite2, mailboxesWrite2,
                                    iAmTheLeaderWrite3,
                                    electionInProgressWrite3,
                                    iAmTheLeaderWrite4,
                                    electionInProgressWrite4, mailboxesWrite3,
                                    electionInProgressWrite5, mailboxesWrite4,
                                    iAmTheLeaderWrite5,
                                    electionInProgressWrite6, mailboxesWrite5,
                                    mailboxesWrite6, iAmTheLeaderWrite6,
                                    electionInProgressWrite7, mailboxesWrite7,
                                    iAmTheLeaderWrite7,
                                    electionInProgressWrite8, mailboxesWrite8,
                                    iAmTheLeaderWrite8,
                                    electionInProgressWrite9, mailboxesRead0,
                                    mailboxesWrite9, mailboxesWrite10,
                                    mailboxesWrite15, mailboxesRead1,
                                    mailboxesWrite16, decidedWrite,
                                    decidedWrite0, decidedWrite1,
                                    decidedWrite2, mailboxesWrite17,
                                    decidedWrite3, electionInProgressRead,
                                    iAmTheLeaderRead, mailboxesWrite18,
                                    mailboxesWrite19, heartbeatFrequencyRead,
                                    sleeperWrite, mailboxesWrite20,
                                    sleeperWrite0, mailboxesWrite21,
                                    sleeperWrite1, mailboxesRead2,
                                    lastSeenWrite, mailboxesWrite22,
                                    lastSeenWrite0, mailboxesWrite23,
                                    sleeperWrite2, lastSeenWrite1,
                                    electionInProgressRead0, iAmTheLeaderRead0,
                                    lastSeenRead, timeoutCheckerRead,
                                    timeoutCheckerWrite, timeoutCheckerWrite0,
                                    timeoutCheckerWrite1, leaderFailureWrite,
                                    electionInProgressWrite10,
                                    leaderFailureWrite0,
                                    electionInProgressWrite11,
                                    timeoutCheckerWrite2, leaderFailureWrite1,
                                    electionInProgressWrite12,
                                    monitorFrequencyRead, sleeperWrite3,
                                    timeoutCheckerWrite3, leaderFailureWrite2,
                                    electionInProgressWrite13, sleeperWrite4,
                                    requestsRead, requestsWrite, myIdRead,
                                    dbRead, upstreamWrite, upstreamWrite0,
                                    iAmTheLeaderRead1, proposerChanWrite,
                                    paxosChanRead, proposerChanWrite0,
                                    upstreamWrite1, proposerChanWrite1,
                                    upstreamWrite2, requestsWrite0,
                                    upstreamWrite3, proposerChanWrite2,
                                    learnerChanRead, kvIdRead, dbWrite,
                                    kvIdRead0, kvIdRead1, requestServiceWrite,
                                    requestServiceWrite0, dbWrite0,
                                    requestServiceWrite1, b, s, elected,
                                    acceptedValues_, max, index_, entry_,
                                    promises, heartbeatMonitorId, accepts_,
                                    value, repropose, resp, maxBal, loopIndex,
                                    acceptedValues, payload, msg_, accepts,
                                    newAccepts, numAccepted, iterator, entry,
                                    msg_l, heartbeatFrequencyLocal, msg_h,
                                    index, monitorFrequencyLocal, heartbeatId_,
                                    msg, null, heartbeatId, proposerId,
                                    counter, requestId_, putOk,
                                    confirmedRequestId, learnerId, operation,
                                    requestId >>

APrepare(self) == /\ pc[self] = "APrepare"
                  /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
                  /\ (Len(network[(msg_[self]).sender])) < (BUFFER_SIZE)
                  /\ mailboxesWrite9' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> PROMISE_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> NULL, val |-> NULL, accepted |-> acceptedValues[self]])]
                  /\ network' = mailboxesWrite9'
                  /\ pc' = [pc EXCEPT ![self] = "A"]
                  /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                  timeoutCheckerAbstract, sleeperAbstract,
                                  kvClient, idAbstract, requestSet,
                                  learnedChan, paxosLayerChan, database,
                                  electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite10,
                                  mailboxesWrite11, mailboxesWrite12,
                                  mailboxesWrite13, mailboxesWrite14,
                                  mailboxesWrite15, mailboxesRead1,
                                  mailboxesWrite16, decidedWrite,
                                  decidedWrite0, decidedWrite1, decidedWrite2,
                                  mailboxesWrite17, decidedWrite3,
                                  electionInProgressRead, iAmTheLeaderRead,
                                  mailboxesWrite18, mailboxesWrite19,
                                  heartbeatFrequencyRead, sleeperWrite,
                                  mailboxesWrite20, sleeperWrite0,
                                  mailboxesWrite21, sleeperWrite1,
                                  mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  mailboxesWrite23, sleeperWrite2,
                                  lastSeenWrite1, electionInProgressRead0,
                                  iAmTheLeaderRead0, lastSeenRead,
                                  timeoutCheckerRead, timeoutCheckerWrite,
                                  timeoutCheckerWrite0, timeoutCheckerWrite1,
                                  leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite, myIdRead,
                                  dbRead, upstreamWrite, upstreamWrite0,
                                  iAmTheLeaderRead1, proposerChanWrite,
                                  paxosChanRead, proposerChanWrite0,
                                  upstreamWrite1, proposerChanWrite1,
                                  upstreamWrite2, requestsWrite0,
                                  upstreamWrite3, proposerChanWrite2,
                                  learnerChanRead, kvIdRead, dbWrite,
                                  kvIdRead0, kvIdRead1, requestServiceWrite,
                                  requestServiceWrite0, dbWrite0,
                                  requestServiceWrite1, b, s, elected,
                                  acceptedValues_, max, index_, entry_,
                                  promises, heartbeatMonitorId, accepts_,
                                  value, repropose, resp, loopIndex,
                                  acceptedValues, payload, msg_, accepts,
                                  newAccepts, numAccepted, iterator, entry,
                                  msg_l, heartbeatFrequencyLocal, msg_h, index,
                                  monitorFrequencyLocal, heartbeatId_, msg,
                                  null, heartbeatId, proposerId, counter,
                                  requestId_, putOk, confirmedRequestId,
                                  learnerId, operation, requestId >>

ABadPrepare(self) == /\ pc[self] = "ABadPrepare"
                     /\ (Len(network[(msg_[self]).sender])) < (BUFFER_SIZE)
                     /\ mailboxesWrite9' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal[self], slot |-> NULL, val |-> NULL, accepted |-> <<>>])]
                     /\ network' = mailboxesWrite9'
                     /\ pc' = [pc EXCEPT ![self] = "A"]
                     /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                     timeoutCheckerAbstract, sleeperAbstract,
                                     kvClient, idAbstract, requestSet,
                                     learnedChan, paxosLayerChan, database,
                                     electionInProgresssAbstract,
                                     iAmTheLeaderAbstract,
                                     leaderFailureAbstract, valueStreamRead,
                                     mailboxesWrite, mailboxesWrite0,
                                     mailboxesRead, iAmTheLeaderWrite,
                                     electionInProgressWrite,
                                     leaderFailureRead, iAmTheLeaderWrite0,
                                     electionInProgressWrite0,
                                     iAmTheLeaderWrite1,
                                     electionInProgressWrite1, mailboxesWrite1,
                                     iAmTheLeaderWrite2,
                                     electionInProgressWrite2, mailboxesWrite2,
                                     iAmTheLeaderWrite3,
                                     electionInProgressWrite3,
                                     iAmTheLeaderWrite4,
                                     electionInProgressWrite4, mailboxesWrite3,
                                     electionInProgressWrite5, mailboxesWrite4,
                                     iAmTheLeaderWrite5,
                                     electionInProgressWrite6, mailboxesWrite5,
                                     mailboxesWrite6, iAmTheLeaderWrite6,
                                     electionInProgressWrite7, mailboxesWrite7,
                                     iAmTheLeaderWrite7,
                                     electionInProgressWrite8, mailboxesWrite8,
                                     iAmTheLeaderWrite8,
                                     electionInProgressWrite9, mailboxesRead0,
                                     mailboxesWrite10, mailboxesWrite11,
                                     mailboxesWrite12, mailboxesWrite13,
                                     mailboxesWrite14, mailboxesWrite15,
                                     mailboxesRead1, mailboxesWrite16,
                                     decidedWrite, decidedWrite0,
                                     decidedWrite1, decidedWrite2,
                                     mailboxesWrite17, decidedWrite3,
                                     electionInProgressRead, iAmTheLeaderRead,
                                     mailboxesWrite18, mailboxesWrite19,
                                     heartbeatFrequencyRead, sleeperWrite,
                                     mailboxesWrite20, sleeperWrite0,
                                     mailboxesWrite21, sleeperWrite1,
                                     mailboxesRead2, lastSeenWrite,
                                     mailboxesWrite22, lastSeenWrite0,
                                     mailboxesWrite23, sleeperWrite2,
                                     lastSeenWrite1, electionInProgressRead0,
                                     iAmTheLeaderRead0, lastSeenRead,
                                     timeoutCheckerRead, timeoutCheckerWrite,
                                     timeoutCheckerWrite0,
                                     timeoutCheckerWrite1, leaderFailureWrite,
                                     electionInProgressWrite10,
                                     leaderFailureWrite0,
                                     electionInProgressWrite11,
                                     timeoutCheckerWrite2, leaderFailureWrite1,
                                     electionInProgressWrite12,
                                     monitorFrequencyRead, sleeperWrite3,
                                     timeoutCheckerWrite3, leaderFailureWrite2,
                                     electionInProgressWrite13, sleeperWrite4,
                                     requestsRead, requestsWrite, myIdRead,
                                     dbRead, upstreamWrite, upstreamWrite0,
                                     iAmTheLeaderRead1, proposerChanWrite,
                                     paxosChanRead, proposerChanWrite0,
                                     upstreamWrite1, proposerChanWrite1,
                                     upstreamWrite2, requestsWrite0,
                                     upstreamWrite3, proposerChanWrite2,
                                     learnerChanRead, kvIdRead, dbWrite,
                                     kvIdRead0, kvIdRead1, requestServiceWrite,
                                     requestServiceWrite0, dbWrite0,
                                     requestServiceWrite1, b, s, elected,
                                     acceptedValues_, max, index_, entry_,
                                     promises, heartbeatMonitorId, accepts_,
                                     value, repropose, resp, maxBal, loopIndex,
                                     acceptedValues, payload, msg_, accepts,
                                     newAccepts, numAccepted, iterator, entry,
                                     msg_l, heartbeatFrequencyLocal, msg_h,
                                     index, monitorFrequencyLocal,
                                     heartbeatId_, msg, null, heartbeatId,
                                     proposerId, counter, requestId_, putOk,
                                     confirmedRequestId, learnerId, operation,
                                     requestId >>

APropose(self) == /\ pc[self] = "APropose"
                  /\ maxBal' = [maxBal EXCEPT ![self] = (msg_[self]).bal]
                  /\ payload' = [payload EXCEPT ![self] = [type |-> ACCEPT_MSG, sender |-> self, bal |-> maxBal'[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, accepted |-> <<>>]]
                  /\ acceptedValues' = [acceptedValues EXCEPT ![self] = Append(acceptedValues[self], [slot |-> (msg_[self]).slot, bal |-> (msg_[self]).bal, val |-> (msg_[self]).val])]
                  /\ (Len(network[(msg_[self]).sender])) < (BUFFER_SIZE)
                  /\ mailboxesWrite9' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], payload'[self])]
                  /\ loopIndex' = [loopIndex EXCEPT ![self] = (2) * (NUM_NODES)]
                  /\ network' = mailboxesWrite9'
                  /\ pc' = [pc EXCEPT ![self] = "ANotifyLearners"]
                  /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                  timeoutCheckerAbstract, sleeperAbstract,
                                  kvClient, idAbstract, requestSet,
                                  learnedChan, paxosLayerChan, database,
                                  electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite10,
                                  mailboxesWrite11, mailboxesWrite12,
                                  mailboxesWrite13, mailboxesWrite14,
                                  mailboxesWrite15, mailboxesRead1,
                                  mailboxesWrite16, decidedWrite,
                                  decidedWrite0, decidedWrite1, decidedWrite2,
                                  mailboxesWrite17, decidedWrite3,
                                  electionInProgressRead, iAmTheLeaderRead,
                                  mailboxesWrite18, mailboxesWrite19,
                                  heartbeatFrequencyRead, sleeperWrite,
                                  mailboxesWrite20, sleeperWrite0,
                                  mailboxesWrite21, sleeperWrite1,
                                  mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  mailboxesWrite23, sleeperWrite2,
                                  lastSeenWrite1, electionInProgressRead0,
                                  iAmTheLeaderRead0, lastSeenRead,
                                  timeoutCheckerRead, timeoutCheckerWrite,
                                  timeoutCheckerWrite0, timeoutCheckerWrite1,
                                  leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite, myIdRead,
                                  dbRead, upstreamWrite, upstreamWrite0,
                                  iAmTheLeaderRead1, proposerChanWrite,
                                  paxosChanRead, proposerChanWrite0,
                                  upstreamWrite1, proposerChanWrite1,
                                  upstreamWrite2, requestsWrite0,
                                  upstreamWrite3, proposerChanWrite2,
                                  learnerChanRead, kvIdRead, dbWrite,
                                  kvIdRead0, kvIdRead1, requestServiceWrite,
                                  requestServiceWrite0, dbWrite0,
                                  requestServiceWrite1, b, s, elected,
                                  acceptedValues_, max, index_, entry_,
                                  promises, heartbeatMonitorId, accepts_,
                                  value, repropose, resp, msg_, accepts,
                                  newAccepts, numAccepted, iterator, entry,
                                  msg_l, heartbeatFrequencyLocal, msg_h, index,
                                  monitorFrequencyLocal, heartbeatId_, msg,
                                  null, heartbeatId, proposerId, counter,
                                  requestId_, putOk, confirmedRequestId,
                                  learnerId, operation, requestId >>

ANotifyLearners(self) == /\ pc[self] = "ANotifyLearners"
                         /\ IF (loopIndex[self]) <= (((3) * (NUM_NODES)) - (1))
                               THEN /\ (Len(network[loopIndex[self]])) < (BUFFER_SIZE)
                                    /\ mailboxesWrite9' = [network EXCEPT ![loopIndex[self]] = Append(network[loopIndex[self]], payload[self])]
                                    /\ loopIndex' = [loopIndex EXCEPT ![self] = (loopIndex[self]) + (1)]
                                    /\ mailboxesWrite10' = mailboxesWrite9'
                                    /\ network' = mailboxesWrite10'
                                    /\ pc' = [pc EXCEPT ![self] = "ANotifyLearners"]
                               ELSE /\ mailboxesWrite10' = network
                                    /\ network' = mailboxesWrite10'
                                    /\ pc' = [pc EXCEPT ![self] = "A"]
                                    /\ UNCHANGED << mailboxesWrite9, loopIndex >>
                         /\ UNCHANGED << values, lastSeenAbstract,
                                         monitorLastSeen,
                                         timeoutCheckerAbstract,
                                         sleeperAbstract, kvClient, idAbstract,
                                         requestSet, learnedChan,
                                         paxosLayerChan, database,
                                         electionInProgresssAbstract,
                                         iAmTheLeaderAbstract,
                                         leaderFailureAbstract,
                                         valueStreamRead, mailboxesWrite,
                                         mailboxesWrite0, mailboxesRead,
                                         iAmTheLeaderWrite,
                                         electionInProgressWrite,
                                         leaderFailureRead, iAmTheLeaderWrite0,
                                         electionInProgressWrite0,
                                         iAmTheLeaderWrite1,
                                         electionInProgressWrite1,
                                         mailboxesWrite1, iAmTheLeaderWrite2,
                                         electionInProgressWrite2,
                                         mailboxesWrite2, iAmTheLeaderWrite3,
                                         electionInProgressWrite3,
                                         iAmTheLeaderWrite4,
                                         electionInProgressWrite4,
                                         mailboxesWrite3,
                                         electionInProgressWrite5,
                                         mailboxesWrite4, iAmTheLeaderWrite5,
                                         electionInProgressWrite6,
                                         mailboxesWrite5, mailboxesWrite6,
                                         iAmTheLeaderWrite6,
                                         electionInProgressWrite7,
                                         mailboxesWrite7, iAmTheLeaderWrite7,
                                         electionInProgressWrite8,
                                         mailboxesWrite8, iAmTheLeaderWrite8,
                                         electionInProgressWrite9,
                                         mailboxesRead0, mailboxesWrite11,
                                         mailboxesWrite12, mailboxesWrite13,
                                         mailboxesWrite14, mailboxesWrite15,
                                         mailboxesRead1, mailboxesWrite16,
                                         decidedWrite, decidedWrite0,
                                         decidedWrite1, decidedWrite2,
                                         mailboxesWrite17, decidedWrite3,
                                         electionInProgressRead,
                                         iAmTheLeaderRead, mailboxesWrite18,
                                         mailboxesWrite19,
                                         heartbeatFrequencyRead, sleeperWrite,
                                         mailboxesWrite20, sleeperWrite0,
                                         mailboxesWrite21, sleeperWrite1,
                                         mailboxesRead2, lastSeenWrite,
                                         mailboxesWrite22, lastSeenWrite0,
                                         mailboxesWrite23, sleeperWrite2,
                                         lastSeenWrite1,
                                         electionInProgressRead0,
                                         iAmTheLeaderRead0, lastSeenRead,
                                         timeoutCheckerRead,
                                         timeoutCheckerWrite,
                                         timeoutCheckerWrite0,
                                         timeoutCheckerWrite1,
                                         leaderFailureWrite,
                                         electionInProgressWrite10,
                                         leaderFailureWrite0,
                                         electionInProgressWrite11,
                                         timeoutCheckerWrite2,
                                         leaderFailureWrite1,
                                         electionInProgressWrite12,
                                         monitorFrequencyRead, sleeperWrite3,
                                         timeoutCheckerWrite3,
                                         leaderFailureWrite2,
                                         electionInProgressWrite13,
                                         sleeperWrite4, requestsRead,
                                         requestsWrite, myIdRead, dbRead,
                                         upstreamWrite, upstreamWrite0,
                                         iAmTheLeaderRead1, proposerChanWrite,
                                         paxosChanRead, proposerChanWrite0,
                                         upstreamWrite1, proposerChanWrite1,
                                         upstreamWrite2, requestsWrite0,
                                         upstreamWrite3, proposerChanWrite2,
                                         learnerChanRead, kvIdRead, dbWrite,
                                         kvIdRead0, kvIdRead1,
                                         requestServiceWrite,
                                         requestServiceWrite0, dbWrite0,
                                         requestServiceWrite1, b, s, elected,
                                         acceptedValues_, max, index_, entry_,
                                         promises, heartbeatMonitorId,
                                         accepts_, value, repropose, resp,
                                         maxBal, acceptedValues, payload, msg_,
                                         accepts, newAccepts, numAccepted,
                                         iterator, entry, msg_l,
                                         heartbeatFrequencyLocal, msg_h, index,
                                         monitorFrequencyLocal, heartbeatId_,
                                         msg, null, heartbeatId, proposerId,
                                         counter, requestId_, putOk,
                                         confirmedRequestId, learnerId,
                                         operation, requestId >>

ABadPropose(self) == /\ pc[self] = "ABadPropose"
                     /\ (Len(network[(msg_[self]).sender])) < (BUFFER_SIZE)
                     /\ mailboxesWrite9' = [network EXCEPT ![(msg_[self]).sender] = Append(network[(msg_[self]).sender], [type |-> REJECT_MSG, sender |-> self, bal |-> maxBal[self], slot |-> (msg_[self]).slot, val |-> (msg_[self]).val, accepted |-> <<>>])]
                     /\ network' = mailboxesWrite9'
                     /\ pc' = [pc EXCEPT ![self] = "A"]
                     /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                     timeoutCheckerAbstract, sleeperAbstract,
                                     kvClient, idAbstract, requestSet,
                                     learnedChan, paxosLayerChan, database,
                                     electionInProgresssAbstract,
                                     iAmTheLeaderAbstract,
                                     leaderFailureAbstract, valueStreamRead,
                                     mailboxesWrite, mailboxesWrite0,
                                     mailboxesRead, iAmTheLeaderWrite,
                                     electionInProgressWrite,
                                     leaderFailureRead, iAmTheLeaderWrite0,
                                     electionInProgressWrite0,
                                     iAmTheLeaderWrite1,
                                     electionInProgressWrite1, mailboxesWrite1,
                                     iAmTheLeaderWrite2,
                                     electionInProgressWrite2, mailboxesWrite2,
                                     iAmTheLeaderWrite3,
                                     electionInProgressWrite3,
                                     iAmTheLeaderWrite4,
                                     electionInProgressWrite4, mailboxesWrite3,
                                     electionInProgressWrite5, mailboxesWrite4,
                                     iAmTheLeaderWrite5,
                                     electionInProgressWrite6, mailboxesWrite5,
                                     mailboxesWrite6, iAmTheLeaderWrite6,
                                     electionInProgressWrite7, mailboxesWrite7,
                                     iAmTheLeaderWrite7,
                                     electionInProgressWrite8, mailboxesWrite8,
                                     iAmTheLeaderWrite8,
                                     electionInProgressWrite9, mailboxesRead0,
                                     mailboxesWrite10, mailboxesWrite11,
                                     mailboxesWrite12, mailboxesWrite13,
                                     mailboxesWrite14, mailboxesWrite15,
                                     mailboxesRead1, mailboxesWrite16,
                                     decidedWrite, decidedWrite0,
                                     decidedWrite1, decidedWrite2,
                                     mailboxesWrite17, decidedWrite3,
                                     electionInProgressRead, iAmTheLeaderRead,
                                     mailboxesWrite18, mailboxesWrite19,
                                     heartbeatFrequencyRead, sleeperWrite,
                                     mailboxesWrite20, sleeperWrite0,
                                     mailboxesWrite21, sleeperWrite1,
                                     mailboxesRead2, lastSeenWrite,
                                     mailboxesWrite22, lastSeenWrite0,
                                     mailboxesWrite23, sleeperWrite2,
                                     lastSeenWrite1, electionInProgressRead0,
                                     iAmTheLeaderRead0, lastSeenRead,
                                     timeoutCheckerRead, timeoutCheckerWrite,
                                     timeoutCheckerWrite0,
                                     timeoutCheckerWrite1, leaderFailureWrite,
                                     electionInProgressWrite10,
                                     leaderFailureWrite0,
                                     electionInProgressWrite11,
                                     timeoutCheckerWrite2, leaderFailureWrite1,
                                     electionInProgressWrite12,
                                     monitorFrequencyRead, sleeperWrite3,
                                     timeoutCheckerWrite3, leaderFailureWrite2,
                                     electionInProgressWrite13, sleeperWrite4,
                                     requestsRead, requestsWrite, myIdRead,
                                     dbRead, upstreamWrite, upstreamWrite0,
                                     iAmTheLeaderRead1, proposerChanWrite,
                                     paxosChanRead, proposerChanWrite0,
                                     upstreamWrite1, proposerChanWrite1,
                                     upstreamWrite2, requestsWrite0,
                                     upstreamWrite3, proposerChanWrite2,
                                     learnerChanRead, kvIdRead, dbWrite,
                                     kvIdRead0, kvIdRead1, requestServiceWrite,
                                     requestServiceWrite0, dbWrite0,
                                     requestServiceWrite1, b, s, elected,
                                     acceptedValues_, max, index_, entry_,
                                     promises, heartbeatMonitorId, accepts_,
                                     value, repropose, resp, maxBal, loopIndex,
                                     acceptedValues, payload, msg_, accepts,
                                     newAccepts, numAccepted, iterator, entry,
                                     msg_l, heartbeatFrequencyLocal, msg_h,
                                     index, monitorFrequencyLocal,
                                     heartbeatId_, msg, null, heartbeatId,
                                     proposerId, counter, requestId_, putOk,
                                     confirmedRequestId, learnerId, operation,
                                     requestId >>

acceptor(self) == A(self) \/ AMsgSwitch(self) \/ APrepare(self)
                     \/ ABadPrepare(self) \/ APropose(self)
                     \/ ANotifyLearners(self) \/ ABadPropose(self)

L(self) == /\ pc[self] = "L"
           /\ IF TRUE
                 THEN /\ (Len(network[self])) > (0)
                      /\ LET msg3 == Head(network[self]) IN
                           /\ mailboxesWrite16' = [network EXCEPT ![self] = Tail(network[self])]
                           /\ mailboxesRead1' = msg3
                      /\ msg_l' = [msg_l EXCEPT ![self] = mailboxesRead1']
                      /\ network' = mailboxesWrite16'
                      /\ pc' = [pc EXCEPT ![self] = "LGotAcc"]
                      /\ UNCHANGED << learnedChan, mailboxesWrite17,
                                      decidedWrite3 >>
                 ELSE /\ mailboxesWrite17' = network
                      /\ decidedWrite3' = learnedChan
                      /\ network' = mailboxesWrite17'
                      /\ learnedChan' = decidedWrite3'
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << mailboxesRead1, mailboxesWrite16, msg_l >>
           /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                           timeoutCheckerAbstract, sleeperAbstract, kvClient,
                           idAbstract, requestSet, paxosLayerChan, database,
                           electionInProgresssAbstract, iAmTheLeaderAbstract,
                           leaderFailureAbstract, valueStreamRead,
                           mailboxesWrite, mailboxesWrite0, mailboxesRead,
                           iAmTheLeaderWrite, electionInProgressWrite,
                           leaderFailureRead, iAmTheLeaderWrite0,
                           electionInProgressWrite0, iAmTheLeaderWrite1,
                           electionInProgressWrite1, mailboxesWrite1,
                           iAmTheLeaderWrite2, electionInProgressWrite2,
                           mailboxesWrite2, iAmTheLeaderWrite3,
                           electionInProgressWrite3, iAmTheLeaderWrite4,
                           electionInProgressWrite4, mailboxesWrite3,
                           electionInProgressWrite5, mailboxesWrite4,
                           iAmTheLeaderWrite5, electionInProgressWrite6,
                           mailboxesWrite5, mailboxesWrite6,
                           iAmTheLeaderWrite6, electionInProgressWrite7,
                           mailboxesWrite7, iAmTheLeaderWrite7,
                           electionInProgressWrite8, mailboxesWrite8,
                           iAmTheLeaderWrite8, electionInProgressWrite9,
                           mailboxesRead0, mailboxesWrite9, mailboxesWrite10,
                           mailboxesWrite11, mailboxesWrite12,
                           mailboxesWrite13, mailboxesWrite14,
                           mailboxesWrite15, decidedWrite, decidedWrite0,
                           decidedWrite1, decidedWrite2,
                           electionInProgressRead, iAmTheLeaderRead,
                           mailboxesWrite18, mailboxesWrite19,
                           heartbeatFrequencyRead, sleeperWrite,
                           mailboxesWrite20, sleeperWrite0, mailboxesWrite21,
                           sleeperWrite1, mailboxesRead2, lastSeenWrite,
                           mailboxesWrite22, lastSeenWrite0, mailboxesWrite23,
                           sleeperWrite2, lastSeenWrite1,
                           electionInProgressRead0, iAmTheLeaderRead0,
                           lastSeenRead, timeoutCheckerRead,
                           timeoutCheckerWrite, timeoutCheckerWrite0,
                           timeoutCheckerWrite1, leaderFailureWrite,
                           electionInProgressWrite10, leaderFailureWrite0,
                           electionInProgressWrite11, timeoutCheckerWrite2,
                           leaderFailureWrite1, electionInProgressWrite12,
                           monitorFrequencyRead, sleeperWrite3,
                           timeoutCheckerWrite3, leaderFailureWrite2,
                           electionInProgressWrite13, sleeperWrite4,
                           requestsRead, requestsWrite, myIdRead, dbRead,
                           upstreamWrite, upstreamWrite0, iAmTheLeaderRead1,
                           proposerChanWrite, paxosChanRead,
                           proposerChanWrite0, upstreamWrite1,
                           proposerChanWrite1, upstreamWrite2, requestsWrite0,
                           upstreamWrite3, proposerChanWrite2, learnerChanRead,
                           kvIdRead, dbWrite, kvIdRead0, kvIdRead1,
                           requestServiceWrite, requestServiceWrite0, dbWrite0,
                           requestServiceWrite1, b, s, elected,
                           acceptedValues_, max, index_, entry_, promises,
                           heartbeatMonitorId, accepts_, value, repropose,
                           resp, maxBal, loopIndex, acceptedValues, payload,
                           msg_, accepts, newAccepts, numAccepted, iterator,
                           entry, heartbeatFrequencyLocal, msg_h, index,
                           monitorFrequencyLocal, heartbeatId_, msg, null,
                           heartbeatId, proposerId, counter, requestId_, putOk,
                           confirmedRequestId, learnerId, operation, requestId >>

LGotAcc(self) == /\ pc[self] = "LGotAcc"
                 /\ IF ((msg_l[self]).type) = (ACCEPT_MSG)
                       THEN /\ accepts' = [accepts EXCEPT ![self] = Append(accepts[self], msg_l[self])]
                            /\ iterator' = [iterator EXCEPT ![self] = 1]
                            /\ numAccepted' = [numAccepted EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "LCheckMajority"]
                            /\ UNCHANGED << learnedChan, decidedWrite2 >>
                       ELSE /\ decidedWrite2' = learnedChan
                            /\ learnedChan' = decidedWrite2'
                            /\ pc' = [pc EXCEPT ![self] = "L"]
                            /\ UNCHANGED << accepts, numAccepted, iterator >>
                 /\ UNCHANGED << network, values, lastSeenAbstract,
                                 monitorLastSeen, timeoutCheckerAbstract,
                                 sleeperAbstract, kvClient, idAbstract,
                                 requestSet, paxosLayerChan, database,
                                 electionInProgresssAbstract,
                                 iAmTheLeaderAbstract, leaderFailureAbstract,
                                 valueStreamRead, mailboxesWrite,
                                 mailboxesWrite0, mailboxesRead,
                                 iAmTheLeaderWrite, electionInProgressWrite,
                                 leaderFailureRead, iAmTheLeaderWrite0,
                                 electionInProgressWrite0, iAmTheLeaderWrite1,
                                 electionInProgressWrite1, mailboxesWrite1,
                                 iAmTheLeaderWrite2, electionInProgressWrite2,
                                 mailboxesWrite2, iAmTheLeaderWrite3,
                                 electionInProgressWrite3, iAmTheLeaderWrite4,
                                 electionInProgressWrite4, mailboxesWrite3,
                                 electionInProgressWrite5, mailboxesWrite4,
                                 iAmTheLeaderWrite5, electionInProgressWrite6,
                                 mailboxesWrite5, mailboxesWrite6,
                                 iAmTheLeaderWrite6, electionInProgressWrite7,
                                 mailboxesWrite7, iAmTheLeaderWrite7,
                                 electionInProgressWrite8, mailboxesWrite8,
                                 iAmTheLeaderWrite8, electionInProgressWrite9,
                                 mailboxesRead0, mailboxesWrite9,
                                 mailboxesWrite10, mailboxesWrite11,
                                 mailboxesWrite12, mailboxesWrite13,
                                 mailboxesWrite14, mailboxesWrite15,
                                 mailboxesRead1, mailboxesWrite16,
                                 decidedWrite, decidedWrite0, decidedWrite1,
                                 mailboxesWrite17, decidedWrite3,
                                 electionInProgressRead, iAmTheLeaderRead,
                                 mailboxesWrite18, mailboxesWrite19,
                                 heartbeatFrequencyRead, sleeperWrite,
                                 mailboxesWrite20, sleeperWrite0,
                                 mailboxesWrite21, sleeperWrite1,
                                 mailboxesRead2, lastSeenWrite,
                                 mailboxesWrite22, lastSeenWrite0,
                                 mailboxesWrite23, sleeperWrite2,
                                 lastSeenWrite1, electionInProgressRead0,
                                 iAmTheLeaderRead0, lastSeenRead,
                                 timeoutCheckerRead, timeoutCheckerWrite,
                                 timeoutCheckerWrite0, timeoutCheckerWrite1,
                                 leaderFailureWrite, electionInProgressWrite10,
                                 leaderFailureWrite0,
                                 electionInProgressWrite11,
                                 timeoutCheckerWrite2, leaderFailureWrite1,
                                 electionInProgressWrite12,
                                 monitorFrequencyRead, sleeperWrite3,
                                 timeoutCheckerWrite3, leaderFailureWrite2,
                                 electionInProgressWrite13, sleeperWrite4,
                                 requestsRead, requestsWrite, myIdRead, dbRead,
                                 upstreamWrite, upstreamWrite0,
                                 iAmTheLeaderRead1, proposerChanWrite,
                                 paxosChanRead, proposerChanWrite0,
                                 upstreamWrite1, proposerChanWrite1,
                                 upstreamWrite2, requestsWrite0,
                                 upstreamWrite3, proposerChanWrite2,
                                 learnerChanRead, kvIdRead, dbWrite, kvIdRead0,
                                 kvIdRead1, requestServiceWrite,
                                 requestServiceWrite0, dbWrite0,
                                 requestServiceWrite1, b, s, elected,
                                 acceptedValues_, max, index_, entry_,
                                 promises, heartbeatMonitorId, accepts_, value,
                                 repropose, resp, maxBal, loopIndex,
                                 acceptedValues, payload, msg_, newAccepts,
                                 entry, msg_l, heartbeatFrequencyLocal, msg_h,
                                 index, monitorFrequencyLocal, heartbeatId_,
                                 msg, null, heartbeatId, proposerId, counter,
                                 requestId_, putOk, confirmedRequestId,
                                 learnerId, operation, requestId >>

LCheckMajority(self) == /\ pc[self] = "LCheckMajority"
                        /\ IF (iterator[self]) <= (Len(accepts[self]))
                              THEN /\ entry' = [entry EXCEPT ![self] = accepts[self][iterator[self]]]
                                   /\ IF ((((entry'[self]).slot) = ((msg_l[self]).slot)) /\ (((entry'[self]).bal) = ((msg_l[self]).bal))) /\ (((entry'[self]).val) = ((msg_l[self]).val))
                                         THEN /\ numAccepted' = [numAccepted EXCEPT ![self] = (numAccepted[self]) + (1)]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED numAccepted
                                   /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                   /\ decidedWrite1' = learnedChan
                                   /\ learnedChan' = decidedWrite1'
                                   /\ pc' = [pc EXCEPT ![self] = "LCheckMajority"]
                                   /\ UNCHANGED << decidedWrite, decidedWrite0,
                                                   newAccepts >>
                              ELSE /\ IF ((numAccepted[self]) * (2)) > (Cardinality(Acceptor))
                                         THEN /\ ((learnedChan[self]).value) = (NULL)
                                              /\ decidedWrite' = [learnedChan EXCEPT ![self] = (msg_l[self]).val]
                                              /\ newAccepts' = [newAccepts EXCEPT ![self] = <<>>]
                                              /\ iterator' = [iterator EXCEPT ![self] = 1]
                                              /\ learnedChan' = decidedWrite'
                                              /\ pc' = [pc EXCEPT ![self] = "garbageCollection"]
                                              /\ UNCHANGED << decidedWrite0,
                                                              decidedWrite1 >>
                                         ELSE /\ decidedWrite0' = learnedChan
                                              /\ decidedWrite1' = decidedWrite0'
                                              /\ learnedChan' = decidedWrite1'
                                              /\ pc' = [pc EXCEPT ![self] = "L"]
                                              /\ UNCHANGED << decidedWrite,
                                                              newAccepts,
                                                              iterator >>
                                   /\ UNCHANGED << numAccepted, entry >>
                        /\ UNCHANGED << network, values, lastSeenAbstract,
                                        monitorLastSeen,
                                        timeoutCheckerAbstract,
                                        sleeperAbstract, kvClient, idAbstract,
                                        requestSet, paxosLayerChan, database,
                                        electionInProgresssAbstract,
                                        iAmTheLeaderAbstract,
                                        leaderFailureAbstract, valueStreamRead,
                                        mailboxesWrite, mailboxesWrite0,
                                        mailboxesRead, iAmTheLeaderWrite,
                                        electionInProgressWrite,
                                        leaderFailureRead, iAmTheLeaderWrite0,
                                        electionInProgressWrite0,
                                        iAmTheLeaderWrite1,
                                        electionInProgressWrite1,
                                        mailboxesWrite1, iAmTheLeaderWrite2,
                                        electionInProgressWrite2,
                                        mailboxesWrite2, iAmTheLeaderWrite3,
                                        electionInProgressWrite3,
                                        iAmTheLeaderWrite4,
                                        electionInProgressWrite4,
                                        mailboxesWrite3,
                                        electionInProgressWrite5,
                                        mailboxesWrite4, iAmTheLeaderWrite5,
                                        electionInProgressWrite6,
                                        mailboxesWrite5, mailboxesWrite6,
                                        iAmTheLeaderWrite6,
                                        electionInProgressWrite7,
                                        mailboxesWrite7, iAmTheLeaderWrite7,
                                        electionInProgressWrite8,
                                        mailboxesWrite8, iAmTheLeaderWrite8,
                                        electionInProgressWrite9,
                                        mailboxesRead0, mailboxesWrite9,
                                        mailboxesWrite10, mailboxesWrite11,
                                        mailboxesWrite12, mailboxesWrite13,
                                        mailboxesWrite14, mailboxesWrite15,
                                        mailboxesRead1, mailboxesWrite16,
                                        decidedWrite2, mailboxesWrite17,
                                        decidedWrite3, electionInProgressRead,
                                        iAmTheLeaderRead, mailboxesWrite18,
                                        mailboxesWrite19,
                                        heartbeatFrequencyRead, sleeperWrite,
                                        mailboxesWrite20, sleeperWrite0,
                                        mailboxesWrite21, sleeperWrite1,
                                        mailboxesRead2, lastSeenWrite,
                                        mailboxesWrite22, lastSeenWrite0,
                                        mailboxesWrite23, sleeperWrite2,
                                        lastSeenWrite1,
                                        electionInProgressRead0,
                                        iAmTheLeaderRead0, lastSeenRead,
                                        timeoutCheckerRead,
                                        timeoutCheckerWrite,
                                        timeoutCheckerWrite0,
                                        timeoutCheckerWrite1,
                                        leaderFailureWrite,
                                        electionInProgressWrite10,
                                        leaderFailureWrite0,
                                        electionInProgressWrite11,
                                        timeoutCheckerWrite2,
                                        leaderFailureWrite1,
                                        electionInProgressWrite12,
                                        monitorFrequencyRead, sleeperWrite3,
                                        timeoutCheckerWrite3,
                                        leaderFailureWrite2,
                                        electionInProgressWrite13,
                                        sleeperWrite4, requestsRead,
                                        requestsWrite, myIdRead, dbRead,
                                        upstreamWrite, upstreamWrite0,
                                        iAmTheLeaderRead1, proposerChanWrite,
                                        paxosChanRead, proposerChanWrite0,
                                        upstreamWrite1, proposerChanWrite1,
                                        upstreamWrite2, requestsWrite0,
                                        upstreamWrite3, proposerChanWrite2,
                                        learnerChanRead, kvIdRead, dbWrite,
                                        kvIdRead0, kvIdRead1,
                                        requestServiceWrite,
                                        requestServiceWrite0, dbWrite0,
                                        requestServiceWrite1, b, s, elected,
                                        acceptedValues_, max, index_, entry_,
                                        promises, heartbeatMonitorId, accepts_,
                                        value, repropose, resp, maxBal,
                                        loopIndex, acceptedValues, payload,
                                        msg_, accepts, msg_l,
                                        heartbeatFrequencyLocal, msg_h, index,
                                        monitorFrequencyLocal, heartbeatId_,
                                        msg, null, heartbeatId, proposerId,
                                        counter, requestId_, putOk,
                                        confirmedRequestId, learnerId,
                                        operation, requestId >>

garbageCollection(self) == /\ pc[self] = "garbageCollection"
                           /\ IF (iterator[self]) <= (Len(accepts[self]))
                                 THEN /\ entry' = [entry EXCEPT ![self] = accepts[self][iterator[self]]]
                                      /\ IF ((entry'[self]).slot) # ((msg_l[self]).slot)
                                            THEN /\ newAccepts' = [newAccepts EXCEPT ![self] = Append(newAccepts[self], entry'[self])]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED newAccepts
                                      /\ iterator' = [iterator EXCEPT ![self] = (iterator[self]) + (1)]
                                      /\ pc' = [pc EXCEPT ![self] = "garbageCollection"]
                                      /\ UNCHANGED accepts
                                 ELSE /\ accepts' = [accepts EXCEPT ![self] = newAccepts[self]]
                                      /\ pc' = [pc EXCEPT ![self] = "L"]
                                      /\ UNCHANGED << newAccepts, iterator,
                                                      entry >>
                           /\ UNCHANGED << network, values, lastSeenAbstract,
                                           monitorLastSeen,
                                           timeoutCheckerAbstract,
                                           sleeperAbstract, kvClient,
                                           idAbstract, requestSet, learnedChan,
                                           paxosLayerChan, database,
                                           electionInProgresssAbstract,
                                           iAmTheLeaderAbstract,
                                           leaderFailureAbstract,
                                           valueStreamRead, mailboxesWrite,
                                           mailboxesWrite0, mailboxesRead,
                                           iAmTheLeaderWrite,
                                           electionInProgressWrite,
                                           leaderFailureRead,
                                           iAmTheLeaderWrite0,
                                           electionInProgressWrite0,
                                           iAmTheLeaderWrite1,
                                           electionInProgressWrite1,
                                           mailboxesWrite1, iAmTheLeaderWrite2,
                                           electionInProgressWrite2,
                                           mailboxesWrite2, iAmTheLeaderWrite3,
                                           electionInProgressWrite3,
                                           iAmTheLeaderWrite4,
                                           electionInProgressWrite4,
                                           mailboxesWrite3,
                                           electionInProgressWrite5,
                                           mailboxesWrite4, iAmTheLeaderWrite5,
                                           electionInProgressWrite6,
                                           mailboxesWrite5, mailboxesWrite6,
                                           iAmTheLeaderWrite6,
                                           electionInProgressWrite7,
                                           mailboxesWrite7, iAmTheLeaderWrite7,
                                           electionInProgressWrite8,
                                           mailboxesWrite8, iAmTheLeaderWrite8,
                                           electionInProgressWrite9,
                                           mailboxesRead0, mailboxesWrite9,
                                           mailboxesWrite10, mailboxesWrite11,
                                           mailboxesWrite12, mailboxesWrite13,
                                           mailboxesWrite14, mailboxesWrite15,
                                           mailboxesRead1, mailboxesWrite16,
                                           decidedWrite, decidedWrite0,
                                           decidedWrite1, decidedWrite2,
                                           mailboxesWrite17, decidedWrite3,
                                           electionInProgressRead,
                                           iAmTheLeaderRead, mailboxesWrite18,
                                           mailboxesWrite19,
                                           heartbeatFrequencyRead,
                                           sleeperWrite, mailboxesWrite20,
                                           sleeperWrite0, mailboxesWrite21,
                                           sleeperWrite1, mailboxesRead2,
                                           lastSeenWrite, mailboxesWrite22,
                                           lastSeenWrite0, mailboxesWrite23,
                                           sleeperWrite2, lastSeenWrite1,
                                           electionInProgressRead0,
                                           iAmTheLeaderRead0, lastSeenRead,
                                           timeoutCheckerRead,
                                           timeoutCheckerWrite,
                                           timeoutCheckerWrite0,
                                           timeoutCheckerWrite1,
                                           leaderFailureWrite,
                                           electionInProgressWrite10,
                                           leaderFailureWrite0,
                                           electionInProgressWrite11,
                                           timeoutCheckerWrite2,
                                           leaderFailureWrite1,
                                           electionInProgressWrite12,
                                           monitorFrequencyRead, sleeperWrite3,
                                           timeoutCheckerWrite3,
                                           leaderFailureWrite2,
                                           electionInProgressWrite13,
                                           sleeperWrite4, requestsRead,
                                           requestsWrite, myIdRead, dbRead,
                                           upstreamWrite, upstreamWrite0,
                                           iAmTheLeaderRead1,
                                           proposerChanWrite, paxosChanRead,
                                           proposerChanWrite0, upstreamWrite1,
                                           proposerChanWrite1, upstreamWrite2,
                                           requestsWrite0, upstreamWrite3,
                                           proposerChanWrite2, learnerChanRead,
                                           kvIdRead, dbWrite, kvIdRead0,
                                           kvIdRead1, requestServiceWrite,
                                           requestServiceWrite0, dbWrite0,
                                           requestServiceWrite1, b, s, elected,
                                           acceptedValues_, max, index_,
                                           entry_, promises,
                                           heartbeatMonitorId, accepts_, value,
                                           repropose, resp, maxBal, loopIndex,
                                           acceptedValues, payload, msg_,
                                           numAccepted, msg_l,
                                           heartbeatFrequencyLocal, msg_h,
                                           index, monitorFrequencyLocal,
                                           heartbeatId_, msg, null,
                                           heartbeatId, proposerId, counter,
                                           requestId_, putOk,
                                           confirmedRequestId, learnerId,
                                           operation, requestId >>

learner(self) == L(self) \/ LGotAcc(self) \/ LCheckMajority(self)
                    \/ garbageCollection(self)

mainLoop(self) == /\ pc[self] = "mainLoop"
                  /\ IF TRUE
                        THEN /\ pc' = [pc EXCEPT ![self] = "leaderLoop"]
                             /\ UNCHANGED << network, lastSeenAbstract,
                                             sleeperAbstract, mailboxesWrite23,
                                             sleeperWrite2, lastSeenWrite1 >>
                        ELSE /\ mailboxesWrite23' = network
                             /\ sleeperWrite2' = sleeperAbstract
                             /\ lastSeenWrite1' = lastSeenAbstract
                             /\ network' = mailboxesWrite23'
                             /\ lastSeenAbstract' = lastSeenWrite1'
                             /\ sleeperAbstract' = sleeperWrite2'
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << values, monitorLastSeen,
                                  timeoutCheckerAbstract, kvClient, idAbstract,
                                  requestSet, learnedChan, paxosLayerChan,
                                  database, electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesWrite14, mailboxesWrite15,
                                  mailboxesRead1, mailboxesWrite16,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, mailboxesWrite17,
                                  decidedWrite3, electionInProgressRead,
                                  iAmTheLeaderRead, mailboxesWrite18,
                                  mailboxesWrite19, heartbeatFrequencyRead,
                                  sleeperWrite, mailboxesWrite20,
                                  sleeperWrite0, mailboxesWrite21,
                                  sleeperWrite1, mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  electionInProgressRead0, iAmTheLeaderRead0,
                                  lastSeenRead, timeoutCheckerRead,
                                  timeoutCheckerWrite, timeoutCheckerWrite0,
                                  timeoutCheckerWrite1, leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite, myIdRead,
                                  dbRead, upstreamWrite, upstreamWrite0,
                                  iAmTheLeaderRead1, proposerChanWrite,
                                  paxosChanRead, proposerChanWrite0,
                                  upstreamWrite1, proposerChanWrite1,
                                  upstreamWrite2, requestsWrite0,
                                  upstreamWrite3, proposerChanWrite2,
                                  learnerChanRead, kvIdRead, dbWrite,
                                  kvIdRead0, kvIdRead1, requestServiceWrite,
                                  requestServiceWrite0, dbWrite0,
                                  requestServiceWrite1, b, s, elected,
                                  acceptedValues_, max, index_, entry_,
                                  promises, heartbeatMonitorId, accepts_,
                                  value, repropose, resp, maxBal, loopIndex,
                                  acceptedValues, payload, msg_, accepts,
                                  newAccepts, numAccepted, iterator, entry,
                                  msg_l, heartbeatFrequencyLocal, msg_h, index,
                                  monitorFrequencyLocal, heartbeatId_, msg,
                                  null, heartbeatId, proposerId, counter,
                                  requestId_, putOk, confirmedRequestId,
                                  learnerId, operation, requestId >>

leaderLoop(self) == /\ pc[self] = "leaderLoop"
                    /\ electionInProgressRead' = electionInProgresssAbstract[self]
                    /\ iAmTheLeaderRead' = iAmTheLeaderAbstract[self]
                    /\ IF (~(electionInProgressRead')) /\ (iAmTheLeaderRead')
                          THEN /\ index' = [index EXCEPT ![self] = (3) * (NUM_NODES)]
                               /\ pc' = [pc EXCEPT ![self] = "heartbeatBroadcast"]
                               /\ UNCHANGED << network, sleeperAbstract,
                                               mailboxesWrite21, sleeperWrite1 >>
                          ELSE /\ mailboxesWrite21' = network
                               /\ sleeperWrite1' = sleeperAbstract
                               /\ network' = mailboxesWrite21'
                               /\ sleeperAbstract' = sleeperWrite1'
                               /\ pc' = [pc EXCEPT ![self] = "followerLoop"]
                               /\ index' = index
                    /\ UNCHANGED << values, lastSeenAbstract, monitorLastSeen,
                                    timeoutCheckerAbstract, kvClient,
                                    idAbstract, requestSet, learnedChan,
                                    paxosLayerChan, database,
                                    electionInProgresssAbstract,
                                    iAmTheLeaderAbstract,
                                    leaderFailureAbstract, valueStreamRead,
                                    mailboxesWrite, mailboxesWrite0,
                                    mailboxesRead, iAmTheLeaderWrite,
                                    electionInProgressWrite, leaderFailureRead,
                                    iAmTheLeaderWrite0,
                                    electionInProgressWrite0,
                                    iAmTheLeaderWrite1,
                                    electionInProgressWrite1, mailboxesWrite1,
                                    iAmTheLeaderWrite2,
                                    electionInProgressWrite2, mailboxesWrite2,
                                    iAmTheLeaderWrite3,
                                    electionInProgressWrite3,
                                    iAmTheLeaderWrite4,
                                    electionInProgressWrite4, mailboxesWrite3,
                                    electionInProgressWrite5, mailboxesWrite4,
                                    iAmTheLeaderWrite5,
                                    electionInProgressWrite6, mailboxesWrite5,
                                    mailboxesWrite6, iAmTheLeaderWrite6,
                                    electionInProgressWrite7, mailboxesWrite7,
                                    iAmTheLeaderWrite7,
                                    electionInProgressWrite8, mailboxesWrite8,
                                    iAmTheLeaderWrite8,
                                    electionInProgressWrite9, mailboxesRead0,
                                    mailboxesWrite9, mailboxesWrite10,
                                    mailboxesWrite11, mailboxesWrite12,
                                    mailboxesWrite13, mailboxesWrite14,
                                    mailboxesWrite15, mailboxesRead1,
                                    mailboxesWrite16, decidedWrite,
                                    decidedWrite0, decidedWrite1,
                                    decidedWrite2, mailboxesWrite17,
                                    decidedWrite3, mailboxesWrite18,
                                    mailboxesWrite19, heartbeatFrequencyRead,
                                    sleeperWrite, mailboxesWrite20,
                                    sleeperWrite0, mailboxesRead2,
                                    lastSeenWrite, mailboxesWrite22,
                                    lastSeenWrite0, mailboxesWrite23,
                                    sleeperWrite2, lastSeenWrite1,
                                    electionInProgressRead0, iAmTheLeaderRead0,
                                    lastSeenRead, timeoutCheckerRead,
                                    timeoutCheckerWrite, timeoutCheckerWrite0,
                                    timeoutCheckerWrite1, leaderFailureWrite,
                                    electionInProgressWrite10,
                                    leaderFailureWrite0,
                                    electionInProgressWrite11,
                                    timeoutCheckerWrite2, leaderFailureWrite1,
                                    electionInProgressWrite12,
                                    monitorFrequencyRead, sleeperWrite3,
                                    timeoutCheckerWrite3, leaderFailureWrite2,
                                    electionInProgressWrite13, sleeperWrite4,
                                    requestsRead, requestsWrite, myIdRead,
                                    dbRead, upstreamWrite, upstreamWrite0,
                                    iAmTheLeaderRead1, proposerChanWrite,
                                    paxosChanRead, proposerChanWrite0,
                                    upstreamWrite1, proposerChanWrite1,
                                    upstreamWrite2, requestsWrite0,
                                    upstreamWrite3, proposerChanWrite2,
                                    learnerChanRead, kvIdRead, dbWrite,
                                    kvIdRead0, kvIdRead1, requestServiceWrite,
                                    requestServiceWrite0, dbWrite0,
                                    requestServiceWrite1, b, s, elected,
                                    acceptedValues_, max, index_, entry_,
                                    promises, heartbeatMonitorId, accepts_,
                                    value, repropose, resp, maxBal, loopIndex,
                                    acceptedValues, payload, msg_, accepts,
                                    newAccepts, numAccepted, iterator, entry,
                                    msg_l, heartbeatFrequencyLocal, msg_h,
                                    monitorFrequencyLocal, heartbeatId_, msg,
                                    null, heartbeatId, proposerId, counter,
                                    requestId_, putOk, confirmedRequestId,
                                    learnerId, operation, requestId >>

heartbeatBroadcast(self) == /\ pc[self] = "heartbeatBroadcast"
                            /\ IF (index[self]) <= (((4) * (NUM_NODES)) - (1))
                                  THEN /\ IF (index[self]) # (self)
                                             THEN /\ (Len(network[index[self]])) < (BUFFER_SIZE)
                                                  /\ mailboxesWrite18' = [network EXCEPT ![index[self]] = Append(network[index[self]], [type |-> HEARTBEAT_MSG, leader |-> (self) - ((3) * (NUM_NODES))])]
                                                  /\ index' = [index EXCEPT ![self] = (index[self]) + (1)]
                                                  /\ mailboxesWrite19' = mailboxesWrite18'
                                                  /\ mailboxesWrite20' = mailboxesWrite19'
                                                  /\ sleeperWrite0' = sleeperAbstract
                                                  /\ network' = mailboxesWrite20'
                                                  /\ sleeperAbstract' = sleeperWrite0'
                                                  /\ pc' = [pc EXCEPT ![self] = "heartbeatBroadcast"]
                                             ELSE /\ mailboxesWrite19' = network
                                                  /\ mailboxesWrite20' = mailboxesWrite19'
                                                  /\ sleeperWrite0' = sleeperAbstract
                                                  /\ network' = mailboxesWrite20'
                                                  /\ sleeperAbstract' = sleeperWrite0'
                                                  /\ pc' = [pc EXCEPT ![self] = "heartbeatBroadcast"]
                                                  /\ UNCHANGED << mailboxesWrite18,
                                                                  index >>
                                       /\ UNCHANGED << heartbeatFrequencyRead,
                                                       sleeperWrite >>
                                  ELSE /\ heartbeatFrequencyRead' = heartbeatFrequencyLocal[self]
                                       /\ sleeperWrite' = heartbeatFrequencyRead'
                                       /\ mailboxesWrite20' = network
                                       /\ sleeperWrite0' = sleeperWrite'
                                       /\ network' = mailboxesWrite20'
                                       /\ sleeperAbstract' = sleeperWrite0'
                                       /\ pc' = [pc EXCEPT ![self] = "leaderLoop"]
                                       /\ UNCHANGED << mailboxesWrite18,
                                                       mailboxesWrite19, index >>
                            /\ UNCHANGED << values, lastSeenAbstract,
                                            monitorLastSeen,
                                            timeoutCheckerAbstract, kvClient,
                                            idAbstract, requestSet,
                                            learnedChan, paxosLayerChan,
                                            database,
                                            electionInProgresssAbstract,
                                            iAmTheLeaderAbstract,
                                            leaderFailureAbstract,
                                            valueStreamRead, mailboxesWrite,
                                            mailboxesWrite0, mailboxesRead,
                                            iAmTheLeaderWrite,
                                            electionInProgressWrite,
                                            leaderFailureRead,
                                            iAmTheLeaderWrite0,
                                            electionInProgressWrite0,
                                            iAmTheLeaderWrite1,
                                            electionInProgressWrite1,
                                            mailboxesWrite1,
                                            iAmTheLeaderWrite2,
                                            electionInProgressWrite2,
                                            mailboxesWrite2,
                                            iAmTheLeaderWrite3,
                                            electionInProgressWrite3,
                                            iAmTheLeaderWrite4,
                                            electionInProgressWrite4,
                                            mailboxesWrite3,
                                            electionInProgressWrite5,
                                            mailboxesWrite4,
                                            iAmTheLeaderWrite5,
                                            electionInProgressWrite6,
                                            mailboxesWrite5, mailboxesWrite6,
                                            iAmTheLeaderWrite6,
                                            electionInProgressWrite7,
                                            mailboxesWrite7,
                                            iAmTheLeaderWrite7,
                                            electionInProgressWrite8,
                                            mailboxesWrite8,
                                            iAmTheLeaderWrite8,
                                            electionInProgressWrite9,
                                            mailboxesRead0, mailboxesWrite9,
                                            mailboxesWrite10, mailboxesWrite11,
                                            mailboxesWrite12, mailboxesWrite13,
                                            mailboxesWrite14, mailboxesWrite15,
                                            mailboxesRead1, mailboxesWrite16,
                                            decidedWrite, decidedWrite0,
                                            decidedWrite1, decidedWrite2,
                                            mailboxesWrite17, decidedWrite3,
                                            electionInProgressRead,
                                            iAmTheLeaderRead, mailboxesWrite21,
                                            sleeperWrite1, mailboxesRead2,
                                            lastSeenWrite, mailboxesWrite22,
                                            lastSeenWrite0, mailboxesWrite23,
                                            sleeperWrite2, lastSeenWrite1,
                                            electionInProgressRead0,
                                            iAmTheLeaderRead0, lastSeenRead,
                                            timeoutCheckerRead,
                                            timeoutCheckerWrite,
                                            timeoutCheckerWrite0,
                                            timeoutCheckerWrite1,
                                            leaderFailureWrite,
                                            electionInProgressWrite10,
                                            leaderFailureWrite0,
                                            electionInProgressWrite11,
                                            timeoutCheckerWrite2,
                                            leaderFailureWrite1,
                                            electionInProgressWrite12,
                                            monitorFrequencyRead,
                                            sleeperWrite3,
                                            timeoutCheckerWrite3,
                                            leaderFailureWrite2,
                                            electionInProgressWrite13,
                                            sleeperWrite4, requestsRead,
                                            requestsWrite, myIdRead, dbRead,
                                            upstreamWrite, upstreamWrite0,
                                            iAmTheLeaderRead1,
                                            proposerChanWrite, paxosChanRead,
                                            proposerChanWrite0, upstreamWrite1,
                                            proposerChanWrite1, upstreamWrite2,
                                            requestsWrite0, upstreamWrite3,
                                            proposerChanWrite2,
                                            learnerChanRead, kvIdRead, dbWrite,
                                            kvIdRead0, kvIdRead1,
                                            requestServiceWrite,
                                            requestServiceWrite0, dbWrite0,
                                            requestServiceWrite1, b, s,
                                            elected, acceptedValues_, max,
                                            index_, entry_, promises,
                                            heartbeatMonitorId, accepts_,
                                            value, repropose, resp, maxBal,
                                            loopIndex, acceptedValues, payload,
                                            msg_, accepts, newAccepts,
                                            numAccepted, iterator, entry,
                                            msg_l, heartbeatFrequencyLocal,
                                            msg_h, monitorFrequencyLocal,
                                            heartbeatId_, msg, null,
                                            heartbeatId, proposerId, counter,
                                            requestId_, putOk,
                                            confirmedRequestId, learnerId,
                                            operation, requestId >>

followerLoop(self) == /\ pc[self] = "followerLoop"
                      /\ electionInProgressRead' = electionInProgresssAbstract[self]
                      /\ iAmTheLeaderRead' = iAmTheLeaderAbstract[self]
                      /\ IF (~(electionInProgressRead')) /\ (~(iAmTheLeaderRead'))
                            THEN /\ (Len(network[self])) > (0)
                                 /\ LET msg4 == Head(network[self]) IN
                                      /\ mailboxesWrite18' = [network EXCEPT ![self] = Tail(network[self])]
                                      /\ mailboxesRead2' = msg4
                                 /\ msg_h' = [msg_h EXCEPT ![self] = mailboxesRead2']
                                 /\ Assert(((msg_h'[self]).type) = (HEARTBEAT_MSG),
                                           "Failure of assertion at line 1028, column 25.")
                                 /\ lastSeenWrite' = msg_h'[self]
                                 /\ mailboxesWrite22' = mailboxesWrite18'
                                 /\ lastSeenWrite0' = lastSeenWrite'
                                 /\ network' = mailboxesWrite22'
                                 /\ lastSeenAbstract' = lastSeenWrite0'
                                 /\ pc' = [pc EXCEPT ![self] = "followerLoop"]
                            ELSE /\ mailboxesWrite22' = network
                                 /\ lastSeenWrite0' = lastSeenAbstract
                                 /\ network' = mailboxesWrite22'
                                 /\ lastSeenAbstract' = lastSeenWrite0'
                                 /\ pc' = [pc EXCEPT ![self] = "mainLoop"]
                                 /\ UNCHANGED << mailboxesWrite18,
                                                 mailboxesRead2, lastSeenWrite,
                                                 msg_h >>
                      /\ UNCHANGED << values, monitorLastSeen,
                                      timeoutCheckerAbstract, sleeperAbstract,
                                      kvClient, idAbstract, requestSet,
                                      learnedChan, paxosLayerChan, database,
                                      electionInProgresssAbstract,
                                      iAmTheLeaderAbstract,
                                      leaderFailureAbstract, valueStreamRead,
                                      mailboxesWrite, mailboxesWrite0,
                                      mailboxesRead, iAmTheLeaderWrite,
                                      electionInProgressWrite,
                                      leaderFailureRead, iAmTheLeaderWrite0,
                                      electionInProgressWrite0,
                                      iAmTheLeaderWrite1,
                                      electionInProgressWrite1,
                                      mailboxesWrite1, iAmTheLeaderWrite2,
                                      electionInProgressWrite2,
                                      mailboxesWrite2, iAmTheLeaderWrite3,
                                      electionInProgressWrite3,
                                      iAmTheLeaderWrite4,
                                      electionInProgressWrite4,
                                      mailboxesWrite3,
                                      electionInProgressWrite5,
                                      mailboxesWrite4, iAmTheLeaderWrite5,
                                      electionInProgressWrite6,
                                      mailboxesWrite5, mailboxesWrite6,
                                      iAmTheLeaderWrite6,
                                      electionInProgressWrite7,
                                      mailboxesWrite7, iAmTheLeaderWrite7,
                                      electionInProgressWrite8,
                                      mailboxesWrite8, iAmTheLeaderWrite8,
                                      electionInProgressWrite9, mailboxesRead0,
                                      mailboxesWrite9, mailboxesWrite10,
                                      mailboxesWrite11, mailboxesWrite12,
                                      mailboxesWrite13, mailboxesWrite14,
                                      mailboxesWrite15, mailboxesRead1,
                                      mailboxesWrite16, decidedWrite,
                                      decidedWrite0, decidedWrite1,
                                      decidedWrite2, mailboxesWrite17,
                                      decidedWrite3, mailboxesWrite19,
                                      heartbeatFrequencyRead, sleeperWrite,
                                      mailboxesWrite20, sleeperWrite0,
                                      mailboxesWrite21, sleeperWrite1,
                                      mailboxesWrite23, sleeperWrite2,
                                      lastSeenWrite1, electionInProgressRead0,
                                      iAmTheLeaderRead0, lastSeenRead,
                                      timeoutCheckerRead, timeoutCheckerWrite,
                                      timeoutCheckerWrite0,
                                      timeoutCheckerWrite1, leaderFailureWrite,
                                      electionInProgressWrite10,
                                      leaderFailureWrite0,
                                      electionInProgressWrite11,
                                      timeoutCheckerWrite2,
                                      leaderFailureWrite1,
                                      electionInProgressWrite12,
                                      monitorFrequencyRead, sleeperWrite3,
                                      timeoutCheckerWrite3,
                                      leaderFailureWrite2,
                                      electionInProgressWrite13, sleeperWrite4,
                                      requestsRead, requestsWrite, myIdRead,
                                      dbRead, upstreamWrite, upstreamWrite0,
                                      iAmTheLeaderRead1, proposerChanWrite,
                                      paxosChanRead, proposerChanWrite0,
                                      upstreamWrite1, proposerChanWrite1,
                                      upstreamWrite2, requestsWrite0,
                                      upstreamWrite3, proposerChanWrite2,
                                      learnerChanRead, kvIdRead, dbWrite,
                                      kvIdRead0, kvIdRead1,
                                      requestServiceWrite,
                                      requestServiceWrite0, dbWrite0,
                                      requestServiceWrite1, b, s, elected,
                                      acceptedValues_, max, index_, entry_,
                                      promises, heartbeatMonitorId, accepts_,
                                      value, repropose, resp, maxBal,
                                      loopIndex, acceptedValues, payload, msg_,
                                      accepts, newAccepts, numAccepted,
                                      iterator, entry, msg_l,
                                      heartbeatFrequencyLocal, index,
                                      monitorFrequencyLocal, heartbeatId_, msg,
                                      null, heartbeatId, proposerId, counter,
                                      requestId_, putOk, confirmedRequestId,
                                      learnerId, operation, requestId >>

heartbeatAction(self) == mainLoop(self) \/ leaderLoop(self)
                            \/ heartbeatBroadcast(self)
                            \/ followerLoop(self)

findId_(self) == /\ pc[self] = "findId_"
                 /\ heartbeatId_' = [heartbeatId_ EXCEPT ![self] = (self) - (NUM_NODES)]
                 /\ pc' = [pc EXCEPT ![self] = "monitorLoop"]
                 /\ UNCHANGED << network, values, lastSeenAbstract,
                                 monitorLastSeen, timeoutCheckerAbstract,
                                 sleeperAbstract, kvClient, idAbstract,
                                 requestSet, learnedChan, paxosLayerChan,
                                 database, electionInProgresssAbstract,
                                 iAmTheLeaderAbstract, leaderFailureAbstract,
                                 valueStreamRead, mailboxesWrite,
                                 mailboxesWrite0, mailboxesRead,
                                 iAmTheLeaderWrite, electionInProgressWrite,
                                 leaderFailureRead, iAmTheLeaderWrite0,
                                 electionInProgressWrite0, iAmTheLeaderWrite1,
                                 electionInProgressWrite1, mailboxesWrite1,
                                 iAmTheLeaderWrite2, electionInProgressWrite2,
                                 mailboxesWrite2, iAmTheLeaderWrite3,
                                 electionInProgressWrite3, iAmTheLeaderWrite4,
                                 electionInProgressWrite4, mailboxesWrite3,
                                 electionInProgressWrite5, mailboxesWrite4,
                                 iAmTheLeaderWrite5, electionInProgressWrite6,
                                 mailboxesWrite5, mailboxesWrite6,
                                 iAmTheLeaderWrite6, electionInProgressWrite7,
                                 mailboxesWrite7, iAmTheLeaderWrite7,
                                 electionInProgressWrite8, mailboxesWrite8,
                                 iAmTheLeaderWrite8, electionInProgressWrite9,
                                 mailboxesRead0, mailboxesWrite9,
                                 mailboxesWrite10, mailboxesWrite11,
                                 mailboxesWrite12, mailboxesWrite13,
                                 mailboxesWrite14, mailboxesWrite15,
                                 mailboxesRead1, mailboxesWrite16,
                                 decidedWrite, decidedWrite0, decidedWrite1,
                                 decidedWrite2, mailboxesWrite17,
                                 decidedWrite3, electionInProgressRead,
                                 iAmTheLeaderRead, mailboxesWrite18,
                                 mailboxesWrite19, heartbeatFrequencyRead,
                                 sleeperWrite, mailboxesWrite20, sleeperWrite0,
                                 mailboxesWrite21, sleeperWrite1,
                                 mailboxesRead2, lastSeenWrite,
                                 mailboxesWrite22, lastSeenWrite0,
                                 mailboxesWrite23, sleeperWrite2,
                                 lastSeenWrite1, electionInProgressRead0,
                                 iAmTheLeaderRead0, lastSeenRead,
                                 timeoutCheckerRead, timeoutCheckerWrite,
                                 timeoutCheckerWrite0, timeoutCheckerWrite1,
                                 leaderFailureWrite, electionInProgressWrite10,
                                 leaderFailureWrite0,
                                 electionInProgressWrite11,
                                 timeoutCheckerWrite2, leaderFailureWrite1,
                                 electionInProgressWrite12,
                                 monitorFrequencyRead, sleeperWrite3,
                                 timeoutCheckerWrite3, leaderFailureWrite2,
                                 electionInProgressWrite13, sleeperWrite4,
                                 requestsRead, requestsWrite, myIdRead, dbRead,
                                 upstreamWrite, upstreamWrite0,
                                 iAmTheLeaderRead1, proposerChanWrite,
                                 paxosChanRead, proposerChanWrite0,
                                 upstreamWrite1, proposerChanWrite1,
                                 upstreamWrite2, requestsWrite0,
                                 upstreamWrite3, proposerChanWrite2,
                                 learnerChanRead, kvIdRead, dbWrite, kvIdRead0,
                                 kvIdRead1, requestServiceWrite,
                                 requestServiceWrite0, dbWrite0,
                                 requestServiceWrite1, b, s, elected,
                                 acceptedValues_, max, index_, entry_,
                                 promises, heartbeatMonitorId, accepts_, value,
                                 repropose, resp, maxBal, loopIndex,
                                 acceptedValues, payload, msg_, accepts,
                                 newAccepts, numAccepted, iterator, entry,
                                 msg_l, heartbeatFrequencyLocal, msg_h, index,
                                 monitorFrequencyLocal, msg, null, heartbeatId,
                                 proposerId, counter, requestId_, putOk,
                                 confirmedRequestId, learnerId, operation,
                                 requestId >>

monitorLoop(self) == /\ pc[self] = "monitorLoop"
                     /\ IF TRUE
                           THEN /\ electionInProgressRead0' = electionInProgresssAbstract[heartbeatId_[self]]
                                /\ iAmTheLeaderRead0' = iAmTheLeaderAbstract[heartbeatId_[self]]
                                /\ IF (~(electionInProgressRead0')) /\ (~(iAmTheLeaderRead0'))
                                      THEN /\ lastSeenRead' = monitorLastSeen
                                           /\ IF (timeoutCheckerAbstract[lastSeenRead']) < (MAX_FAILURES)
                                                 THEN /\ \/ /\ timeoutCheckerWrite' = [timeoutCheckerAbstract EXCEPT ![lastSeenRead'] = (timeoutCheckerAbstract[lastSeenRead']) + (1)]
                                                            /\ timeoutCheckerRead' = TRUE
                                                            /\ timeoutCheckerWrite0' = timeoutCheckerWrite'
                                                            /\ timeoutCheckerWrite1' = timeoutCheckerWrite0'
                                                         \/ /\ timeoutCheckerRead' = FALSE
                                                            /\ timeoutCheckerWrite0' = timeoutCheckerAbstract
                                                            /\ timeoutCheckerWrite1' = timeoutCheckerWrite0'
                                                            /\ UNCHANGED timeoutCheckerWrite
                                                 ELSE /\ timeoutCheckerRead' = FALSE
                                                      /\ timeoutCheckerWrite1' = timeoutCheckerAbstract
                                                      /\ UNCHANGED << timeoutCheckerWrite,
                                                                      timeoutCheckerWrite0 >>
                                           /\ IF timeoutCheckerRead'
                                                 THEN /\ leaderFailureWrite' = [leaderFailureAbstract EXCEPT ![heartbeatId_[self]] = TRUE]
                                                      /\ electionInProgressWrite10' = [electionInProgresssAbstract EXCEPT ![heartbeatId_[self]] = TRUE]
                                                      /\ leaderFailureWrite0' = leaderFailureWrite'
                                                      /\ electionInProgressWrite11' = electionInProgressWrite10'
                                                      /\ timeoutCheckerWrite2' = timeoutCheckerWrite1'
                                                      /\ leaderFailureWrite1' = leaderFailureWrite0'
                                                      /\ electionInProgressWrite12' = electionInProgressWrite11'
                                                 ELSE /\ leaderFailureWrite0' = leaderFailureAbstract
                                                      /\ electionInProgressWrite11' = electionInProgresssAbstract
                                                      /\ timeoutCheckerWrite2' = timeoutCheckerWrite1'
                                                      /\ leaderFailureWrite1' = leaderFailureWrite0'
                                                      /\ electionInProgressWrite12' = electionInProgressWrite11'
                                                      /\ UNCHANGED << leaderFailureWrite,
                                                                      electionInProgressWrite10 >>
                                      ELSE /\ timeoutCheckerWrite2' = timeoutCheckerAbstract
                                           /\ leaderFailureWrite1' = leaderFailureAbstract
                                           /\ electionInProgressWrite12' = electionInProgresssAbstract
                                           /\ UNCHANGED << lastSeenRead,
                                                           timeoutCheckerRead,
                                                           timeoutCheckerWrite,
                                                           timeoutCheckerWrite0,
                                                           timeoutCheckerWrite1,
                                                           leaderFailureWrite,
                                                           electionInProgressWrite10,
                                                           leaderFailureWrite0,
                                                           electionInProgressWrite11 >>
                                /\ monitorFrequencyRead' = monitorFrequencyLocal[self]
                                /\ sleeperWrite3' = monitorFrequencyRead'
                                /\ timeoutCheckerWrite3' = timeoutCheckerWrite2'
                                /\ leaderFailureWrite2' = leaderFailureWrite1'
                                /\ electionInProgressWrite13' = electionInProgressWrite12'
                                /\ sleeperWrite4' = sleeperWrite3'
                                /\ timeoutCheckerAbstract' = timeoutCheckerWrite3'
                                /\ leaderFailureAbstract' = leaderFailureWrite2'
                                /\ electionInProgresssAbstract' = electionInProgressWrite13'
                                /\ sleeperAbstract' = sleeperWrite4'
                                /\ pc' = [pc EXCEPT ![self] = "monitorLoop"]
                           ELSE /\ timeoutCheckerWrite3' = timeoutCheckerAbstract
                                /\ leaderFailureWrite2' = leaderFailureAbstract
                                /\ electionInProgressWrite13' = electionInProgresssAbstract
                                /\ sleeperWrite4' = sleeperAbstract
                                /\ timeoutCheckerAbstract' = timeoutCheckerWrite3'
                                /\ leaderFailureAbstract' = leaderFailureWrite2'
                                /\ electionInProgresssAbstract' = electionInProgressWrite13'
                                /\ sleeperAbstract' = sleeperWrite4'
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << electionInProgressRead0,
                                                iAmTheLeaderRead0,
                                                lastSeenRead,
                                                timeoutCheckerRead,
                                                timeoutCheckerWrite,
                                                timeoutCheckerWrite0,
                                                timeoutCheckerWrite1,
                                                leaderFailureWrite,
                                                electionInProgressWrite10,
                                                leaderFailureWrite0,
                                                electionInProgressWrite11,
                                                timeoutCheckerWrite2,
                                                leaderFailureWrite1,
                                                electionInProgressWrite12,
                                                monitorFrequencyRead,
                                                sleeperWrite3 >>
                     /\ UNCHANGED << network, values, lastSeenAbstract,
                                     monitorLastSeen, kvClient, idAbstract,
                                     requestSet, learnedChan, paxosLayerChan,
                                     database, iAmTheLeaderAbstract,
                                     valueStreamRead, mailboxesWrite,
                                     mailboxesWrite0, mailboxesRead,
                                     iAmTheLeaderWrite,
                                     electionInProgressWrite,
                                     leaderFailureRead, iAmTheLeaderWrite0,
                                     electionInProgressWrite0,
                                     iAmTheLeaderWrite1,
                                     electionInProgressWrite1, mailboxesWrite1,
                                     iAmTheLeaderWrite2,
                                     electionInProgressWrite2, mailboxesWrite2,
                                     iAmTheLeaderWrite3,
                                     electionInProgressWrite3,
                                     iAmTheLeaderWrite4,
                                     electionInProgressWrite4, mailboxesWrite3,
                                     electionInProgressWrite5, mailboxesWrite4,
                                     iAmTheLeaderWrite5,
                                     electionInProgressWrite6, mailboxesWrite5,
                                     mailboxesWrite6, iAmTheLeaderWrite6,
                                     electionInProgressWrite7, mailboxesWrite7,
                                     iAmTheLeaderWrite7,
                                     electionInProgressWrite8, mailboxesWrite8,
                                     iAmTheLeaderWrite8,
                                     electionInProgressWrite9, mailboxesRead0,
                                     mailboxesWrite9, mailboxesWrite10,
                                     mailboxesWrite11, mailboxesWrite12,
                                     mailboxesWrite13, mailboxesWrite14,
                                     mailboxesWrite15, mailboxesRead1,
                                     mailboxesWrite16, decidedWrite,
                                     decidedWrite0, decidedWrite1,
                                     decidedWrite2, mailboxesWrite17,
                                     decidedWrite3, electionInProgressRead,
                                     iAmTheLeaderRead, mailboxesWrite18,
                                     mailboxesWrite19, heartbeatFrequencyRead,
                                     sleeperWrite, mailboxesWrite20,
                                     sleeperWrite0, mailboxesWrite21,
                                     sleeperWrite1, mailboxesRead2,
                                     lastSeenWrite, mailboxesWrite22,
                                     lastSeenWrite0, mailboxesWrite23,
                                     sleeperWrite2, lastSeenWrite1,
                                     requestsRead, requestsWrite, myIdRead,
                                     dbRead, upstreamWrite, upstreamWrite0,
                                     iAmTheLeaderRead1, proposerChanWrite,
                                     paxosChanRead, proposerChanWrite0,
                                     upstreamWrite1, proposerChanWrite1,
                                     upstreamWrite2, requestsWrite0,
                                     upstreamWrite3, proposerChanWrite2,
                                     learnerChanRead, kvIdRead, dbWrite,
                                     kvIdRead0, kvIdRead1, requestServiceWrite,
                                     requestServiceWrite0, dbWrite0,
                                     requestServiceWrite1, b, s, elected,
                                     acceptedValues_, max, index_, entry_,
                                     promises, heartbeatMonitorId, accepts_,
                                     value, repropose, resp, maxBal, loopIndex,
                                     acceptedValues, payload, msg_, accepts,
                                     newAccepts, numAccepted, iterator, entry,
                                     msg_l, heartbeatFrequencyLocal, msg_h,
                                     index, monitorFrequencyLocal,
                                     heartbeatId_, msg, null, heartbeatId,
                                     proposerId, counter, requestId_, putOk,
                                     confirmedRequestId, learnerId, operation,
                                     requestId >>

leaderStatusMonitor(self) == findId_(self) \/ monitorLoop(self)

kvInit(self) == /\ pc[self] = "kvInit"
                /\ heartbeatId' = [heartbeatId EXCEPT ![self] = (self) - ((2) * (NUM_NODES))]
                /\ proposerId' = [proposerId EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                /\ UNCHANGED << network, values, lastSeenAbstract,
                                monitorLastSeen, timeoutCheckerAbstract,
                                sleeperAbstract, kvClient, idAbstract,
                                requestSet, learnedChan, paxosLayerChan,
                                database, electionInProgresssAbstract,
                                iAmTheLeaderAbstract, leaderFailureAbstract,
                                valueStreamRead, mailboxesWrite,
                                mailboxesWrite0, mailboxesRead,
                                iAmTheLeaderWrite, electionInProgressWrite,
                                leaderFailureRead, iAmTheLeaderWrite0,
                                electionInProgressWrite0, iAmTheLeaderWrite1,
                                electionInProgressWrite1, mailboxesWrite1,
                                iAmTheLeaderWrite2, electionInProgressWrite2,
                                mailboxesWrite2, iAmTheLeaderWrite3,
                                electionInProgressWrite3, iAmTheLeaderWrite4,
                                electionInProgressWrite4, mailboxesWrite3,
                                electionInProgressWrite5, mailboxesWrite4,
                                iAmTheLeaderWrite5, electionInProgressWrite6,
                                mailboxesWrite5, mailboxesWrite6,
                                iAmTheLeaderWrite6, electionInProgressWrite7,
                                mailboxesWrite7, iAmTheLeaderWrite7,
                                electionInProgressWrite8, mailboxesWrite8,
                                iAmTheLeaderWrite8, electionInProgressWrite9,
                                mailboxesRead0, mailboxesWrite9,
                                mailboxesWrite10, mailboxesWrite11,
                                mailboxesWrite12, mailboxesWrite13,
                                mailboxesWrite14, mailboxesWrite15,
                                mailboxesRead1, mailboxesWrite16, decidedWrite,
                                decidedWrite0, decidedWrite1, decidedWrite2,
                                mailboxesWrite17, decidedWrite3,
                                electionInProgressRead, iAmTheLeaderRead,
                                mailboxesWrite18, mailboxesWrite19,
                                heartbeatFrequencyRead, sleeperWrite,
                                mailboxesWrite20, sleeperWrite0,
                                mailboxesWrite21, sleeperWrite1,
                                mailboxesRead2, lastSeenWrite,
                                mailboxesWrite22, lastSeenWrite0,
                                mailboxesWrite23, sleeperWrite2,
                                lastSeenWrite1, electionInProgressRead0,
                                iAmTheLeaderRead0, lastSeenRead,
                                timeoutCheckerRead, timeoutCheckerWrite,
                                timeoutCheckerWrite0, timeoutCheckerWrite1,
                                leaderFailureWrite, electionInProgressWrite10,
                                leaderFailureWrite0, electionInProgressWrite11,
                                timeoutCheckerWrite2, leaderFailureWrite1,
                                electionInProgressWrite12,
                                monitorFrequencyRead, sleeperWrite3,
                                timeoutCheckerWrite3, leaderFailureWrite2,
                                electionInProgressWrite13, sleeperWrite4,
                                requestsRead, requestsWrite, myIdRead, dbRead,
                                upstreamWrite, upstreamWrite0,
                                iAmTheLeaderRead1, proposerChanWrite,
                                paxosChanRead, proposerChanWrite0,
                                upstreamWrite1, proposerChanWrite1,
                                upstreamWrite2, requestsWrite0, upstreamWrite3,
                                proposerChanWrite2, learnerChanRead, kvIdRead,
                                dbWrite, kvIdRead0, kvIdRead1,
                                requestServiceWrite, requestServiceWrite0,
                                dbWrite0, requestServiceWrite1, b, s, elected,
                                acceptedValues_, max, index_, entry_, promises,
                                heartbeatMonitorId, accepts_, value, repropose,
                                resp, maxBal, loopIndex, acceptedValues,
                                payload, msg_, accepts, newAccepts,
                                numAccepted, iterator, entry, msg_l,
                                heartbeatFrequencyLocal, msg_h, index,
                                monitorFrequencyLocal, heartbeatId_, msg, null,
                                counter, requestId_, putOk, confirmedRequestId,
                                learnerId, operation, requestId >>

kvLoop(self) == /\ pc[self] = "kvLoop"
                /\ IF TRUE
                      THEN /\ (Cardinality(requestSet)) > (0)
                           /\ \E req0 \in requestSet:
                                /\ requestsWrite' = (requestSet) \ ({req0})
                                /\ requestsRead' = req0
                           /\ msg' = [msg EXCEPT ![self] = requestsRead']
                           /\ Assert((((msg'[self]).type) = (GET_MSG)) \/ (((msg'[self]).type) = (PUT_MSG)),
                                     "Failure of assertion at line 1136, column 17.")
                           /\ requestSet' = requestsWrite'
                           /\ pc' = [pc EXCEPT ![self] = "checkGet"]
                           /\ UNCHANGED << values, kvClient, requestsWrite0,
                                           upstreamWrite3, proposerChanWrite2 >>
                      ELSE /\ requestsWrite0' = requestSet
                           /\ upstreamWrite3' = kvClient
                           /\ proposerChanWrite2' = values
                           /\ requestSet' = requestsWrite0'
                           /\ kvClient' = upstreamWrite3'
                           /\ values' = proposerChanWrite2'
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << requestsRead, requestsWrite, msg >>
                /\ UNCHANGED << network, lastSeenAbstract, monitorLastSeen,
                                timeoutCheckerAbstract, sleeperAbstract,
                                idAbstract, learnedChan, paxosLayerChan,
                                database, electionInProgresssAbstract,
                                iAmTheLeaderAbstract, leaderFailureAbstract,
                                valueStreamRead, mailboxesWrite,
                                mailboxesWrite0, mailboxesRead,
                                iAmTheLeaderWrite, electionInProgressWrite,
                                leaderFailureRead, iAmTheLeaderWrite0,
                                electionInProgressWrite0, iAmTheLeaderWrite1,
                                electionInProgressWrite1, mailboxesWrite1,
                                iAmTheLeaderWrite2, electionInProgressWrite2,
                                mailboxesWrite2, iAmTheLeaderWrite3,
                                electionInProgressWrite3, iAmTheLeaderWrite4,
                                electionInProgressWrite4, mailboxesWrite3,
                                electionInProgressWrite5, mailboxesWrite4,
                                iAmTheLeaderWrite5, electionInProgressWrite6,
                                mailboxesWrite5, mailboxesWrite6,
                                iAmTheLeaderWrite6, electionInProgressWrite7,
                                mailboxesWrite7, iAmTheLeaderWrite7,
                                electionInProgressWrite8, mailboxesWrite8,
                                iAmTheLeaderWrite8, electionInProgressWrite9,
                                mailboxesRead0, mailboxesWrite9,
                                mailboxesWrite10, mailboxesWrite11,
                                mailboxesWrite12, mailboxesWrite13,
                                mailboxesWrite14, mailboxesWrite15,
                                mailboxesRead1, mailboxesWrite16, decidedWrite,
                                decidedWrite0, decidedWrite1, decidedWrite2,
                                mailboxesWrite17, decidedWrite3,
                                electionInProgressRead, iAmTheLeaderRead,
                                mailboxesWrite18, mailboxesWrite19,
                                heartbeatFrequencyRead, sleeperWrite,
                                mailboxesWrite20, sleeperWrite0,
                                mailboxesWrite21, sleeperWrite1,
                                mailboxesRead2, lastSeenWrite,
                                mailboxesWrite22, lastSeenWrite0,
                                mailboxesWrite23, sleeperWrite2,
                                lastSeenWrite1, electionInProgressRead0,
                                iAmTheLeaderRead0, lastSeenRead,
                                timeoutCheckerRead, timeoutCheckerWrite,
                                timeoutCheckerWrite0, timeoutCheckerWrite1,
                                leaderFailureWrite, electionInProgressWrite10,
                                leaderFailureWrite0, electionInProgressWrite11,
                                timeoutCheckerWrite2, leaderFailureWrite1,
                                electionInProgressWrite12,
                                monitorFrequencyRead, sleeperWrite3,
                                timeoutCheckerWrite3, leaderFailureWrite2,
                                electionInProgressWrite13, sleeperWrite4,
                                myIdRead, dbRead, upstreamWrite,
                                upstreamWrite0, iAmTheLeaderRead1,
                                proposerChanWrite, paxosChanRead,
                                proposerChanWrite0, upstreamWrite1,
                                proposerChanWrite1, upstreamWrite2,
                                learnerChanRead, kvIdRead, dbWrite, kvIdRead0,
                                kvIdRead1, requestServiceWrite,
                                requestServiceWrite0, dbWrite0,
                                requestServiceWrite1, b, s, elected,
                                acceptedValues_, max, index_, entry_, promises,
                                heartbeatMonitorId, accepts_, value, repropose,
                                resp, maxBal, loopIndex, acceptedValues,
                                payload, msg_, accepts, newAccepts,
                                numAccepted, iterator, entry, msg_l,
                                heartbeatFrequencyLocal, msg_h, index,
                                monitorFrequencyLocal, heartbeatId_, null,
                                heartbeatId, proposerId, counter, requestId_,
                                putOk, confirmedRequestId, learnerId,
                                operation, requestId >>

checkGet(self) == /\ pc[self] = "checkGet"
                  /\ IF ((msg[self]).type) = (GET_MSG)
                        THEN /\ myIdRead' = self
                             /\ dbRead' = database[<<myIdRead', (msg[self]).key>>]
                             /\ upstreamWrite' = [type |-> GET_RESPONSE_MSG, result |-> dbRead']
                             /\ upstreamWrite0' = upstreamWrite'
                             /\ kvClient' = upstreamWrite0'
                        ELSE /\ upstreamWrite0' = kvClient
                             /\ kvClient' = upstreamWrite0'
                             /\ UNCHANGED << myIdRead, dbRead, upstreamWrite >>
                  /\ pc' = [pc EXCEPT ![self] = "checkPut"]
                  /\ UNCHANGED << network, values, lastSeenAbstract,
                                  monitorLastSeen, timeoutCheckerAbstract,
                                  sleeperAbstract, idAbstract, requestSet,
                                  learnedChan, paxosLayerChan, database,
                                  electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesWrite14, mailboxesWrite15,
                                  mailboxesRead1, mailboxesWrite16,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, mailboxesWrite17,
                                  decidedWrite3, electionInProgressRead,
                                  iAmTheLeaderRead, mailboxesWrite18,
                                  mailboxesWrite19, heartbeatFrequencyRead,
                                  sleeperWrite, mailboxesWrite20,
                                  sleeperWrite0, mailboxesWrite21,
                                  sleeperWrite1, mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  mailboxesWrite23, sleeperWrite2,
                                  lastSeenWrite1, electionInProgressRead0,
                                  iAmTheLeaderRead0, lastSeenRead,
                                  timeoutCheckerRead, timeoutCheckerWrite,
                                  timeoutCheckerWrite0, timeoutCheckerWrite1,
                                  leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite,
                                  iAmTheLeaderRead1, proposerChanWrite,
                                  paxosChanRead, proposerChanWrite0,
                                  upstreamWrite1, proposerChanWrite1,
                                  upstreamWrite2, requestsWrite0,
                                  upstreamWrite3, proposerChanWrite2,
                                  learnerChanRead, kvIdRead, dbWrite,
                                  kvIdRead0, kvIdRead1, requestServiceWrite,
                                  requestServiceWrite0, dbWrite0,
                                  requestServiceWrite1, b, s, elected,
                                  acceptedValues_, max, index_, entry_,
                                  promises, heartbeatMonitorId, accepts_,
                                  value, repropose, resp, maxBal, loopIndex,
                                  acceptedValues, payload, msg_, accepts,
                                  newAccepts, numAccepted, iterator, entry,
                                  msg_l, heartbeatFrequencyLocal, msg_h, index,
                                  monitorFrequencyLocal, heartbeatId_, msg,
                                  null, heartbeatId, proposerId, counter,
                                  requestId_, putOk, confirmedRequestId,
                                  learnerId, operation, requestId >>

checkPut(self) == /\ pc[self] = "checkPut"
                  /\ IF ((msg[self]).type) = (PUT_MSG)
                        THEN /\ iAmTheLeaderRead1' = iAmTheLeaderAbstract[heartbeatId[self]]
                             /\ IF iAmTheLeaderRead1'
                                   THEN /\ requestId_' = [requestId_ EXCEPT ![self] = <<self, counter[self]>>]
                                        /\ ((values[proposerId[self]]).value) = (NULL)
                                        /\ proposerChanWrite' = [values EXCEPT ![proposerId[self]] = [id |-> requestId_'[self], key |-> (msg[self]).key, value |-> (msg[self]).value]]
                                        /\ values' = proposerChanWrite'
                                        /\ pc' = [pc EXCEPT ![self] = "putConfirm"]
                                        /\ UNCHANGED << kvClient,
                                                        upstreamWrite,
                                                        proposerChanWrite0,
                                                        upstreamWrite1,
                                                        proposerChanWrite1,
                                                        upstreamWrite2 >>
                                   ELSE /\ upstreamWrite' = [type |-> PUT_NOT_LEADER_MSG, result |-> null[self]]
                                        /\ proposerChanWrite0' = values
                                        /\ upstreamWrite1' = upstreamWrite'
                                        /\ proposerChanWrite1' = proposerChanWrite0'
                                        /\ upstreamWrite2' = upstreamWrite1'
                                        /\ kvClient' = upstreamWrite2'
                                        /\ values' = proposerChanWrite1'
                                        /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                                        /\ UNCHANGED << proposerChanWrite,
                                                        requestId_ >>
                        ELSE /\ proposerChanWrite1' = values
                             /\ upstreamWrite2' = kvClient
                             /\ kvClient' = upstreamWrite2'
                             /\ values' = proposerChanWrite1'
                             /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                             /\ UNCHANGED << upstreamWrite, iAmTheLeaderRead1,
                                             proposerChanWrite,
                                             proposerChanWrite0,
                                             upstreamWrite1, requestId_ >>
                  /\ UNCHANGED << network, lastSeenAbstract, monitorLastSeen,
                                  timeoutCheckerAbstract, sleeperAbstract,
                                  idAbstract, requestSet, learnedChan,
                                  paxosLayerChan, database,
                                  electionInProgresssAbstract,
                                  iAmTheLeaderAbstract, leaderFailureAbstract,
                                  valueStreamRead, mailboxesWrite,
                                  mailboxesWrite0, mailboxesRead,
                                  iAmTheLeaderWrite, electionInProgressWrite,
                                  leaderFailureRead, iAmTheLeaderWrite0,
                                  electionInProgressWrite0, iAmTheLeaderWrite1,
                                  electionInProgressWrite1, mailboxesWrite1,
                                  iAmTheLeaderWrite2, electionInProgressWrite2,
                                  mailboxesWrite2, iAmTheLeaderWrite3,
                                  electionInProgressWrite3, iAmTheLeaderWrite4,
                                  electionInProgressWrite4, mailboxesWrite3,
                                  electionInProgressWrite5, mailboxesWrite4,
                                  iAmTheLeaderWrite5, electionInProgressWrite6,
                                  mailboxesWrite5, mailboxesWrite6,
                                  iAmTheLeaderWrite6, electionInProgressWrite7,
                                  mailboxesWrite7, iAmTheLeaderWrite7,
                                  electionInProgressWrite8, mailboxesWrite8,
                                  iAmTheLeaderWrite8, electionInProgressWrite9,
                                  mailboxesRead0, mailboxesWrite9,
                                  mailboxesWrite10, mailboxesWrite11,
                                  mailboxesWrite12, mailboxesWrite13,
                                  mailboxesWrite14, mailboxesWrite15,
                                  mailboxesRead1, mailboxesWrite16,
                                  decidedWrite, decidedWrite0, decidedWrite1,
                                  decidedWrite2, mailboxesWrite17,
                                  decidedWrite3, electionInProgressRead,
                                  iAmTheLeaderRead, mailboxesWrite18,
                                  mailboxesWrite19, heartbeatFrequencyRead,
                                  sleeperWrite, mailboxesWrite20,
                                  sleeperWrite0, mailboxesWrite21,
                                  sleeperWrite1, mailboxesRead2, lastSeenWrite,
                                  mailboxesWrite22, lastSeenWrite0,
                                  mailboxesWrite23, sleeperWrite2,
                                  lastSeenWrite1, electionInProgressRead0,
                                  iAmTheLeaderRead0, lastSeenRead,
                                  timeoutCheckerRead, timeoutCheckerWrite,
                                  timeoutCheckerWrite0, timeoutCheckerWrite1,
                                  leaderFailureWrite,
                                  electionInProgressWrite10,
                                  leaderFailureWrite0,
                                  electionInProgressWrite11,
                                  timeoutCheckerWrite2, leaderFailureWrite1,
                                  electionInProgressWrite12,
                                  monitorFrequencyRead, sleeperWrite3,
                                  timeoutCheckerWrite3, leaderFailureWrite2,
                                  electionInProgressWrite13, sleeperWrite4,
                                  requestsRead, requestsWrite, myIdRead,
                                  dbRead, upstreamWrite0, paxosChanRead,
                                  requestsWrite0, upstreamWrite3,
                                  proposerChanWrite2, learnerChanRead,
                                  kvIdRead, dbWrite, kvIdRead0, kvIdRead1,
                                  requestServiceWrite, requestServiceWrite0,
                                  dbWrite0, requestServiceWrite1, b, s,
                                  elected, acceptedValues_, max, index_,
                                  entry_, promises, heartbeatMonitorId,
                                  accepts_, value, repropose, resp, maxBal,
                                  loopIndex, acceptedValues, payload, msg_,
                                  accepts, newAccepts, numAccepted, iterator,
                                  entry, msg_l, heartbeatFrequencyLocal, msg_h,
                                  index, monitorFrequencyLocal, heartbeatId_,
                                  msg, null, heartbeatId, proposerId, counter,
                                  putOk, confirmedRequestId, learnerId,
                                  operation, requestId >>

putConfirm(self) == /\ pc[self] = "putConfirm"
                    /\ ((paxosLayerChan[self]).value) # (NULL)
                    /\ LET v1 == paxosLayerChan[self] IN
                         /\ paxosLayerChan' = [paxosLayerChan EXCEPT ![self].value = NULL]
                         /\ paxosChanRead' = v1
                    /\ putOk' = [putOk EXCEPT ![self] = paxosChanRead']
                    /\ confirmedRequestId' = [confirmedRequestId EXCEPT ![self] = (putOk'[self]).id]
                    /\ Assert(((confirmedRequestId'[self][1]) = (self)) /\ ((confirmedRequestId'[self][2]) = (counter[self])),
                              "Failure of assertion at line 1166, column 33.")
                    /\ upstreamWrite' = [type |-> PUT_OK_MSG, result |-> null[self]]
                    /\ counter' = [counter EXCEPT ![self] = (counter[self]) + (1)]
                    /\ kvClient' = upstreamWrite'
                    /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                    /\ UNCHANGED << network, values, lastSeenAbstract,
                                    monitorLastSeen, timeoutCheckerAbstract,
                                    sleeperAbstract, idAbstract, requestSet,
                                    learnedChan, database,
                                    electionInProgresssAbstract,
                                    iAmTheLeaderAbstract,
                                    leaderFailureAbstract, valueStreamRead,
                                    mailboxesWrite, mailboxesWrite0,
                                    mailboxesRead, iAmTheLeaderWrite,
                                    electionInProgressWrite, leaderFailureRead,
                                    iAmTheLeaderWrite0,
                                    electionInProgressWrite0,
                                    iAmTheLeaderWrite1,
                                    electionInProgressWrite1, mailboxesWrite1,
                                    iAmTheLeaderWrite2,
                                    electionInProgressWrite2, mailboxesWrite2,
                                    iAmTheLeaderWrite3,
                                    electionInProgressWrite3,
                                    iAmTheLeaderWrite4,
                                    electionInProgressWrite4, mailboxesWrite3,
                                    electionInProgressWrite5, mailboxesWrite4,
                                    iAmTheLeaderWrite5,
                                    electionInProgressWrite6, mailboxesWrite5,
                                    mailboxesWrite6, iAmTheLeaderWrite6,
                                    electionInProgressWrite7, mailboxesWrite7,
                                    iAmTheLeaderWrite7,
                                    electionInProgressWrite8, mailboxesWrite8,
                                    iAmTheLeaderWrite8,
                                    electionInProgressWrite9, mailboxesRead0,
                                    mailboxesWrite9, mailboxesWrite10,
                                    mailboxesWrite11, mailboxesWrite12,
                                    mailboxesWrite13, mailboxesWrite14,
                                    mailboxesWrite15, mailboxesRead1,
                                    mailboxesWrite16, decidedWrite,
                                    decidedWrite0, decidedWrite1,
                                    decidedWrite2, mailboxesWrite17,
                                    decidedWrite3, electionInProgressRead,
                                    iAmTheLeaderRead, mailboxesWrite18,
                                    mailboxesWrite19, heartbeatFrequencyRead,
                                    sleeperWrite, mailboxesWrite20,
                                    sleeperWrite0, mailboxesWrite21,
                                    sleeperWrite1, mailboxesRead2,
                                    lastSeenWrite, mailboxesWrite22,
                                    lastSeenWrite0, mailboxesWrite23,
                                    sleeperWrite2, lastSeenWrite1,
                                    electionInProgressRead0, iAmTheLeaderRead0,
                                    lastSeenRead, timeoutCheckerRead,
                                    timeoutCheckerWrite, timeoutCheckerWrite0,
                                    timeoutCheckerWrite1, leaderFailureWrite,
                                    electionInProgressWrite10,
                                    leaderFailureWrite0,
                                    electionInProgressWrite11,
                                    timeoutCheckerWrite2, leaderFailureWrite1,
                                    electionInProgressWrite12,
                                    monitorFrequencyRead, sleeperWrite3,
                                    timeoutCheckerWrite3, leaderFailureWrite2,
                                    electionInProgressWrite13, sleeperWrite4,
                                    requestsRead, requestsWrite, myIdRead,
                                    dbRead, upstreamWrite0, iAmTheLeaderRead1,
                                    proposerChanWrite, proposerChanWrite0,
                                    upstreamWrite1, proposerChanWrite1,
                                    upstreamWrite2, requestsWrite0,
                                    upstreamWrite3, proposerChanWrite2,
                                    learnerChanRead, kvIdRead, dbWrite,
                                    kvIdRead0, kvIdRead1, requestServiceWrite,
                                    requestServiceWrite0, dbWrite0,
                                    requestServiceWrite1, b, s, elected,
                                    acceptedValues_, max, index_, entry_,
                                    promises, heartbeatMonitorId, accepts_,
                                    value, repropose, resp, maxBal, loopIndex,
                                    acceptedValues, payload, msg_, accepts,
                                    newAccepts, numAccepted, iterator, entry,
                                    msg_l, heartbeatFrequencyLocal, msg_h,
                                    index, monitorFrequencyLocal, heartbeatId_,
                                    msg, null, heartbeatId, proposerId,
                                    requestId_, learnerId, operation,
                                    requestId >>

kvRequests(self) == kvInit(self) \/ kvLoop(self) \/ checkGet(self)
                       \/ checkPut(self) \/ putConfirm(self)

findId(self) == /\ pc[self] = "findId"
                /\ learnerId' = [learnerId EXCEPT ![self] = (self) - ((4) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                /\ UNCHANGED << network, values, lastSeenAbstract,
                                monitorLastSeen, timeoutCheckerAbstract,
                                sleeperAbstract, kvClient, idAbstract,
                                requestSet, learnedChan, paxosLayerChan,
                                database, electionInProgresssAbstract,
                                iAmTheLeaderAbstract, leaderFailureAbstract,
                                valueStreamRead, mailboxesWrite,
                                mailboxesWrite0, mailboxesRead,
                                iAmTheLeaderWrite, electionInProgressWrite,
                                leaderFailureRead, iAmTheLeaderWrite0,
                                electionInProgressWrite0, iAmTheLeaderWrite1,
                                electionInProgressWrite1, mailboxesWrite1,
                                iAmTheLeaderWrite2, electionInProgressWrite2,
                                mailboxesWrite2, iAmTheLeaderWrite3,
                                electionInProgressWrite3, iAmTheLeaderWrite4,
                                electionInProgressWrite4, mailboxesWrite3,
                                electionInProgressWrite5, mailboxesWrite4,
                                iAmTheLeaderWrite5, electionInProgressWrite6,
                                mailboxesWrite5, mailboxesWrite6,
                                iAmTheLeaderWrite6, electionInProgressWrite7,
                                mailboxesWrite7, iAmTheLeaderWrite7,
                                electionInProgressWrite8, mailboxesWrite8,
                                iAmTheLeaderWrite8, electionInProgressWrite9,
                                mailboxesRead0, mailboxesWrite9,
                                mailboxesWrite10, mailboxesWrite11,
                                mailboxesWrite12, mailboxesWrite13,
                                mailboxesWrite14, mailboxesWrite15,
                                mailboxesRead1, mailboxesWrite16, decidedWrite,
                                decidedWrite0, decidedWrite1, decidedWrite2,
                                mailboxesWrite17, decidedWrite3,
                                electionInProgressRead, iAmTheLeaderRead,
                                mailboxesWrite18, mailboxesWrite19,
                                heartbeatFrequencyRead, sleeperWrite,
                                mailboxesWrite20, sleeperWrite0,
                                mailboxesWrite21, sleeperWrite1,
                                mailboxesRead2, lastSeenWrite,
                                mailboxesWrite22, lastSeenWrite0,
                                mailboxesWrite23, sleeperWrite2,
                                lastSeenWrite1, electionInProgressRead0,
                                iAmTheLeaderRead0, lastSeenRead,
                                timeoutCheckerRead, timeoutCheckerWrite,
                                timeoutCheckerWrite0, timeoutCheckerWrite1,
                                leaderFailureWrite, electionInProgressWrite10,
                                leaderFailureWrite0, electionInProgressWrite11,
                                timeoutCheckerWrite2, leaderFailureWrite1,
                                electionInProgressWrite12,
                                monitorFrequencyRead, sleeperWrite3,
                                timeoutCheckerWrite3, leaderFailureWrite2,
                                electionInProgressWrite13, sleeperWrite4,
                                requestsRead, requestsWrite, myIdRead, dbRead,
                                upstreamWrite, upstreamWrite0,
                                iAmTheLeaderRead1, proposerChanWrite,
                                paxosChanRead, proposerChanWrite0,
                                upstreamWrite1, proposerChanWrite1,
                                upstreamWrite2, requestsWrite0, upstreamWrite3,
                                proposerChanWrite2, learnerChanRead, kvIdRead,
                                dbWrite, kvIdRead0, kvIdRead1,
                                requestServiceWrite, requestServiceWrite0,
                                dbWrite0, requestServiceWrite1, b, s, elected,
                                acceptedValues_, max, index_, entry_, promises,
                                heartbeatMonitorId, accepts_, value, repropose,
                                resp, maxBal, loopIndex, acceptedValues,
                                payload, msg_, accepts, newAccepts,
                                numAccepted, iterator, entry, msg_l,
                                heartbeatFrequencyLocal, msg_h, index,
                                monitorFrequencyLocal, heartbeatId_, msg, null,
                                heartbeatId, proposerId, counter, requestId_,
                                putOk, confirmedRequestId, operation,
                                requestId >>

kvManagerLoop(self) == /\ pc[self] = "kvManagerLoop"
                       /\ IF TRUE
                             THEN /\ ((learnedChan[learnerId[self]]).value) # (NULL)
                                  /\ LET v2 == learnedChan[learnerId[self]] IN
                                       /\ learnedChan' = [learnedChan EXCEPT ![learnerId[self]].value = NULL]
                                       /\ learnerChanRead' = v2
                                  /\ operation' = [operation EXCEPT ![self] = learnerChanRead']
                                  /\ requestId' = [requestId EXCEPT ![self] = (operation'[self]).id]
                                  /\ kvIdRead' = (self) - (NUM_NODES)
                                  /\ dbWrite' = [database EXCEPT ![<<kvIdRead', (operation'[self]).key>>] = (operation'[self]).value]
                                  /\ kvIdRead0' = (self) - (NUM_NODES)
                                  /\ IF (requestId'[self][1]) = (kvIdRead0')
                                        THEN /\ kvIdRead1' = (self) - (NUM_NODES)
                                             /\ ((paxosLayerChan[kvIdRead1']).value) = (NULL)
                                             /\ requestServiceWrite' = [paxosLayerChan EXCEPT ![kvIdRead1'] = operation'[self]]
                                             /\ requestServiceWrite0' = requestServiceWrite'
                                             /\ dbWrite0' = dbWrite'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ database' = dbWrite0'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                        ELSE /\ requestServiceWrite0' = paxosLayerChan
                                             /\ dbWrite0' = dbWrite'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ database' = dbWrite0'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                             /\ UNCHANGED << kvIdRead1,
                                                             requestServiceWrite >>
                             ELSE /\ dbWrite0' = database
                                  /\ requestServiceWrite1' = paxosLayerChan
                                  /\ paxosLayerChan' = requestServiceWrite1'
                                  /\ database' = dbWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << learnedChan, learnerChanRead,
                                                  kvIdRead, dbWrite, kvIdRead0,
                                                  kvIdRead1,
                                                  requestServiceWrite,
                                                  requestServiceWrite0,
                                                  operation, requestId >>
                       /\ UNCHANGED << network, values, lastSeenAbstract,
                                       monitorLastSeen, timeoutCheckerAbstract,
                                       sleeperAbstract, kvClient, idAbstract,
                                       requestSet, electionInProgresssAbstract,
                                       iAmTheLeaderAbstract,
                                       leaderFailureAbstract, valueStreamRead,
                                       mailboxesWrite, mailboxesWrite0,
                                       mailboxesRead, iAmTheLeaderWrite,
                                       electionInProgressWrite,
                                       leaderFailureRead, iAmTheLeaderWrite0,
                                       electionInProgressWrite0,
                                       iAmTheLeaderWrite1,
                                       electionInProgressWrite1,
                                       mailboxesWrite1, iAmTheLeaderWrite2,
                                       electionInProgressWrite2,
                                       mailboxesWrite2, iAmTheLeaderWrite3,
                                       electionInProgressWrite3,
                                       iAmTheLeaderWrite4,
                                       electionInProgressWrite4,
                                       mailboxesWrite3,
                                       electionInProgressWrite5,
                                       mailboxesWrite4, iAmTheLeaderWrite5,
                                       electionInProgressWrite6,
                                       mailboxesWrite5, mailboxesWrite6,
                                       iAmTheLeaderWrite6,
                                       electionInProgressWrite7,
                                       mailboxesWrite7, iAmTheLeaderWrite7,
                                       electionInProgressWrite8,
                                       mailboxesWrite8, iAmTheLeaderWrite8,
                                       electionInProgressWrite9,
                                       mailboxesRead0, mailboxesWrite9,
                                       mailboxesWrite10, mailboxesWrite11,
                                       mailboxesWrite12, mailboxesWrite13,
                                       mailboxesWrite14, mailboxesWrite15,
                                       mailboxesRead1, mailboxesWrite16,
                                       decidedWrite, decidedWrite0,
                                       decidedWrite1, decidedWrite2,
                                       mailboxesWrite17, decidedWrite3,
                                       electionInProgressRead,
                                       iAmTheLeaderRead, mailboxesWrite18,
                                       mailboxesWrite19,
                                       heartbeatFrequencyRead, sleeperWrite,
                                       mailboxesWrite20, sleeperWrite0,
                                       mailboxesWrite21, sleeperWrite1,
                                       mailboxesRead2, lastSeenWrite,
                                       mailboxesWrite22, lastSeenWrite0,
                                       mailboxesWrite23, sleeperWrite2,
                                       lastSeenWrite1, electionInProgressRead0,
                                       iAmTheLeaderRead0, lastSeenRead,
                                       timeoutCheckerRead, timeoutCheckerWrite,
                                       timeoutCheckerWrite0,
                                       timeoutCheckerWrite1,
                                       leaderFailureWrite,
                                       electionInProgressWrite10,
                                       leaderFailureWrite0,
                                       electionInProgressWrite11,
                                       timeoutCheckerWrite2,
                                       leaderFailureWrite1,
                                       electionInProgressWrite12,
                                       monitorFrequencyRead, sleeperWrite3,
                                       timeoutCheckerWrite3,
                                       leaderFailureWrite2,
                                       electionInProgressWrite13,
                                       sleeperWrite4, requestsRead,
                                       requestsWrite, myIdRead, dbRead,
                                       upstreamWrite, upstreamWrite0,
                                       iAmTheLeaderRead1, proposerChanWrite,
                                       paxosChanRead, proposerChanWrite0,
                                       upstreamWrite1, proposerChanWrite1,
                                       upstreamWrite2, requestsWrite0,
                                       upstreamWrite3, proposerChanWrite2, b,
                                       s, elected, acceptedValues_, max,
                                       index_, entry_, promises,
                                       heartbeatMonitorId, accepts_, value,
                                       repropose, resp, maxBal, loopIndex,
                                       acceptedValues, payload, msg_, accepts,
                                       newAccepts, numAccepted, iterator,
                                       entry, msg_l, heartbeatFrequencyLocal,
                                       msg_h, index, monitorFrequencyLocal,
                                       heartbeatId_, msg, null, heartbeatId,
                                       proposerId, counter, requestId_, putOk,
                                       confirmedRequestId, learnerId >>

kvPaxosManager(self) == findId(self) \/ kvManagerLoop(self)

Next == (\E self \in Proposer: proposer(self))
           \/ (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Learner: learner(self))
           \/ (\E self \in Heartbeat: heartbeatAction(self))
           \/ (\E self \in LeaderMonitor: leaderStatusMonitor(self))
           \/ (\E self \in KVRequests: kvRequests(self))
           \/ (\E self \in KVPaxosManager: kvPaxosManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proposer : WF_vars(proposer(self))
        /\ \A self \in Acceptor : WF_vars(acceptor(self))
        /\ \A self \in Learner : WF_vars(learner(self))
        /\ \A self \in Heartbeat : WF_vars(heartbeatAction(self))
        /\ \A self \in LeaderMonitor : WF_vars(leaderStatusMonitor(self))
        /\ \A self \in KVRequests : WF_vars(kvRequests(self))
        /\ \A self \in KVPaxosManager : WF_vars(kvPaxosManager(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\*  Every KV node has a consistent database
ConsistentDatabase == \A kv1, kv2 \in KVRequests, k \in PutSet :
                          database[kv1, k] # NULL /\ database[kv2, k] # NULL => database[kv1, k] = database[kv2, k]

\* Put requests are eventually consumed by proposers
EventuallyConsumeValue == LET putRequests == { [type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet }
                          IN
                            <>(\E p \in Proposer, req \in putRequests : value[p] # defaultInitValue /\ value[p].key = req.key /\ value[p].value = req.value)

\* A leader is eventually elected
EventuallyElected == \E p \in Proposer : <>(elected[p])

\* Eventually the database of every node is populated with the associated value
Progress == \A kv \in KVRequests, k \in PutSet : <>(database[kv, k] = k)

\* Invariant
THEOREM Spec => []ConsistentDatabase

\* Temporal properties
THEOREM Spec => /\ EventuallyConsumeValue
                /\ EventuallyElected
                /\ Progress

=========================================================
