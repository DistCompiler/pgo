----------------------------------- MODULE consensus_kv ---------------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NUM_NODES
ASSUME NUM_NODES \in Nat

CONSTANT NULL, NULL_DB_VALUE
ASSUME NULL \notin Nat /\ NULL_DB_VALUE # NULL

FiniteNaturalSet(s) == IsFiniteSet(s) /\ (\A e \in s : e \in Nat)
CONSTANTS GetSet, PutSet
ASSUME FiniteNaturalSet(GetSet) /\ FiniteNaturalSet(PutSet)

(***************************************************************************
--mpcal ConsensusKV {
  define {
      \* maintain process identifers from Paxos spec for interoperability with Paxos model
      Proposer       == 0..NUM_NODES-1
      Learner        == (2*NUM_NODES)..(3*NUM_NODES-1)
      Heartbeat      == (3*NUM_NODES)..(4*NUM_NODES-1)
      KVRequests     == (5*NUM_NODES)..(6*NUM_NODES-1)
      KVPaxosManager == (6*NUM_NODES)..(7*NUM_NODES-1)
      ConsensusSet   == (7*NUM_NODES)..(8*NUM_NODES-1)

      GET_MSG            == "get_msg"
      PUT_MSG            == "put_msg"
      GET_RESPONSE_MSG   == "get_response_msg"
      NOT_LEADER_MSG     == "not_leader_msg"
      OK_MSG             == "ok_msg"

      GET == "get"
      PUT == "put"

  }

  mapping macro SelfManager {
      read  { yield self - NUM_NODES; }
      write { assert(FALSE); yield $value; }
  }

  \* defines semantics of unbuffered Go channels for records with a `value` field
  mapping macro UnbufferedRecordChannel {
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

  \* defines semantics of unbuffered Go channels for integers
  mapping macro UnbufferedIntChannel {
      read {
          await $variable # NULL;
          with (v = $variable) {
              $variable := NULL;
              yield v;
          }
      }

      write {
          await $variable  = NULL;
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

  mapping macro Identity {
      read  { yield $variable; }
      write { yield $value; }
  }

  mapping macro SetAdd {
      read  {
          assert(FALSE);
          yield $variable;
      }

      write {
          yield $variable \union {$value};
      }
  }

  archetype Consensus(proposerChan, ref learnerChan)
  variables msg, learnerId, proposerId;
  {
      findIds:
          proposerId := self - 7*NUM_NODES;
          learnerId := self - 5*NUM_NODES;

      consensusLoop:
        while (TRUE) {
            msg := proposerChan[proposerId];
            learnerChan[learnerId] := msg;
        }
  }

  archetype KeyValueRequests(requests, ref upstream, iAmTheLeader, ref proposerChan, paxosChan)
  variables msg, null, heartbeatId, proposerId, counter = 0, requestId, proposal, result;
  {
      kvInit:
        heartbeatId := self - 2*NUM_NODES;
        proposerId := self - 5*NUM_NODES;

      kvLoop:
        while (TRUE) {
            msg := requests;
            assert(msg.type = GET_MSG \/ msg.type = PUT_MSG);

            if (iAmTheLeader[heartbeatId]) {
                \* request that this operation be proposed by the underlying proposer

                \* unique request identifier
                requestId := << self, counter >>;

                if (msg.type = GET_MSG) {
                    proposal := [operation |-> GET, id |-> requestId, key |-> msg.key, value |-> msg.key];
                } else {
                    proposal := [operation |-> PUT, id |-> requestId, key |-> msg.key, value |-> msg.value];
                };

                proposerChan[proposerId] := proposal;

                \* Known limitation: the current may no longer be the leader by the time the key-value
                \* node sends the proposal. We need a way to receive a notification from the proposer that
                \* the we are no longer the leader.
                requestConfirm:
                  result := paxosChan[self];

                  upstream := [type |-> OK_MSG, result |-> result];
                  counter := counter + 1;
            } else {
                notLeader:
                  upstream := [type |-> NOT_LEADER_MSG, result |-> null];
            }
        }
  }

  archetype KeyValuePaxosManager(ref requestService, learnerChan, ref db)
  variables result, learnerId, decided, kvId;
  {
      findId:
        learnerId := self - 4*NUM_NODES;
        kvId := self - NUM_NODES;

      kvManagerLoop:
        while (TRUE) {
            \* wait for a value to be informed by the learner
            decided := learnerChan[learnerId];

            \* always update the database if it's a PUT request, regardless of whether
            \* this instance issued the request
            if (decided.operation = PUT) {
                db[decided.key] := decided.value;
            };

            \* only send the result to the request service if we issued the request
            if (decided.id[1] = kvId) {
                \* read value from the database and return result
                if (decided.operation = GET) {
                    result := db[decided.key];
                } else {
                    result := decided.value;
                };

                requestService[kvId] := result;
            };
        }
  }

  variables
        values = [k \in Proposer |-> [value |-> NULL]],

        \* requests to be sent by the client
        requestSet = { [type |-> GET_MSG, key |-> k, value |-> k] : k \in GetSet } \union
                     { [type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet},

        learnedChan = [l \in Learner |-> [value |-> NULL]],
        paxosLayerChan = [p \in KVRequests |-> NULL],

        kvClient = {},
        idAbstract,

        iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE];

    fair process (kvRequests \in KVRequests) == instance KeyValueRequests(requestSet, ref kvClient, iAmTheLeaderAbstract, values, paxosLayerChan)
        mapping requestSet via NextRequest
        mapping kvClient via SetAdd
        mapping iAmTheLeaderAbstract[_] via Identity
        mapping values[_] via UnbufferedRecordChannel
        mapping paxosLayerChan[_] via UnbufferedIntChannel;

    fair process (kvPaxosManager \in KVPaxosManager) == instance KeyValuePaxosManager(ref paxosLayerChan, learnedChan, [k \in GetSet \union PutSet |-> NULL_DB_VALUE])
        mapping paxosLayerChan[_] via UnbufferedIntChannel
        mapping learnedChan[_] via UnbufferedRecordChannel
        mapping @3[_] via Identity;

    fair process (consensus \in ConsensusSet) == instance Consensus(values, learnedChan)
        mapping values[_] via UnbufferedRecordChannel
        mapping learnedChan[_] via UnbufferedRecordChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ConsensusKV {
    variables values = [k \in Proposer |-> [value |-> NULL]], requestSet = ({[type |-> GET_MSG, key |-> k, value |-> k] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}), learnedChan = [l \in Learner |-> [value |-> NULL]], paxosLayerChan = [p \in KVRequests |-> NULL], kvClient = {}, idAbstract, iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE], requestsRead, requestsWrite, iAmTheLeaderRead, proposerChanWrite, paxosChanRead, paxosChanWrite, upstreamWrite, proposerChanWrite0, paxosChanWrite0, upstreamWrite0, requestsWrite0, proposerChanWrite1, paxosChanWrite1, upstreamWrite1, learnerChanRead, dbWrite, dbWrite0, dbRead, requestServiceWrite, requestServiceWrite0, dbWrite1, requestServiceWrite1, proposerChanRead, learnerChanWrite, learnerChanWrite0;
    define {
        Proposer == (0) .. ((NUM_NODES) - (1))
        Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
        Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
        KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
        KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
        ConsensusSet == ((7) * (NUM_NODES)) .. (((8) * (NUM_NODES)) - (1))
        GET_MSG == "get_msg"
        PUT_MSG == "put_msg"
        GET_RESPONSE_MSG == "get_response_msg"
        NOT_LEADER_MSG == "not_leader_msg"
        OK_MSG == "ok_msg"
        GET == "get"
        PUT == "put"
    }
    fair process (kvRequests \in KVRequests)
    variables msg, null, heartbeatId, proposerId, counter = 0, requestId, proposal, result;
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
                iAmTheLeaderRead := iAmTheLeaderAbstract[heartbeatId];
                if (iAmTheLeaderRead) {
                    requestId := <<self, counter>>;
                    if (((msg).type) = (GET_MSG)) {
                        proposal := [operation |-> GET, id |-> requestId, key |-> (msg).key, value |-> (msg).key];
                    } else {
                        proposal := [operation |-> PUT, id |-> requestId, key |-> (msg).key, value |-> (msg).value];
                    };
                    await ((values[proposerId]).value) = (NULL);
                    proposerChanWrite := [values EXCEPT ![proposerId] = proposal];
                    requestSet := requestsWrite;
                    values := proposerChanWrite;
                    requestConfirm:
                        await (paxosLayerChan[self]) # (NULL);
                        with (v0 = paxosLayerChan[self]) {
                            paxosChanWrite := [paxosLayerChan EXCEPT ![self] = NULL];
                            paxosChanRead := v0;
                        };
                        result := paxosChanRead;
                        upstreamWrite := (kvClient) \union ({[type |-> OK_MSG, result |-> result]});
                        counter := (counter) + (1);
                        kvClient := upstreamWrite;
                        paxosLayerChan := paxosChanWrite;
                        goto kvLoop;

                } else {
                    requestSet := requestsWrite;
                    notLeader:
                        upstreamWrite := (kvClient) \union ({[type |-> NOT_LEADER_MSG, result |-> null]});
                        kvClient := upstreamWrite;
                        goto kvLoop;

                };
            } else {
                requestsWrite0 := requestSet;
                proposerChanWrite1 := values;
                paxosChanWrite1 := paxosLayerChan;
                upstreamWrite1 := kvClient;
                requestSet := requestsWrite0;
                kvClient := upstreamWrite1;
                values := proposerChanWrite1;
                paxosLayerChan := paxosChanWrite1;
            };

    }
    fair process (kvPaxosManager \in KVPaxosManager)
    variables dbLocal = [k \in (GetSet) \union (PutSet) |-> NULL_DB_VALUE], result, learnerId, decided, kvId;
    {
        findId:
            learnerId := (self) - ((4) * (NUM_NODES));
            kvId := (self) - (NUM_NODES);
        kvManagerLoop:
            if (TRUE) {
                await ((learnedChan[learnerId]).value) # (NULL);
                with (v1 = learnedChan[learnerId]) {
                    learnedChan[learnerId].value := NULL;
                    learnerChanRead := v1;
                };
                decided := learnerChanRead;
                if (((decided).operation) = (PUT)) {
                    dbWrite := [dbLocal EXCEPT ![(decided).key] = (decided).value];
                    dbWrite0 := dbWrite;
                } else {
                    dbWrite0 := dbLocal;
                };
                if (((decided).id[1]) = (kvId)) {
                    if (((decided).operation) = (GET)) {
                        dbRead := dbWrite0[(decided).key];
                        result := dbRead;
                    } else {
                        result := (decided).value;
                    };
                    await (paxosLayerChan[kvId]) = (NULL);
                    requestServiceWrite := [paxosLayerChan EXCEPT ![kvId] = result];
                    requestServiceWrite0 := requestServiceWrite;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    dbLocal := dbWrite1;
                    goto kvManagerLoop;
                } else {
                    requestServiceWrite0 := paxosLayerChan;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    dbLocal := dbWrite1;
                    goto kvManagerLoop;
                };
            } else {
                dbWrite1 := dbLocal;
                requestServiceWrite1 := paxosLayerChan;
                paxosLayerChan := requestServiceWrite1;
                dbLocal := dbWrite1;
            };

    }
    fair process (consensus \in ConsensusSet)
    variables msg, learnerId, proposerId;
    {
        findIds:
            proposerId := (self) - ((7) * (NUM_NODES));
            learnerId := (self) - ((5) * (NUM_NODES));
        consensusLoop:
            if (TRUE) {
                await ((values[proposerId]).value) # (NULL);
                with (v2 = values[proposerId]) {
                    values[proposerId].value := NULL;
                    proposerChanRead := v2;
                };
                msg := proposerChanRead;
                await ((learnedChan[learnerId]).value) = (NULL);
                learnerChanWrite := [learnedChan EXCEPT ![learnerId] = msg];
                learnerChanWrite0 := learnerChanWrite;
                learnedChan := learnerChanWrite0;
                goto consensusLoop;
            } else {
                learnerChanWrite0 := learnedChan;
                learnedChan := learnerChanWrite0;
            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)

\* BEGIN TRANSLATION
\* Process variable msg of process kvRequests at line 240 col 15 changed to msg_
\* Process variable proposerId of process kvRequests at line 240 col 39 changed to proposerId_
\* Process variable result of process kvRequests at line 240 col 85 changed to result_
\* Process variable learnerId of process kvPaxosManager at line 300 col 85 changed to learnerId_
CONSTANT defaultInitValue
VARIABLES values, requestSet, learnedChan, paxosLayerChan, kvClient,
          idAbstract, iAmTheLeaderAbstract, requestsRead, requestsWrite,
          iAmTheLeaderRead, proposerChanWrite, paxosChanRead, paxosChanWrite,
          upstreamWrite, proposerChanWrite0, paxosChanWrite0, upstreamWrite0,
          requestsWrite0, proposerChanWrite1, paxosChanWrite1, upstreamWrite1,
          learnerChanRead, dbWrite, dbWrite0, dbRead, requestServiceWrite,
          requestServiceWrite0, dbWrite1, requestServiceWrite1,
          proposerChanRead, learnerChanWrite, learnerChanWrite0, pc

(* define statement *)
Proposer == (0) .. ((NUM_NODES) - (1))
Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
ConsensusSet == ((7) * (NUM_NODES)) .. (((8) * (NUM_NODES)) - (1))
GET_MSG == "get_msg"
PUT_MSG == "put_msg"
GET_RESPONSE_MSG == "get_response_msg"
NOT_LEADER_MSG == "not_leader_msg"
OK_MSG == "ok_msg"
GET == "get"
PUT == "put"

VARIABLES msg_, null, heartbeatId, proposerId_, counter, requestId, proposal,
          result_, dbLocal, result, learnerId_, decided, kvId, msg, learnerId,
          proposerId

vars == << values, requestSet, learnedChan, paxosLayerChan, kvClient,
           idAbstract, iAmTheLeaderAbstract, requestsRead, requestsWrite,
           iAmTheLeaderRead, proposerChanWrite, paxosChanRead, paxosChanWrite,
           upstreamWrite, proposerChanWrite0, paxosChanWrite0, upstreamWrite0,
           requestsWrite0, proposerChanWrite1, paxosChanWrite1,
           upstreamWrite1, learnerChanRead, dbWrite, dbWrite0, dbRead,
           requestServiceWrite, requestServiceWrite0, dbWrite1,
           requestServiceWrite1, proposerChanRead, learnerChanWrite,
           learnerChanWrite0, pc, msg_, null, heartbeatId, proposerId_,
           counter, requestId, proposal, result_, dbLocal, result, learnerId_,
           decided, kvId, msg, learnerId, proposerId >>

ProcSet == (KVRequests) \cup (KVPaxosManager) \cup (ConsensusSet)

Init == (* Global variables *)
        /\ values = [k \in Proposer |-> [value |-> NULL]]
        /\ requestSet = (({[type |-> GET_MSG, key |-> k, value |-> k] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}))
        /\ learnedChan = [l \in Learner |-> [value |-> NULL]]
        /\ paxosLayerChan = [p \in KVRequests |-> NULL]
        /\ kvClient = {}
        /\ idAbstract = defaultInitValue
        /\ iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE]
        /\ requestsRead = defaultInitValue
        /\ requestsWrite = defaultInitValue
        /\ iAmTheLeaderRead = defaultInitValue
        /\ proposerChanWrite = defaultInitValue
        /\ paxosChanRead = defaultInitValue
        /\ paxosChanWrite = defaultInitValue
        /\ upstreamWrite = defaultInitValue
        /\ proposerChanWrite0 = defaultInitValue
        /\ paxosChanWrite0 = defaultInitValue
        /\ upstreamWrite0 = defaultInitValue
        /\ requestsWrite0 = defaultInitValue
        /\ proposerChanWrite1 = defaultInitValue
        /\ paxosChanWrite1 = defaultInitValue
        /\ upstreamWrite1 = defaultInitValue
        /\ learnerChanRead = defaultInitValue
        /\ dbWrite = defaultInitValue
        /\ dbWrite0 = defaultInitValue
        /\ dbRead = defaultInitValue
        /\ requestServiceWrite = defaultInitValue
        /\ requestServiceWrite0 = defaultInitValue
        /\ dbWrite1 = defaultInitValue
        /\ requestServiceWrite1 = defaultInitValue
        /\ proposerChanRead = defaultInitValue
        /\ learnerChanWrite = defaultInitValue
        /\ learnerChanWrite0 = defaultInitValue
        (* Process kvRequests *)
        /\ msg_ = [self \in KVRequests |-> defaultInitValue]
        /\ null = [self \in KVRequests |-> defaultInitValue]
        /\ heartbeatId = [self \in KVRequests |-> defaultInitValue]
        /\ proposerId_ = [self \in KVRequests |-> defaultInitValue]
        /\ counter = [self \in KVRequests |-> 0]
        /\ requestId = [self \in KVRequests |-> defaultInitValue]
        /\ proposal = [self \in KVRequests |-> defaultInitValue]
        /\ result_ = [self \in KVRequests |-> defaultInitValue]
        (* Process kvPaxosManager *)
        /\ dbLocal = [self \in KVPaxosManager |-> [k \in (GetSet) \union (PutSet) |-> NULL_DB_VALUE]]
        /\ result = [self \in KVPaxosManager |-> defaultInitValue]
        /\ learnerId_ = [self \in KVPaxosManager |-> defaultInitValue]
        /\ decided = [self \in KVPaxosManager |-> defaultInitValue]
        /\ kvId = [self \in KVPaxosManager |-> defaultInitValue]
        (* Process consensus *)
        /\ msg = [self \in ConsensusSet |-> defaultInitValue]
        /\ learnerId = [self \in ConsensusSet |-> defaultInitValue]
        /\ proposerId = [self \in ConsensusSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in KVRequests -> "kvInit"
                                        [] self \in KVPaxosManager -> "findId"
                                        [] self \in ConsensusSet -> "findIds"]

kvInit(self) == /\ pc[self] = "kvInit"
                /\ heartbeatId' = [heartbeatId EXCEPT ![self] = (self) - ((2) * (NUM_NODES))]
                /\ proposerId_' = [proposerId_ EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                /\ UNCHANGED << values, requestSet, learnedChan,
                                paxosLayerChan, kvClient, idAbstract,
                                iAmTheLeaderAbstract, requestsRead,
                                requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead, dbWrite,
                                dbWrite0, dbRead, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, msg_,
                                null, counter, requestId, proposal, result_,
                                dbLocal, result, learnerId_, decided, kvId,
                                msg, learnerId, proposerId >>

kvLoop(self) == /\ pc[self] = "kvLoop"
                /\ IF TRUE
                      THEN /\ (Cardinality(requestSet)) > (0)
                           /\ \E req0 \in requestSet:
                                /\ requestsWrite' = (requestSet) \ ({req0})
                                /\ requestsRead' = req0
                           /\ msg_' = [msg_ EXCEPT ![self] = requestsRead']
                           /\ Assert((((msg_'[self]).type) = (GET_MSG)) \/ (((msg_'[self]).type) = (PUT_MSG)),
                                     "Failure of assertion at line 253, column 17.")
                           /\ iAmTheLeaderRead' = iAmTheLeaderAbstract[heartbeatId[self]]
                           /\ IF iAmTheLeaderRead'
                                 THEN /\ requestId' = [requestId EXCEPT ![self] = <<self, counter[self]>>]
                                      /\ IF ((msg_'[self]).type) = (GET_MSG)
                                            THEN /\ proposal' = [proposal EXCEPT ![self] = [operation |-> GET, id |-> requestId'[self], key |-> (msg_'[self]).key, value |-> (msg_'[self]).key]]
                                            ELSE /\ proposal' = [proposal EXCEPT ![self] = [operation |-> PUT, id |-> requestId'[self], key |-> (msg_'[self]).key, value |-> (msg_'[self]).value]]
                                      /\ ((values[proposerId_[self]]).value) = (NULL)
                                      /\ proposerChanWrite' = [values EXCEPT ![proposerId_[self]] = proposal'[self]]
                                      /\ requestSet' = requestsWrite'
                                      /\ values' = proposerChanWrite'
                                      /\ pc' = [pc EXCEPT ![self] = "requestConfirm"]
                                 ELSE /\ requestSet' = requestsWrite'
                                      /\ pc' = [pc EXCEPT ![self] = "notLeader"]
                                      /\ UNCHANGED << values,
                                                      proposerChanWrite,
                                                      requestId, proposal >>
                           /\ UNCHANGED << paxosLayerChan, kvClient,
                                           requestsWrite0, proposerChanWrite1,
                                           paxosChanWrite1, upstreamWrite1 >>
                      ELSE /\ requestsWrite0' = requestSet
                           /\ proposerChanWrite1' = values
                           /\ paxosChanWrite1' = paxosLayerChan
                           /\ upstreamWrite1' = kvClient
                           /\ requestSet' = requestsWrite0'
                           /\ kvClient' = upstreamWrite1'
                           /\ values' = proposerChanWrite1'
                           /\ paxosLayerChan' = paxosChanWrite1'
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << requestsRead, requestsWrite,
                                           iAmTheLeaderRead, proposerChanWrite,
                                           msg_, requestId, proposal >>
                /\ UNCHANGED << learnedChan, idAbstract, iAmTheLeaderAbstract,
                                paxosChanRead, paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, learnerChanRead, dbWrite,
                                dbWrite0, dbRead, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, null,
                                heartbeatId, proposerId_, counter, result_,
                                dbLocal, result, learnerId_, decided, kvId,
                                msg, learnerId, proposerId >>

requestConfirm(self) == /\ pc[self] = "requestConfirm"
                        /\ (paxosLayerChan[self]) # (NULL)
                        /\ LET v0 == paxosLayerChan[self] IN
                             /\ paxosChanWrite' = [paxosLayerChan EXCEPT ![self] = NULL]
                             /\ paxosChanRead' = v0
                        /\ result_' = [result_ EXCEPT ![self] = paxosChanRead']
                        /\ upstreamWrite' = ((kvClient) \union ({[type |-> OK_MSG, result |-> result_'[self]]}))
                        /\ counter' = [counter EXCEPT ![self] = (counter[self]) + (1)]
                        /\ kvClient' = upstreamWrite'
                        /\ paxosLayerChan' = paxosChanWrite'
                        /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                        /\ UNCHANGED << values, requestSet, learnedChan,
                                        idAbstract, iAmTheLeaderAbstract,
                                        requestsRead, requestsWrite,
                                        iAmTheLeaderRead, proposerChanWrite,
                                        proposerChanWrite0, paxosChanWrite0,
                                        upstreamWrite0, requestsWrite0,
                                        proposerChanWrite1, paxosChanWrite1,
                                        upstreamWrite1, learnerChanRead,
                                        dbWrite, dbWrite0, dbRead,
                                        requestServiceWrite,
                                        requestServiceWrite0, dbWrite1,
                                        requestServiceWrite1, proposerChanRead,
                                        learnerChanWrite, learnerChanWrite0,
                                        msg_, null, heartbeatId, proposerId_,
                                        requestId, proposal, dbLocal, result,
                                        learnerId_, decided, kvId, msg,
                                        learnerId, proposerId >>

notLeader(self) == /\ pc[self] = "notLeader"
                   /\ upstreamWrite' = ((kvClient) \union ({[type |-> NOT_LEADER_MSG, result |-> null[self]]}))
                   /\ kvClient' = upstreamWrite'
                   /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                   /\ UNCHANGED << values, requestSet, learnedChan,
                                   paxosLayerChan, idAbstract,
                                   iAmTheLeaderAbstract, requestsRead,
                                   requestsWrite, iAmTheLeaderRead,
                                   proposerChanWrite, paxosChanRead,
                                   paxosChanWrite, proposerChanWrite0,
                                   paxosChanWrite0, upstreamWrite0,
                                   requestsWrite0, proposerChanWrite1,
                                   paxosChanWrite1, upstreamWrite1,
                                   learnerChanRead, dbWrite, dbWrite0, dbRead,
                                   requestServiceWrite, requestServiceWrite0,
                                   dbWrite1, requestServiceWrite1,
                                   proposerChanRead, learnerChanWrite,
                                   learnerChanWrite0, msg_, null, heartbeatId,
                                   proposerId_, counter, requestId, proposal,
                                   result_, dbLocal, result, learnerId_,
                                   decided, kvId, msg, learnerId, proposerId >>

kvRequests(self) == kvInit(self) \/ kvLoop(self) \/ requestConfirm(self)
                       \/ notLeader(self)

findId(self) == /\ pc[self] = "findId"
                /\ learnerId_' = [learnerId_ EXCEPT ![self] = (self) - ((4) * (NUM_NODES))]
                /\ kvId' = [kvId EXCEPT ![self] = (self) - (NUM_NODES)]
                /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                /\ UNCHANGED << values, requestSet, learnedChan,
                                paxosLayerChan, kvClient, idAbstract,
                                iAmTheLeaderAbstract, requestsRead,
                                requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead, dbWrite,
                                dbWrite0, dbRead, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, msg_,
                                null, heartbeatId, proposerId_, counter,
                                requestId, proposal, result_, dbLocal, result,
                                decided, msg, learnerId, proposerId >>

kvManagerLoop(self) == /\ pc[self] = "kvManagerLoop"
                       /\ IF TRUE
                             THEN /\ ((learnedChan[learnerId_[self]]).value) # (NULL)
                                  /\ LET v1 == learnedChan[learnerId_[self]] IN
                                       /\ learnedChan' = [learnedChan EXCEPT ![learnerId_[self]].value = NULL]
                                       /\ learnerChanRead' = v1
                                  /\ decided' = [decided EXCEPT ![self] = learnerChanRead']
                                  /\ IF ((decided'[self]).operation) = (PUT)
                                        THEN /\ dbWrite' = [dbLocal[self] EXCEPT ![(decided'[self]).key] = (decided'[self]).value]
                                             /\ dbWrite0' = dbWrite'
                                        ELSE /\ dbWrite0' = dbLocal[self]
                                             /\ UNCHANGED dbWrite
                                  /\ IF ((decided'[self]).id[1]) = (kvId[self])
                                        THEN /\ IF ((decided'[self]).operation) = (GET)
                                                   THEN /\ dbRead' = dbWrite0'[(decided'[self]).key]
                                                        /\ result' = [result EXCEPT ![self] = dbRead']
                                                   ELSE /\ result' = [result EXCEPT ![self] = (decided'[self]).value]
                                                        /\ UNCHANGED dbRead
                                             /\ (paxosLayerChan[kvId[self]]) = (NULL)
                                             /\ requestServiceWrite' = [paxosLayerChan EXCEPT ![kvId[self]] = result'[self]]
                                             /\ requestServiceWrite0' = requestServiceWrite'
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ dbLocal' = [dbLocal EXCEPT ![self] = dbWrite1']
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                        ELSE /\ requestServiceWrite0' = paxosLayerChan
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ dbLocal' = [dbLocal EXCEPT ![self] = dbWrite1']
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                             /\ UNCHANGED << dbRead,
                                                             requestServiceWrite,
                                                             result >>
                             ELSE /\ dbWrite1' = dbLocal[self]
                                  /\ requestServiceWrite1' = paxosLayerChan
                                  /\ paxosLayerChan' = requestServiceWrite1'
                                  /\ dbLocal' = [dbLocal EXCEPT ![self] = dbWrite1']
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << learnedChan, learnerChanRead,
                                                  dbWrite, dbWrite0, dbRead,
                                                  requestServiceWrite,
                                                  requestServiceWrite0, result,
                                                  decided >>
                       /\ UNCHANGED << values, requestSet, kvClient,
                                       idAbstract, iAmTheLeaderAbstract,
                                       requestsRead, requestsWrite,
                                       iAmTheLeaderRead, proposerChanWrite,
                                       paxosChanRead, paxosChanWrite,
                                       upstreamWrite, proposerChanWrite0,
                                       paxosChanWrite0, upstreamWrite0,
                                       requestsWrite0, proposerChanWrite1,
                                       paxosChanWrite1, upstreamWrite1,
                                       proposerChanRead, learnerChanWrite,
                                       learnerChanWrite0, msg_, null,
                                       heartbeatId, proposerId_, counter,
                                       requestId, proposal, result_,
                                       learnerId_, kvId, msg, learnerId,
                                       proposerId >>

kvPaxosManager(self) == findId(self) \/ kvManagerLoop(self)

findIds(self) == /\ pc[self] = "findIds"
                 /\ proposerId' = [proposerId EXCEPT ![self] = (self) - ((7) * (NUM_NODES))]
                 /\ learnerId' = [learnerId EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                 /\ pc' = [pc EXCEPT ![self] = "consensusLoop"]
                 /\ UNCHANGED << values, requestSet, learnedChan,
                                 paxosLayerChan, kvClient, idAbstract,
                                 iAmTheLeaderAbstract, requestsRead,
                                 requestsWrite, iAmTheLeaderRead,
                                 proposerChanWrite, paxosChanRead,
                                 paxosChanWrite, upstreamWrite,
                                 proposerChanWrite0, paxosChanWrite0,
                                 upstreamWrite0, requestsWrite0,
                                 proposerChanWrite1, paxosChanWrite1,
                                 upstreamWrite1, learnerChanRead, dbWrite,
                                 dbWrite0, dbRead, requestServiceWrite,
                                 requestServiceWrite0, dbWrite1,
                                 requestServiceWrite1, proposerChanRead,
                                 learnerChanWrite, learnerChanWrite0, msg_,
                                 null, heartbeatId, proposerId_, counter,
                                 requestId, proposal, result_, dbLocal, result,
                                 learnerId_, decided, kvId, msg >>

consensusLoop(self) == /\ pc[self] = "consensusLoop"
                       /\ IF TRUE
                             THEN /\ ((values[proposerId[self]]).value) # (NULL)
                                  /\ LET v2 == values[proposerId[self]] IN
                                       /\ values' = [values EXCEPT ![proposerId[self]].value = NULL]
                                       /\ proposerChanRead' = v2
                                  /\ msg' = [msg EXCEPT ![self] = proposerChanRead']
                                  /\ ((learnedChan[learnerId[self]]).value) = (NULL)
                                  /\ learnerChanWrite' = [learnedChan EXCEPT ![learnerId[self]] = msg'[self]]
                                  /\ learnerChanWrite0' = learnerChanWrite'
                                  /\ learnedChan' = learnerChanWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "consensusLoop"]
                             ELSE /\ learnerChanWrite0' = learnedChan
                                  /\ learnedChan' = learnerChanWrite0'
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << values, proposerChanRead,
                                                  learnerChanWrite, msg >>
                       /\ UNCHANGED << requestSet, paxosLayerChan, kvClient,
                                       idAbstract, iAmTheLeaderAbstract,
                                       requestsRead, requestsWrite,
                                       iAmTheLeaderRead, proposerChanWrite,
                                       paxosChanRead, paxosChanWrite,
                                       upstreamWrite, proposerChanWrite0,
                                       paxosChanWrite0, upstreamWrite0,
                                       requestsWrite0, proposerChanWrite1,
                                       paxosChanWrite1, upstreamWrite1,
                                       learnerChanRead, dbWrite, dbWrite0,
                                       dbRead, requestServiceWrite,
                                       requestServiceWrite0, dbWrite1,
                                       requestServiceWrite1, msg_, null,
                                       heartbeatId, proposerId_, counter,
                                       requestId, proposal, result_, dbLocal,
                                       result, learnerId_, decided, kvId,
                                       learnerId, proposerId >>

consensus(self) == findIds(self) \/ consensusLoop(self)

Next == (\E self \in KVRequests: kvRequests(self))
           \/ (\E self \in KVPaxosManager: kvPaxosManager(self))
           \/ (\E self \in ConsensusSet: consensus(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in KVRequests : WF_vars(kvRequests(self))
        /\ \A self \in KVPaxosManager : WF_vars(kvPaxosManager(self))
        /\ \A self \in ConsensusSet : WF_vars(consensus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\*  Every KV node has a consistent database (this is only true if the keys used in PUT operations are distinct)
\* ConsistentDatabase == \A kv1, kv2 \in KVRequests, k \in PutSet :
\*                           database[kv1, k] # NULL /\ database[kv2, k] # NULL => database[kv1, k] = database[kv2, k]

ConsistentDatabase == \A kv1 \in KVPaxosManager, k \in PutSet : dbLocal[kv1][k] = NULL_DB_VALUE \/ dbLocal[kv1][k] = k

\* Eventually the database of every node is populated with the associated value
\* All PUT operations performed are in the format: Put(key, key)
Progress == \A kv \in KVPaxosManager, k \in PutSet : <>(dbLocal[kv][k] = k)

\* Termination formula:
\* ~(\A k \in PutSet : \E kv \in KVRequests : database[kv, k] # NULL)

=========================================================
