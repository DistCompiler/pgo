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

      GET_MSG            == 6
      PUT_MSG            == 7
      GET_RESPONSE_MSG   == 8
      NOT_LEADER_MSG     == 9
      OK_MSG             == 10

      GET == 11
      PUT == 12

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
  variables msg, null, heartbeatId, proposerId, counter = 0, requestId, requestOk, confirmedRequestId, proposal, result;
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

                requestConfirm:
                  result := paxosChan[self];

                  upstream := [type |-> OK_MSG, result |-> result];
                  counter := counter + 1;
            } else {
                upstream := [type |-> NOT_LEADER_MSG, result |-> null];
            }
        }
  }

  archetype KeyValuePaxosManager(ref requestService, learnerChan, ref db, kvId)
  variables result, learnerId, decided;
  {
      findId:
        learnerId := self - 4*NUM_NODES;

      kvManagerLoop:
        while (TRUE) {
            \* wait for a value to be informed by the learner
            decided := learnerChan[learnerId];

            \* always update the database if it's a PUT request, regardless of whether
            \* this instance issued the request
            if (decided.operation = PUT) {
                db[<< kvId, decided.key >>] := decided.value;
            };

            \* only send the result to the request service if we issued the request
            if (decided.id[1] = kvId) {
                \* read value from the database and return result
                if (decided.operation = GET) {
                    result := db[<< kvId, decided.key >>];
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
        requestSet = { [type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet } \union { [type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet},

        learnedChan = [l \in Learner |-> [value |-> NULL]],
        paxosLayerChan = [p \in KVRequests |-> NULL],

        kvClient = {},
        idAbstract,

        database = [p \in KVRequests, k \in GetSet \union PutSet |-> NULL_DB_VALUE],
        iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE];

    fair process (kvRequests \in KVRequests) == instance KeyValueRequests(requestSet, ref kvClient, iAmTheLeaderAbstract, values, paxosLayerChan)
        mapping requestSet via NextRequest
        mapping kvClient via SetAdd
        mapping iAmTheLeaderAbstract[_] via Identity
        mapping values[_] via UnbufferedRecordChannel
        mapping paxosLayerChan[_] via UnbufferedIntChannel;

    fair process (kvPaxosManager \in KVPaxosManager) == instance KeyValuePaxosManager(ref paxosLayerChan, learnedChan, ref database, idAbstract)
        mapping paxosLayerChan[_] via UnbufferedIntChannel
        mapping learnedChan[_] via UnbufferedRecordChannel
        mapping database[_] via Identity
        mapping idAbstract via SelfManager;

    fair process (consensus \in ConsensusSet) == instance Consensus(values, learnedChan)
        mapping values[_] via UnbufferedRecordChannel
        mapping learnedChan[_] via UnbufferedRecordChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ConsensusKV {
    variables values = [k \in Proposer |-> [value |-> NULL]], requestSet = ({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}), learnedChan = [l \in Learner |-> [value |-> NULL]], paxosLayerChan = [p \in KVRequests |-> NULL], kvClient = {}, idAbstract, database = [p \in KVRequests, k \in (GetSet) \union (PutSet) |-> NULL_DB_VALUE], iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE], requestsRead, requestsWrite, iAmTheLeaderRead, proposerChanWrite, paxosChanRead, paxosChanWrite, upstreamWrite, proposerChanWrite0, paxosChanWrite0, upstreamWrite0, requestsWrite0, proposerChanWrite1, paxosChanWrite1, upstreamWrite1, learnerChanRead, kvIdRead, dbWrite, dbWrite0, kvIdRead0, kvIdRead1, dbRead, kvIdRead2, requestServiceWrite, requestServiceWrite0, dbWrite1, requestServiceWrite1, proposerChanRead, learnerChanWrite, learnerChanWrite0;
    define {
        Proposer == (0) .. ((NUM_NODES) - (1))
        Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
        Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
        KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
        KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
        ConsensusSet == ((7) * (NUM_NODES)) .. (((8) * (NUM_NODES)) - (1))
        GET_MSG == 6
        PUT_MSG == 7
        GET_RESPONSE_MSG == 8
        NOT_LEADER_MSG == 9
        OK_MSG == 10
        GET == 11
        PUT == 12
    }
    fair process (kvRequests \in KVRequests)
    variables msg, null, heartbeatId, proposerId, counter = 0, requestId, requestOk, confirmedRequestId, proposal, result;
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
                    upstreamWrite := (kvClient) \union ({[type |-> NOT_LEADER_MSG, result |-> null]});
                    proposerChanWrite0 := values;
                    paxosChanWrite0 := paxosLayerChan;
                    upstreamWrite0 := upstreamWrite;
                    requestsWrite0 := requestsWrite;
                    proposerChanWrite1 := proposerChanWrite0;
                    paxosChanWrite1 := paxosChanWrite0;
                    upstreamWrite1 := upstreamWrite0;
                    requestSet := requestsWrite0;
                    kvClient := upstreamWrite1;
                    values := proposerChanWrite1;
                    paxosLayerChan := paxosChanWrite1;
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
    variables result, learnerId, decided;
    {
        findId:
            learnerId := (self) - ((4) * (NUM_NODES));
        kvManagerLoop:
            if (TRUE) {
                await ((learnedChan[learnerId]).value) # (NULL);
                with (v1 = learnedChan[learnerId]) {
                    learnedChan[learnerId].value := NULL;
                    learnerChanRead := v1;
                };
                decided := learnerChanRead;
                if (((decided).operation) = (PUT)) {
                    kvIdRead := (self) - (NUM_NODES);
                    dbWrite := [database EXCEPT ![<<kvIdRead, (decided).key>>] = (decided).value];
                    dbWrite0 := dbWrite;
                } else {
                    dbWrite0 := database;
                };
                kvIdRead0 := (self) - (NUM_NODES);
                if (((decided).id[1]) = (kvIdRead0)) {
                    if (((decided).operation) = (GET)) {
                        kvIdRead1 := (self) - (NUM_NODES);
                        dbRead := dbWrite0[<<kvIdRead1, (decided).key>>];
                        result := dbRead;
                    } else {
                        result := (decided).value;
                    };
                    kvIdRead2 := (self) - (NUM_NODES);
                    await (paxosLayerChan[kvIdRead2]) = (NULL);
                    requestServiceWrite := [paxosLayerChan EXCEPT ![kvIdRead2] = result];
                    requestServiceWrite0 := requestServiceWrite;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    database := dbWrite1;
                    goto kvManagerLoop;
                } else {
                    requestServiceWrite0 := paxosLayerChan;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    database := dbWrite1;
                    goto kvManagerLoop;
                };
            } else {
                dbWrite1 := database;
                requestServiceWrite1 := paxosLayerChan;
                paxosLayerChan := requestServiceWrite1;
                database := dbWrite1;
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
\* Process variable msg of process kvRequests at line 236 col 15 changed to msg_
\* Process variable proposerId of process kvRequests at line 236 col 39 changed to proposerId_
\* Process variable result of process kvRequests at line 236 col 116 changed to result_
\* Process variable learnerId of process kvPaxosManager at line 303 col 23 changed to learnerId_
CONSTANT defaultInitValue
VARIABLES values, requestSet, learnedChan, paxosLayerChan, kvClient,
          idAbstract, database, iAmTheLeaderAbstract, requestsRead,
          requestsWrite, iAmTheLeaderRead, proposerChanWrite, paxosChanRead,
          paxosChanWrite, upstreamWrite, proposerChanWrite0, paxosChanWrite0,
          upstreamWrite0, requestsWrite0, proposerChanWrite1, paxosChanWrite1,
          upstreamWrite1, learnerChanRead, kvIdRead, dbWrite, dbWrite0,
          kvIdRead0, kvIdRead1, dbRead, kvIdRead2, requestServiceWrite,
          requestServiceWrite0, dbWrite1, requestServiceWrite1,
          proposerChanRead, learnerChanWrite, learnerChanWrite0, pc

(* define statement *)
Proposer == (0) .. ((NUM_NODES) - (1))
Learner == ((2) * (NUM_NODES)) .. (((3) * (NUM_NODES)) - (1))
Heartbeat == ((3) * (NUM_NODES)) .. (((4) * (NUM_NODES)) - (1))
KVRequests == ((5) * (NUM_NODES)) .. (((6) * (NUM_NODES)) - (1))
KVPaxosManager == ((6) * (NUM_NODES)) .. (((7) * (NUM_NODES)) - (1))
ConsensusSet == ((7) * (NUM_NODES)) .. (((8) * (NUM_NODES)) - (1))
GET_MSG == 6
PUT_MSG == 7
GET_RESPONSE_MSG == 8
NOT_LEADER_MSG == 9
OK_MSG == 10
GET == 11
PUT == 12

VARIABLES msg_, null, heartbeatId, proposerId_, counter, requestId, requestOk,
          confirmedRequestId, proposal, result_, result, learnerId_, decided,
          msg, learnerId, proposerId

vars == << values, requestSet, learnedChan, paxosLayerChan, kvClient,
           idAbstract, database, iAmTheLeaderAbstract, requestsRead,
           requestsWrite, iAmTheLeaderRead, proposerChanWrite, paxosChanRead,
           paxosChanWrite, upstreamWrite, proposerChanWrite0, paxosChanWrite0,
           upstreamWrite0, requestsWrite0, proposerChanWrite1,
           paxosChanWrite1, upstreamWrite1, learnerChanRead, kvIdRead,
           dbWrite, dbWrite0, kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
           requestServiceWrite, requestServiceWrite0, dbWrite1,
           requestServiceWrite1, proposerChanRead, learnerChanWrite,
           learnerChanWrite0, pc, msg_, null, heartbeatId, proposerId_,
           counter, requestId, requestOk, confirmedRequestId, proposal,
           result_, result, learnerId_, decided, msg, learnerId, proposerId
        >>

ProcSet == (KVRequests) \cup (KVPaxosManager) \cup (ConsensusSet)

Init == (* Global variables *)
        /\ values = [k \in Proposer |-> [value |-> NULL]]
        /\ requestSet = (({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}))
        /\ learnedChan = [l \in Learner |-> [value |-> NULL]]
        /\ paxosLayerChan = [p \in KVRequests |-> NULL]
        /\ kvClient = {}
        /\ idAbstract = defaultInitValue
        /\ database = [p \in KVRequests, k \in (GetSet) \union (PutSet) |-> NULL_DB_VALUE]
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
        /\ kvIdRead = defaultInitValue
        /\ dbWrite = defaultInitValue
        /\ dbWrite0 = defaultInitValue
        /\ kvIdRead0 = defaultInitValue
        /\ kvIdRead1 = defaultInitValue
        /\ dbRead = defaultInitValue
        /\ kvIdRead2 = defaultInitValue
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
        /\ requestOk = [self \in KVRequests |-> defaultInitValue]
        /\ confirmedRequestId = [self \in KVRequests |-> defaultInitValue]
        /\ proposal = [self \in KVRequests |-> defaultInitValue]
        /\ result_ = [self \in KVRequests |-> defaultInitValue]
        (* Process kvPaxosManager *)
        /\ result = [self \in KVPaxosManager |-> defaultInitValue]
        /\ learnerId_ = [self \in KVPaxosManager |-> defaultInitValue]
        /\ decided = [self \in KVPaxosManager |-> defaultInitValue]
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
                                paxosLayerChan, kvClient, idAbstract, database,
                                iAmTheLeaderAbstract, requestsRead,
                                requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead, kvIdRead,
                                dbWrite, dbWrite0, kvIdRead0, kvIdRead1,
                                dbRead, kvIdRead2, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, msg_,
                                null, counter, requestId, requestOk,
                                confirmedRequestId, proposal, result_, result,
                                learnerId_, decided, msg, learnerId,
                                proposerId >>

kvLoop(self) == /\ pc[self] = "kvLoop"
                /\ IF TRUE
                      THEN /\ (Cardinality(requestSet)) > (0)
                           /\ \E req0 \in requestSet:
                                /\ requestsWrite' = (requestSet) \ ({req0})
                                /\ requestsRead' = req0
                           /\ msg_' = [msg_ EXCEPT ![self] = requestsRead']
                           /\ Assert((((msg_'[self]).type) = (GET_MSG)) \/ (((msg_'[self]).type) = (PUT_MSG)),
                                     "Failure of assertion at line 249, column 17.")
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
                                      /\ UNCHANGED << paxosLayerChan, kvClient,
                                                      upstreamWrite,
                                                      proposerChanWrite0,
                                                      paxosChanWrite0,
                                                      upstreamWrite0,
                                                      requestsWrite0,
                                                      proposerChanWrite1,
                                                      paxosChanWrite1,
                                                      upstreamWrite1 >>
                                 ELSE /\ upstreamWrite' = ((kvClient) \union ({[type |-> NOT_LEADER_MSG, result |-> null[self]]}))
                                      /\ proposerChanWrite0' = values
                                      /\ paxosChanWrite0' = paxosLayerChan
                                      /\ upstreamWrite0' = upstreamWrite'
                                      /\ requestsWrite0' = requestsWrite'
                                      /\ proposerChanWrite1' = proposerChanWrite0'
                                      /\ paxosChanWrite1' = paxosChanWrite0'
                                      /\ upstreamWrite1' = upstreamWrite0'
                                      /\ requestSet' = requestsWrite0'
                                      /\ kvClient' = upstreamWrite1'
                                      /\ values' = proposerChanWrite1'
                                      /\ paxosLayerChan' = paxosChanWrite1'
                                      /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                                      /\ UNCHANGED << proposerChanWrite,
                                                      requestId, proposal >>
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
                                           upstreamWrite, proposerChanWrite0,
                                           paxosChanWrite0, upstreamWrite0,
                                           msg_, requestId, proposal >>
                /\ UNCHANGED << learnedChan, idAbstract, database,
                                iAmTheLeaderAbstract, paxosChanRead,
                                paxosChanWrite, learnerChanRead, kvIdRead,
                                dbWrite, dbWrite0, kvIdRead0, kvIdRead1,
                                dbRead, kvIdRead2, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, null,
                                heartbeatId, proposerId_, counter, requestOk,
                                confirmedRequestId, result_, result,
                                learnerId_, decided, msg, learnerId,
                                proposerId >>

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
                                        idAbstract, database,
                                        iAmTheLeaderAbstract, requestsRead,
                                        requestsWrite, iAmTheLeaderRead,
                                        proposerChanWrite, proposerChanWrite0,
                                        paxosChanWrite0, upstreamWrite0,
                                        requestsWrite0, proposerChanWrite1,
                                        paxosChanWrite1, upstreamWrite1,
                                        learnerChanRead, kvIdRead, dbWrite,
                                        dbWrite0, kvIdRead0, kvIdRead1, dbRead,
                                        kvIdRead2, requestServiceWrite,
                                        requestServiceWrite0, dbWrite1,
                                        requestServiceWrite1, proposerChanRead,
                                        learnerChanWrite, learnerChanWrite0,
                                        msg_, null, heartbeatId, proposerId_,
                                        requestId, requestOk,
                                        confirmedRequestId, proposal, result,
                                        learnerId_, decided, msg, learnerId,
                                        proposerId >>

kvRequests(self) == kvInit(self) \/ kvLoop(self) \/ requestConfirm(self)

findId(self) == /\ pc[self] = "findId"
                /\ learnerId_' = [learnerId_ EXCEPT ![self] = (self) - ((4) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                /\ UNCHANGED << values, requestSet, learnedChan,
                                paxosLayerChan, kvClient, idAbstract, database,
                                iAmTheLeaderAbstract, requestsRead,
                                requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead, kvIdRead,
                                dbWrite, dbWrite0, kvIdRead0, kvIdRead1,
                                dbRead, kvIdRead2, requestServiceWrite,
                                requestServiceWrite0, dbWrite1,
                                requestServiceWrite1, proposerChanRead,
                                learnerChanWrite, learnerChanWrite0, msg_,
                                null, heartbeatId, proposerId_, counter,
                                requestId, requestOk, confirmedRequestId,
                                proposal, result_, result, decided, msg,
                                learnerId, proposerId >>

kvManagerLoop(self) == /\ pc[self] = "kvManagerLoop"
                       /\ IF TRUE
                             THEN /\ ((learnedChan[learnerId_[self]]).value) # (NULL)
                                  /\ LET v1 == learnedChan[learnerId_[self]] IN
                                       /\ learnedChan' = [learnedChan EXCEPT ![learnerId_[self]].value = NULL]
                                       /\ learnerChanRead' = v1
                                  /\ decided' = [decided EXCEPT ![self] = learnerChanRead']
                                  /\ IF ((decided'[self]).operation) = (PUT)
                                        THEN /\ kvIdRead' = (self) - (NUM_NODES)
                                             /\ dbWrite' = [database EXCEPT ![<<kvIdRead', (decided'[self]).key>>] = (decided'[self]).value]
                                             /\ dbWrite0' = dbWrite'
                                        ELSE /\ dbWrite0' = database
                                             /\ UNCHANGED << kvIdRead, dbWrite >>
                                  /\ kvIdRead0' = (self) - (NUM_NODES)
                                  /\ IF ((decided'[self]).id[1]) = (kvIdRead0')
                                        THEN /\ IF ((decided'[self]).operation) = (GET)
                                                   THEN /\ kvIdRead1' = (self) - (NUM_NODES)
                                                        /\ dbRead' = dbWrite0'[<<kvIdRead1', (decided'[self]).key>>]
                                                        /\ result' = [result EXCEPT ![self] = dbRead']
                                                   ELSE /\ result' = [result EXCEPT ![self] = (decided'[self]).value]
                                                        /\ UNCHANGED << kvIdRead1,
                                                                        dbRead >>
                                             /\ kvIdRead2' = (self) - (NUM_NODES)
                                             /\ (paxosLayerChan[kvIdRead2']) = (NULL)
                                             /\ requestServiceWrite' = [paxosLayerChan EXCEPT ![kvIdRead2'] = result'[self]]
                                             /\ requestServiceWrite0' = requestServiceWrite'
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ database' = dbWrite1'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                        ELSE /\ requestServiceWrite0' = paxosLayerChan
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ database' = dbWrite1'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                             /\ UNCHANGED << kvIdRead1, dbRead,
                                                             kvIdRead2,
                                                             requestServiceWrite,
                                                             result >>
                             ELSE /\ dbWrite1' = database
                                  /\ requestServiceWrite1' = paxosLayerChan
                                  /\ paxosLayerChan' = requestServiceWrite1'
                                  /\ database' = dbWrite1'
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << learnedChan, learnerChanRead,
                                                  kvIdRead, dbWrite, dbWrite0,
                                                  kvIdRead0, kvIdRead1, dbRead,
                                                  kvIdRead2,
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
                                       requestId, requestOk,
                                       confirmedRequestId, proposal, result_,
                                       learnerId_, msg, learnerId, proposerId >>

kvPaxosManager(self) == findId(self) \/ kvManagerLoop(self)

findIds(self) == /\ pc[self] = "findIds"
                 /\ proposerId' = [proposerId EXCEPT ![self] = (self) - ((7) * (NUM_NODES))]
                 /\ learnerId' = [learnerId EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                 /\ pc' = [pc EXCEPT ![self] = "consensusLoop"]
                 /\ UNCHANGED << values, requestSet, learnedChan,
                                 paxosLayerChan, kvClient, idAbstract,
                                 database, iAmTheLeaderAbstract, requestsRead,
                                 requestsWrite, iAmTheLeaderRead,
                                 proposerChanWrite, paxosChanRead,
                                 paxosChanWrite, upstreamWrite,
                                 proposerChanWrite0, paxosChanWrite0,
                                 upstreamWrite0, requestsWrite0,
                                 proposerChanWrite1, paxosChanWrite1,
                                 upstreamWrite1, learnerChanRead, kvIdRead,
                                 dbWrite, dbWrite0, kvIdRead0, kvIdRead1,
                                 dbRead, kvIdRead2, requestServiceWrite,
                                 requestServiceWrite0, dbWrite1,
                                 requestServiceWrite1, proposerChanRead,
                                 learnerChanWrite, learnerChanWrite0, msg_,
                                 null, heartbeatId, proposerId_, counter,
                                 requestId, requestOk, confirmedRequestId,
                                 proposal, result_, result, learnerId_,
                                 decided, msg >>

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
                                       idAbstract, database,
                                       iAmTheLeaderAbstract, requestsRead,
                                       requestsWrite, iAmTheLeaderRead,
                                       proposerChanWrite, paxosChanRead,
                                       paxosChanWrite, upstreamWrite,
                                       proposerChanWrite0, paxosChanWrite0,
                                       upstreamWrite0, requestsWrite0,
                                       proposerChanWrite1, paxosChanWrite1,
                                       upstreamWrite1, learnerChanRead,
                                       kvIdRead, dbWrite, dbWrite0, kvIdRead0,
                                       kvIdRead1, dbRead, kvIdRead2,
                                       requestServiceWrite,
                                       requestServiceWrite0, dbWrite1,
                                       requestServiceWrite1, msg_, null,
                                       heartbeatId, proposerId_, counter,
                                       requestId, requestOk,
                                       confirmedRequestId, proposal, result_,
                                       result, learnerId_, decided, learnerId,
                                       proposerId >>

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

ConsistentDatabase == \A kv1 \in KVRequests, k \in PutSet : database[kv1, k] = NULL_DB_VALUE \/ database[kv1, k] = k

\* Eventually the database of every node is populated with the associated value
\* All PUT operations performed are in the format: Put(key, key)
Progress == \A kv \in KVRequests, k \in PutSet : <>(database[kv, k] = k)

\* Termination formula:
\* ~(\A k \in PutSet : \E kv \in KVRequests : database[kv, k] # NULL)

=========================================================
