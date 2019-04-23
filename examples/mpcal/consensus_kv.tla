----------------------------------- MODULE consensus_kv ---------------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NUM_NODES
ASSUME NUM_NODES \in Nat

CONSTANT NULL, NULL_DB_VALUE
ASSUME NULL \notin Nat /\ NULL_DB_VALUE # NULL

CONSTANT BUFFER_SIZE
ASSUME BUFFER_SIZE \in Nat

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
          with (e \in $variable) {
              $variable := $variable \ {e};
              yield e;
          }
      }

      write {
          yield $variable \union {$value};
      }
  }

  archetype Consensus(proposerChans, ref learnerChan)
  variables msg, learnerId, proposerId;
  {
      findIds:
          learnerId := self - 5*NUM_NODES;

      consensusLoop:
        while (TRUE) {
            msg := proposerChans[self];

            sendLearner:
              learnerChan[learnerId] := msg;
        }
  }

  archetype ConsensusBroadcast(bcastChan, ref proposerChans)
  variables msg, j;
  {
    broadcastLoop:
      while (TRUE) {
          msg := bcastChan;
          j := 7*NUM_NODES;

          broadcastMessage:
            while (j <= 8*NUM_NODES-1) {
                proposerChans[j] := msg;
            }
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

                \* divergence from Paxos spec: no function application in proposerChan
                proposerChan := proposal;

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
        values = [k \in Proposer |-> <<>>],

        \* requests to be sent by the client
        requestSet = { [type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet } \union { [type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet},

        learnedChan = [l \in Learner |-> <<>>],
        paxosLayerChan = [p \in KVRequests |-> <<>>],

        kvClient = {},
        idAbstract,

        network = [c \in ConsensusSet |-> <<>>],
        broadcastChan = {},

        database = [p \in KVRequests, k \in GetSet \union PutSet |-> NULL_DB_VALUE],
        iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE];

    fair process (kvRequests \in KVRequests) == instance KeyValueRequests(requestSet, ref kvClient, iAmTheLeaderAbstract, broadcastChan, paxosLayerChan)
        mapping requestSet via NextRequest
        mapping kvClient via SetAdd
        mapping iAmTheLeaderAbstract[_] via Identity
        mapping broadcastChan via SetAdd
        mapping paxosLayerChan[_] via FIFOChannel;

    fair process (kvPaxosManager \in KVPaxosManager) == instance KeyValuePaxosManager(ref paxosLayerChan, learnedChan, ref database, idAbstract)
        mapping paxosLayerChan[_] via FIFOChannel
        mapping learnedChan[_] via FIFOChannel
        mapping database[_] via Identity
        mapping idAbstract via SelfManager;

    fair process (consensus \in ConsensusSet) == instance Consensus(network, learnedChan)
        mapping learnedChan[_] via FIFOChannel
        mapping network[_] via FIFOChannel;

    fair process (consensusBroadcast = 8*NUM_NODES) == instance ConsensusBroadcast(broadcastChan, ref network)
        mapping broadcastChan via SetAdd
        mapping network[_] via FIFOChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ConsensusKV {
    variables values = [k \in Proposer |-> <<>>], requestSet = ({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}), learnedChan = [l \in Learner |-> <<>>], paxosLayerChan = [p \in KVRequests |-> <<>>], kvClient = {}, idAbstract, network = [c \in ConsensusSet |-> <<>>], broadcastChan = {}, database = [p \in KVRequests, k \in (GetSet) \union (PutSet) |-> NULL_DB_VALUE], iAmTheLeaderAbstract = [h \in Heartbeat |-> TRUE], requestsRead, requestsWrite, iAmTheLeaderRead, proposerChanWrite, paxosChanRead, paxosChanWrite, upstreamWrite, proposerChanWrite0, paxosChanWrite0, upstreamWrite0, requestsWrite0, proposerChanWrite1, paxosChanWrite1, upstreamWrite1, learnerChanRead, learnerChanWrite, kvIdRead, dbWrite, dbWrite0, kvIdRead0, kvIdRead1, dbRead, kvIdRead2, requestServiceWrite, requestServiceWrite0, learnerChanWrite0, dbWrite1, requestServiceWrite1, proposerChansRead, proposerChansWrite, learnerChanWrite1, proposerChansWrite0, learnerChanWrite2, bcastChanRead, bcastChanWrite, proposerChansWrite1, proposerChansWrite2, bcastChanWrite0, proposerChansWrite3;
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
                    proposerChanWrite := (broadcastChan) \union ({proposal});
                    requestSet := requestsWrite;
                    broadcastChan := proposerChanWrite;
                    requestConfirm:
                        await (Len(paxosLayerChan[self])) > (0);
                        with (msg0 = Head(paxosLayerChan[self])) {
                            paxosChanWrite := [paxosLayerChan EXCEPT ![self] = Tail(paxosLayerChan[self])];
                            paxosChanRead := msg0;
                        };
                        result := paxosChanRead;
                        upstreamWrite := (kvClient) \union ({[type |-> OK_MSG, result |-> result]});
                        counter := (counter) + (1);
                        kvClient := upstreamWrite;
                        paxosLayerChan := paxosChanWrite;
                        goto kvLoop;

                } else {
                    upstreamWrite := (kvClient) \union ({[type |-> NOT_LEADER_MSG, result |-> null]});
                    proposerChanWrite0 := broadcastChan;
                    paxosChanWrite0 := paxosLayerChan;
                    upstreamWrite0 := upstreamWrite;
                    requestsWrite0 := requestsWrite;
                    proposerChanWrite1 := proposerChanWrite0;
                    paxosChanWrite1 := paxosChanWrite0;
                    upstreamWrite1 := upstreamWrite0;
                    requestSet := requestsWrite0;
                    kvClient := upstreamWrite1;
                    broadcastChan := proposerChanWrite1;
                    paxosLayerChan := paxosChanWrite1;
                    goto kvLoop;
                };
            } else {
                requestsWrite0 := requestSet;
                proposerChanWrite1 := broadcastChan;
                paxosChanWrite1 := paxosLayerChan;
                upstreamWrite1 := kvClient;
                requestSet := requestsWrite0;
                kvClient := upstreamWrite1;
                broadcastChan := proposerChanWrite1;
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
                await (Len(learnedChan[learnerId])) > (0);
                with (msg1 = Head(learnedChan[learnerId])) {
                    learnerChanWrite := [learnedChan EXCEPT ![learnerId] = Tail(learnedChan[learnerId])];
                    learnerChanRead := msg1;
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
                    await (Len(paxosLayerChan[kvIdRead2])) < (BUFFER_SIZE);
                    requestServiceWrite := [paxosLayerChan EXCEPT ![kvIdRead2] = Append(paxosLayerChan[kvIdRead2], result)];
                    requestServiceWrite0 := requestServiceWrite;
                    learnerChanWrite0 := learnerChanWrite;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    learnedChan := learnerChanWrite0;
                    database := dbWrite1;
                    goto kvManagerLoop;
                } else {
                    requestServiceWrite0 := paxosLayerChan;
                    learnerChanWrite0 := learnerChanWrite;
                    dbWrite1 := dbWrite0;
                    requestServiceWrite1 := requestServiceWrite0;
                    paxosLayerChan := requestServiceWrite1;
                    learnedChan := learnerChanWrite0;
                    database := dbWrite1;
                    goto kvManagerLoop;
                };
            } else {
                learnerChanWrite0 := learnedChan;
                dbWrite1 := database;
                requestServiceWrite1 := paxosLayerChan;
                paxosLayerChan := requestServiceWrite1;
                learnedChan := learnerChanWrite0;
                database := dbWrite1;
            };

    }
    fair process (consensus \in ConsensusSet)
    variables msg, learnerId, proposerId;
    {
        findIds:
            learnerId := (self) - ((5) * (NUM_NODES));
        consensusLoop:
            if (TRUE) {
                await (Len(network[self])) > (0);
                with (msg2 = Head(network[self])) {
                    proposerChansWrite := [network EXCEPT ![self] = Tail(network[self])];
                    proposerChansRead := msg2;
                };
                msg := proposerChansRead;
                network := proposerChansWrite;
                sendLearner:
                    await (Len(learnedChan[learnerId])) < (BUFFER_SIZE);
                    learnerChanWrite1 := [learnedChan EXCEPT ![learnerId] = Append(learnedChan[learnerId], msg)];
                    learnedChan := learnerChanWrite1;
                    goto consensusLoop;

            } else {
                proposerChansWrite0 := network;
                learnerChanWrite2 := learnedChan;
                network := proposerChansWrite0;
                learnedChan := learnerChanWrite2;
            };

    }
    fair process (consensusBroadcast = (8) * (NUM_NODES))
    variables msg, j;
    {
        broadcastLoop:
            if (TRUE) {
                with (e0 \in broadcastChan) {
                    bcastChanWrite := (broadcastChan) \ ({e0});
                    bcastChanRead := e0;
                };
                msg := bcastChanRead;
                j := (7) * (NUM_NODES);
                broadcastChan := bcastChanWrite;
                broadcastMessage:
                    if ((j) <= (((8) * (NUM_NODES)) - (1))) {
                        await (Len(network[j])) < (BUFFER_SIZE);
                        proposerChansWrite1 := [network EXCEPT ![j] = Append(network[j], msg)];
                        proposerChansWrite2 := proposerChansWrite1;
                        network := proposerChansWrite2;
                        goto broadcastMessage;
                    } else {
                        proposerChansWrite2 := network;
                        network := proposerChansWrite2;
                        goto broadcastLoop;
                    };

            } else {
                bcastChanWrite0 := broadcastChan;
                proposerChansWrite3 := network;
                broadcastChan := bcastChanWrite0;
                network := proposerChansWrite3;
            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)

\* BEGIN TRANSLATION
\* Process variable msg of process kvRequests at line 248 col 15 changed to msg_
\* Process variable proposerId of process kvRequests at line 248 col 39 changed to proposerId_
\* Process variable result of process kvRequests at line 248 col 116 changed to result_
\* Process variable learnerId of process kvPaxosManager at line 314 col 23 changed to learnerId_
\* Process variable msg of process consensus at line 374 col 15 changed to msg_c
CONSTANT defaultInitValue
VARIABLES values, requestSet, learnedChan, paxosLayerChan, kvClient,
          idAbstract, network, broadcastChan, database, iAmTheLeaderAbstract,
          requestsRead, requestsWrite, iAmTheLeaderRead, proposerChanWrite,
          paxosChanRead, paxosChanWrite, upstreamWrite, proposerChanWrite0,
          paxosChanWrite0, upstreamWrite0, requestsWrite0, proposerChanWrite1,
          paxosChanWrite1, upstreamWrite1, learnerChanRead, learnerChanWrite,
          kvIdRead, dbWrite, dbWrite0, kvIdRead0, kvIdRead1, dbRead,
          kvIdRead2, requestServiceWrite, requestServiceWrite0,
          learnerChanWrite0, dbWrite1, requestServiceWrite1,
          proposerChansRead, proposerChansWrite, learnerChanWrite1,
          proposerChansWrite0, learnerChanWrite2, bcastChanRead,
          bcastChanWrite, proposerChansWrite1, proposerChansWrite2,
          bcastChanWrite0, proposerChansWrite3, pc

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
          msg_c, learnerId, proposerId, msg, j

vars == << values, requestSet, learnedChan, paxosLayerChan, kvClient,
           idAbstract, network, broadcastChan, database, iAmTheLeaderAbstract,
           requestsRead, requestsWrite, iAmTheLeaderRead, proposerChanWrite,
           paxosChanRead, paxosChanWrite, upstreamWrite, proposerChanWrite0,
           paxosChanWrite0, upstreamWrite0, requestsWrite0,
           proposerChanWrite1, paxosChanWrite1, upstreamWrite1,
           learnerChanRead, learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
           kvIdRead0, kvIdRead1, dbRead, kvIdRead2, requestServiceWrite,
           requestServiceWrite0, learnerChanWrite0, dbWrite1,
           requestServiceWrite1, proposerChansRead, proposerChansWrite,
           learnerChanWrite1, proposerChansWrite0, learnerChanWrite2,
           bcastChanRead, bcastChanWrite, proposerChansWrite1,
           proposerChansWrite2, bcastChanWrite0, proposerChansWrite3, pc,
           msg_, null, heartbeatId, proposerId_, counter, requestId,
           requestOk, confirmedRequestId, proposal, result_, result,
           learnerId_, decided, msg_c, learnerId, proposerId, msg, j >>

ProcSet == (KVRequests) \cup (KVPaxosManager) \cup (ConsensusSet) \cup {(8) * (NUM_NODES)}

Init == (* Global variables *)
        /\ values = [k \in Proposer |-> <<>>]
        /\ requestSet = (({[type |-> GET_MSG, key |-> k, value |-> NULL] : k \in GetSet}) \union ({[type |-> PUT_MSG, key |-> v, value |-> v] : v \in PutSet}))
        /\ learnedChan = [l \in Learner |-> <<>>]
        /\ paxosLayerChan = [p \in KVRequests |-> <<>>]
        /\ kvClient = {}
        /\ idAbstract = defaultInitValue
        /\ network = [c \in ConsensusSet |-> <<>>]
        /\ broadcastChan = {}
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
        /\ learnerChanWrite = defaultInitValue
        /\ kvIdRead = defaultInitValue
        /\ dbWrite = defaultInitValue
        /\ dbWrite0 = defaultInitValue
        /\ kvIdRead0 = defaultInitValue
        /\ kvIdRead1 = defaultInitValue
        /\ dbRead = defaultInitValue
        /\ kvIdRead2 = defaultInitValue
        /\ requestServiceWrite = defaultInitValue
        /\ requestServiceWrite0 = defaultInitValue
        /\ learnerChanWrite0 = defaultInitValue
        /\ dbWrite1 = defaultInitValue
        /\ requestServiceWrite1 = defaultInitValue
        /\ proposerChansRead = defaultInitValue
        /\ proposerChansWrite = defaultInitValue
        /\ learnerChanWrite1 = defaultInitValue
        /\ proposerChansWrite0 = defaultInitValue
        /\ learnerChanWrite2 = defaultInitValue
        /\ bcastChanRead = defaultInitValue
        /\ bcastChanWrite = defaultInitValue
        /\ proposerChansWrite1 = defaultInitValue
        /\ proposerChansWrite2 = defaultInitValue
        /\ bcastChanWrite0 = defaultInitValue
        /\ proposerChansWrite3 = defaultInitValue
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
        /\ msg_c = [self \in ConsensusSet |-> defaultInitValue]
        /\ learnerId = [self \in ConsensusSet |-> defaultInitValue]
        /\ proposerId = [self \in ConsensusSet |-> defaultInitValue]
        (* Process consensusBroadcast *)
        /\ msg = defaultInitValue
        /\ j = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in KVRequests -> "kvInit"
                                        [] self \in KVPaxosManager -> "findId"
                                        [] self \in ConsensusSet -> "findIds"
                                        [] self = (8) * (NUM_NODES) -> "broadcastLoop"]

kvInit(self) == /\ pc[self] = "kvInit"
                /\ heartbeatId' = [heartbeatId EXCEPT ![self] = (self) - ((2) * (NUM_NODES))]
                /\ proposerId_' = [proposerId_ EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                /\ UNCHANGED << values, requestSet, learnedChan,
                                paxosLayerChan, kvClient, idAbstract, network,
                                broadcastChan, database, iAmTheLeaderAbstract,
                                requestsRead, requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead,
                                learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
                                kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
                                requestServiceWrite, requestServiceWrite0,
                                learnerChanWrite0, dbWrite1,
                                requestServiceWrite1, proposerChansRead,
                                proposerChansWrite, learnerChanWrite1,
                                proposerChansWrite0, learnerChanWrite2,
                                bcastChanRead, bcastChanWrite,
                                proposerChansWrite1, proposerChansWrite2,
                                bcastChanWrite0, proposerChansWrite3, msg_,
                                null, counter, requestId, requestOk,
                                confirmedRequestId, proposal, result_, result,
                                learnerId_, decided, msg_c, learnerId,
                                proposerId, msg, j >>

kvLoop(self) == /\ pc[self] = "kvLoop"
                /\ IF TRUE
                      THEN /\ (Cardinality(requestSet)) > (0)
                           /\ \E req0 \in requestSet:
                                /\ requestsWrite' = (requestSet) \ ({req0})
                                /\ requestsRead' = req0
                           /\ msg_' = [msg_ EXCEPT ![self] = requestsRead']
                           /\ Assert((((msg_'[self]).type) = (GET_MSG)) \/ (((msg_'[self]).type) = (PUT_MSG)),
                                     "Failure of assertion at line 261, column 17.")
                           /\ iAmTheLeaderRead' = iAmTheLeaderAbstract[heartbeatId[self]]
                           /\ IF iAmTheLeaderRead'
                                 THEN /\ requestId' = [requestId EXCEPT ![self] = <<self, counter[self]>>]
                                      /\ IF ((msg_'[self]).type) = (GET_MSG)
                                            THEN /\ proposal' = [proposal EXCEPT ![self] = [operation |-> GET, id |-> requestId'[self], key |-> (msg_'[self]).key, value |-> (msg_'[self]).key]]
                                            ELSE /\ proposal' = [proposal EXCEPT ![self] = [operation |-> PUT, id |-> requestId'[self], key |-> (msg_'[self]).key, value |-> (msg_'[self]).value]]
                                      /\ proposerChanWrite' = ((broadcastChan) \union ({proposal'[self]}))
                                      /\ requestSet' = requestsWrite'
                                      /\ broadcastChan' = proposerChanWrite'
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
                                      /\ proposerChanWrite0' = broadcastChan
                                      /\ paxosChanWrite0' = paxosLayerChan
                                      /\ upstreamWrite0' = upstreamWrite'
                                      /\ requestsWrite0' = requestsWrite'
                                      /\ proposerChanWrite1' = proposerChanWrite0'
                                      /\ paxosChanWrite1' = paxosChanWrite0'
                                      /\ upstreamWrite1' = upstreamWrite0'
                                      /\ requestSet' = requestsWrite0'
                                      /\ kvClient' = upstreamWrite1'
                                      /\ broadcastChan' = proposerChanWrite1'
                                      /\ paxosLayerChan' = paxosChanWrite1'
                                      /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                                      /\ UNCHANGED << proposerChanWrite,
                                                      requestId, proposal >>
                      ELSE /\ requestsWrite0' = requestSet
                           /\ proposerChanWrite1' = broadcastChan
                           /\ paxosChanWrite1' = paxosLayerChan
                           /\ upstreamWrite1' = kvClient
                           /\ requestSet' = requestsWrite0'
                           /\ kvClient' = upstreamWrite1'
                           /\ broadcastChan' = proposerChanWrite1'
                           /\ paxosLayerChan' = paxosChanWrite1'
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << requestsRead, requestsWrite,
                                           iAmTheLeaderRead, proposerChanWrite,
                                           upstreamWrite, proposerChanWrite0,
                                           paxosChanWrite0, upstreamWrite0,
                                           msg_, requestId, proposal >>
                /\ UNCHANGED << values, learnedChan, idAbstract, network,
                                database, iAmTheLeaderAbstract, paxosChanRead,
                                paxosChanWrite, learnerChanRead,
                                learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
                                kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
                                requestServiceWrite, requestServiceWrite0,
                                learnerChanWrite0, dbWrite1,
                                requestServiceWrite1, proposerChansRead,
                                proposerChansWrite, learnerChanWrite1,
                                proposerChansWrite0, learnerChanWrite2,
                                bcastChanRead, bcastChanWrite,
                                proposerChansWrite1, proposerChansWrite2,
                                bcastChanWrite0, proposerChansWrite3, null,
                                heartbeatId, proposerId_, counter, requestOk,
                                confirmedRequestId, result_, result,
                                learnerId_, decided, msg_c, learnerId,
                                proposerId, msg, j >>

requestConfirm(self) == /\ pc[self] = "requestConfirm"
                        /\ (Len(paxosLayerChan[self])) > (0)
                        /\ LET msg0 == Head(paxosLayerChan[self]) IN
                             /\ paxosChanWrite' = [paxosLayerChan EXCEPT ![self] = Tail(paxosLayerChan[self])]
                             /\ paxosChanRead' = msg0
                        /\ result_' = [result_ EXCEPT ![self] = paxosChanRead']
                        /\ upstreamWrite' = ((kvClient) \union ({[type |-> OK_MSG, result |-> result_'[self]]}))
                        /\ counter' = [counter EXCEPT ![self] = (counter[self]) + (1)]
                        /\ kvClient' = upstreamWrite'
                        /\ paxosLayerChan' = paxosChanWrite'
                        /\ pc' = [pc EXCEPT ![self] = "kvLoop"]
                        /\ UNCHANGED << values, requestSet, learnedChan,
                                        idAbstract, network, broadcastChan,
                                        database, iAmTheLeaderAbstract,
                                        requestsRead, requestsWrite,
                                        iAmTheLeaderRead, proposerChanWrite,
                                        proposerChanWrite0, paxosChanWrite0,
                                        upstreamWrite0, requestsWrite0,
                                        proposerChanWrite1, paxosChanWrite1,
                                        upstreamWrite1, learnerChanRead,
                                        learnerChanWrite, kvIdRead, dbWrite,
                                        dbWrite0, kvIdRead0, kvIdRead1, dbRead,
                                        kvIdRead2, requestServiceWrite,
                                        requestServiceWrite0,
                                        learnerChanWrite0, dbWrite1,
                                        requestServiceWrite1,
                                        proposerChansRead, proposerChansWrite,
                                        learnerChanWrite1, proposerChansWrite0,
                                        learnerChanWrite2, bcastChanRead,
                                        bcastChanWrite, proposerChansWrite1,
                                        proposerChansWrite2, bcastChanWrite0,
                                        proposerChansWrite3, msg_, null,
                                        heartbeatId, proposerId_, requestId,
                                        requestOk, confirmedRequestId,
                                        proposal, result, learnerId_, decided,
                                        msg_c, learnerId, proposerId, msg, j >>

kvRequests(self) == kvInit(self) \/ kvLoop(self) \/ requestConfirm(self)

findId(self) == /\ pc[self] = "findId"
                /\ learnerId_' = [learnerId_ EXCEPT ![self] = (self) - ((4) * (NUM_NODES))]
                /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                /\ UNCHANGED << values, requestSet, learnedChan,
                                paxosLayerChan, kvClient, idAbstract, network,
                                broadcastChan, database, iAmTheLeaderAbstract,
                                requestsRead, requestsWrite, iAmTheLeaderRead,
                                proposerChanWrite, paxosChanRead,
                                paxosChanWrite, upstreamWrite,
                                proposerChanWrite0, paxosChanWrite0,
                                upstreamWrite0, requestsWrite0,
                                proposerChanWrite1, paxosChanWrite1,
                                upstreamWrite1, learnerChanRead,
                                learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
                                kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
                                requestServiceWrite, requestServiceWrite0,
                                learnerChanWrite0, dbWrite1,
                                requestServiceWrite1, proposerChansRead,
                                proposerChansWrite, learnerChanWrite1,
                                proposerChansWrite0, learnerChanWrite2,
                                bcastChanRead, bcastChanWrite,
                                proposerChansWrite1, proposerChansWrite2,
                                bcastChanWrite0, proposerChansWrite3, msg_,
                                null, heartbeatId, proposerId_, counter,
                                requestId, requestOk, confirmedRequestId,
                                proposal, result_, result, decided, msg_c,
                                learnerId, proposerId, msg, j >>

kvManagerLoop(self) == /\ pc[self] = "kvManagerLoop"
                       /\ IF TRUE
                             THEN /\ (Len(learnedChan[learnerId_[self]])) > (0)
                                  /\ LET msg1 == Head(learnedChan[learnerId_[self]]) IN
                                       /\ learnerChanWrite' = [learnedChan EXCEPT ![learnerId_[self]] = Tail(learnedChan[learnerId_[self]])]
                                       /\ learnerChanRead' = msg1
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
                                             /\ (Len(paxosLayerChan[kvIdRead2'])) < (BUFFER_SIZE)
                                             /\ requestServiceWrite' = [paxosLayerChan EXCEPT ![kvIdRead2'] = Append(paxosLayerChan[kvIdRead2'], result'[self])]
                                             /\ requestServiceWrite0' = requestServiceWrite'
                                             /\ learnerChanWrite0' = learnerChanWrite'
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ learnedChan' = learnerChanWrite0'
                                             /\ database' = dbWrite1'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                        ELSE /\ requestServiceWrite0' = paxosLayerChan
                                             /\ learnerChanWrite0' = learnerChanWrite'
                                             /\ dbWrite1' = dbWrite0'
                                             /\ requestServiceWrite1' = requestServiceWrite0'
                                             /\ paxosLayerChan' = requestServiceWrite1'
                                             /\ learnedChan' = learnerChanWrite0'
                                             /\ database' = dbWrite1'
                                             /\ pc' = [pc EXCEPT ![self] = "kvManagerLoop"]
                                             /\ UNCHANGED << kvIdRead1, dbRead,
                                                             kvIdRead2,
                                                             requestServiceWrite,
                                                             result >>
                             ELSE /\ learnerChanWrite0' = learnedChan
                                  /\ dbWrite1' = database
                                  /\ requestServiceWrite1' = paxosLayerChan
                                  /\ paxosLayerChan' = requestServiceWrite1'
                                  /\ learnedChan' = learnerChanWrite0'
                                  /\ database' = dbWrite1'
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << learnerChanRead,
                                                  learnerChanWrite, kvIdRead,
                                                  dbWrite, dbWrite0, kvIdRead0,
                                                  kvIdRead1, dbRead, kvIdRead2,
                                                  requestServiceWrite,
                                                  requestServiceWrite0, result,
                                                  decided >>
                       /\ UNCHANGED << values, requestSet, kvClient,
                                       idAbstract, network, broadcastChan,
                                       iAmTheLeaderAbstract, requestsRead,
                                       requestsWrite, iAmTheLeaderRead,
                                       proposerChanWrite, paxosChanRead,
                                       paxosChanWrite, upstreamWrite,
                                       proposerChanWrite0, paxosChanWrite0,
                                       upstreamWrite0, requestsWrite0,
                                       proposerChanWrite1, paxosChanWrite1,
                                       upstreamWrite1, proposerChansRead,
                                       proposerChansWrite, learnerChanWrite1,
                                       proposerChansWrite0, learnerChanWrite2,
                                       bcastChanRead, bcastChanWrite,
                                       proposerChansWrite1,
                                       proposerChansWrite2, bcastChanWrite0,
                                       proposerChansWrite3, msg_, null,
                                       heartbeatId, proposerId_, counter,
                                       requestId, requestOk,
                                       confirmedRequestId, proposal, result_,
                                       learnerId_, msg_c, learnerId,
                                       proposerId, msg, j >>

kvPaxosManager(self) == findId(self) \/ kvManagerLoop(self)

findIds(self) == /\ pc[self] = "findIds"
                 /\ learnerId' = [learnerId EXCEPT ![self] = (self) - ((5) * (NUM_NODES))]
                 /\ pc' = [pc EXCEPT ![self] = "consensusLoop"]
                 /\ UNCHANGED << values, requestSet, learnedChan,
                                 paxosLayerChan, kvClient, idAbstract, network,
                                 broadcastChan, database, iAmTheLeaderAbstract,
                                 requestsRead, requestsWrite, iAmTheLeaderRead,
                                 proposerChanWrite, paxosChanRead,
                                 paxosChanWrite, upstreamWrite,
                                 proposerChanWrite0, paxosChanWrite0,
                                 upstreamWrite0, requestsWrite0,
                                 proposerChanWrite1, paxosChanWrite1,
                                 upstreamWrite1, learnerChanRead,
                                 learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
                                 kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
                                 requestServiceWrite, requestServiceWrite0,
                                 learnerChanWrite0, dbWrite1,
                                 requestServiceWrite1, proposerChansRead,
                                 proposerChansWrite, learnerChanWrite1,
                                 proposerChansWrite0, learnerChanWrite2,
                                 bcastChanRead, bcastChanWrite,
                                 proposerChansWrite1, proposerChansWrite2,
                                 bcastChanWrite0, proposerChansWrite3, msg_,
                                 null, heartbeatId, proposerId_, counter,
                                 requestId, requestOk, confirmedRequestId,
                                 proposal, result_, result, learnerId_,
                                 decided, msg_c, proposerId, msg, j >>

consensusLoop(self) == /\ pc[self] = "consensusLoop"
                       /\ IF TRUE
                             THEN /\ (Len(network[self])) > (0)
                                  /\ LET msg2 == Head(network[self]) IN
                                       /\ proposerChansWrite' = [network EXCEPT ![self] = Tail(network[self])]
                                       /\ proposerChansRead' = msg2
                                  /\ msg_c' = [msg_c EXCEPT ![self] = proposerChansRead']
                                  /\ network' = proposerChansWrite'
                                  /\ pc' = [pc EXCEPT ![self] = "sendLearner"]
                                  /\ UNCHANGED << learnedChan,
                                                  proposerChansWrite0,
                                                  learnerChanWrite2 >>
                             ELSE /\ proposerChansWrite0' = network
                                  /\ learnerChanWrite2' = learnedChan
                                  /\ network' = proposerChansWrite0'
                                  /\ learnedChan' = learnerChanWrite2'
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << proposerChansRead,
                                                  proposerChansWrite, msg_c >>
                       /\ UNCHANGED << values, requestSet, paxosLayerChan,
                                       kvClient, idAbstract, broadcastChan,
                                       database, iAmTheLeaderAbstract,
                                       requestsRead, requestsWrite,
                                       iAmTheLeaderRead, proposerChanWrite,
                                       paxosChanRead, paxosChanWrite,
                                       upstreamWrite, proposerChanWrite0,
                                       paxosChanWrite0, upstreamWrite0,
                                       requestsWrite0, proposerChanWrite1,
                                       paxosChanWrite1, upstreamWrite1,
                                       learnerChanRead, learnerChanWrite,
                                       kvIdRead, dbWrite, dbWrite0, kvIdRead0,
                                       kvIdRead1, dbRead, kvIdRead2,
                                       requestServiceWrite,
                                       requestServiceWrite0, learnerChanWrite0,
                                       dbWrite1, requestServiceWrite1,
                                       learnerChanWrite1, bcastChanRead,
                                       bcastChanWrite, proposerChansWrite1,
                                       proposerChansWrite2, bcastChanWrite0,
                                       proposerChansWrite3, msg_, null,
                                       heartbeatId, proposerId_, counter,
                                       requestId, requestOk,
                                       confirmedRequestId, proposal, result_,
                                       result, learnerId_, decided, learnerId,
                                       proposerId, msg, j >>

sendLearner(self) == /\ pc[self] = "sendLearner"
                     /\ (Len(learnedChan[learnerId[self]])) < (BUFFER_SIZE)
                     /\ learnerChanWrite1' = [learnedChan EXCEPT ![learnerId[self]] = Append(learnedChan[learnerId[self]], msg_c[self])]
                     /\ learnedChan' = learnerChanWrite1'
                     /\ pc' = [pc EXCEPT ![self] = "consensusLoop"]
                     /\ UNCHANGED << values, requestSet, paxosLayerChan,
                                     kvClient, idAbstract, network,
                                     broadcastChan, database,
                                     iAmTheLeaderAbstract, requestsRead,
                                     requestsWrite, iAmTheLeaderRead,
                                     proposerChanWrite, paxosChanRead,
                                     paxosChanWrite, upstreamWrite,
                                     proposerChanWrite0, paxosChanWrite0,
                                     upstreamWrite0, requestsWrite0,
                                     proposerChanWrite1, paxosChanWrite1,
                                     upstreamWrite1, learnerChanRead,
                                     learnerChanWrite, kvIdRead, dbWrite,
                                     dbWrite0, kvIdRead0, kvIdRead1, dbRead,
                                     kvIdRead2, requestServiceWrite,
                                     requestServiceWrite0, learnerChanWrite0,
                                     dbWrite1, requestServiceWrite1,
                                     proposerChansRead, proposerChansWrite,
                                     proposerChansWrite0, learnerChanWrite2,
                                     bcastChanRead, bcastChanWrite,
                                     proposerChansWrite1, proposerChansWrite2,
                                     bcastChanWrite0, proposerChansWrite3,
                                     msg_, null, heartbeatId, proposerId_,
                                     counter, requestId, requestOk,
                                     confirmedRequestId, proposal, result_,
                                     result, learnerId_, decided, msg_c,
                                     learnerId, proposerId, msg, j >>

consensus(self) == findIds(self) \/ consensusLoop(self)
                      \/ sendLearner(self)

broadcastLoop == /\ pc[(8) * (NUM_NODES)] = "broadcastLoop"
                 /\ IF TRUE
                       THEN /\ \E e0 \in broadcastChan:
                                 /\ bcastChanWrite' = (broadcastChan) \ ({e0})
                                 /\ bcastChanRead' = e0
                            /\ msg' = bcastChanRead'
                            /\ j' = (7) * (NUM_NODES)
                            /\ broadcastChan' = bcastChanWrite'
                            /\ pc' = [pc EXCEPT ![(8) * (NUM_NODES)] = "broadcastMessage"]
                            /\ UNCHANGED << network, bcastChanWrite0,
                                            proposerChansWrite3 >>
                       ELSE /\ bcastChanWrite0' = broadcastChan
                            /\ proposerChansWrite3' = network
                            /\ broadcastChan' = bcastChanWrite0'
                            /\ network' = proposerChansWrite3'
                            /\ pc' = [pc EXCEPT ![(8) * (NUM_NODES)] = "Done"]
                            /\ UNCHANGED << bcastChanRead, bcastChanWrite, msg,
                                            j >>
                 /\ UNCHANGED << values, requestSet, learnedChan,
                                 paxosLayerChan, kvClient, idAbstract,
                                 database, iAmTheLeaderAbstract, requestsRead,
                                 requestsWrite, iAmTheLeaderRead,
                                 proposerChanWrite, paxosChanRead,
                                 paxosChanWrite, upstreamWrite,
                                 proposerChanWrite0, paxosChanWrite0,
                                 upstreamWrite0, requestsWrite0,
                                 proposerChanWrite1, paxosChanWrite1,
                                 upstreamWrite1, learnerChanRead,
                                 learnerChanWrite, kvIdRead, dbWrite, dbWrite0,
                                 kvIdRead0, kvIdRead1, dbRead, kvIdRead2,
                                 requestServiceWrite, requestServiceWrite0,
                                 learnerChanWrite0, dbWrite1,
                                 requestServiceWrite1, proposerChansRead,
                                 proposerChansWrite, learnerChanWrite1,
                                 proposerChansWrite0, learnerChanWrite2,
                                 proposerChansWrite1, proposerChansWrite2,
                                 msg_, null, heartbeatId, proposerId_, counter,
                                 requestId, requestOk, confirmedRequestId,
                                 proposal, result_, result, learnerId_,
                                 decided, msg_c, learnerId, proposerId >>

broadcastMessage == /\ pc[(8) * (NUM_NODES)] = "broadcastMessage"
                    /\ IF (j) <= (((8) * (NUM_NODES)) - (1))
                          THEN /\ (Len(network[j])) < (BUFFER_SIZE)
                               /\ proposerChansWrite1' = [network EXCEPT ![j] = Append(network[j], msg)]
                               /\ proposerChansWrite2' = proposerChansWrite1'
                               /\ network' = proposerChansWrite2'
                               /\ pc' = [pc EXCEPT ![(8) * (NUM_NODES)] = "broadcastMessage"]
                          ELSE /\ proposerChansWrite2' = network
                               /\ network' = proposerChansWrite2'
                               /\ pc' = [pc EXCEPT ![(8) * (NUM_NODES)] = "broadcastLoop"]
                               /\ UNCHANGED proposerChansWrite1
                    /\ UNCHANGED << values, requestSet, learnedChan,
                                    paxosLayerChan, kvClient, idAbstract,
                                    broadcastChan, database,
                                    iAmTheLeaderAbstract, requestsRead,
                                    requestsWrite, iAmTheLeaderRead,
                                    proposerChanWrite, paxosChanRead,
                                    paxosChanWrite, upstreamWrite,
                                    proposerChanWrite0, paxosChanWrite0,
                                    upstreamWrite0, requestsWrite0,
                                    proposerChanWrite1, paxosChanWrite1,
                                    upstreamWrite1, learnerChanRead,
                                    learnerChanWrite, kvIdRead, dbWrite,
                                    dbWrite0, kvIdRead0, kvIdRead1, dbRead,
                                    kvIdRead2, requestServiceWrite,
                                    requestServiceWrite0, learnerChanWrite0,
                                    dbWrite1, requestServiceWrite1,
                                    proposerChansRead, proposerChansWrite,
                                    learnerChanWrite1, proposerChansWrite0,
                                    learnerChanWrite2, bcastChanRead,
                                    bcastChanWrite, bcastChanWrite0,
                                    proposerChansWrite3, msg_, null,
                                    heartbeatId, proposerId_, counter,
                                    requestId, requestOk, confirmedRequestId,
                                    proposal, result_, result, learnerId_,
                                    decided, msg_c, learnerId, proposerId, msg,
                                    j >>

consensusBroadcast == broadcastLoop \/ broadcastMessage

Next == consensusBroadcast
           \/ (\E self \in KVRequests: kvRequests(self))
           \/ (\E self \in KVPaxosManager: kvPaxosManager(self))
           \/ (\E self \in ConsensusSet: consensus(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in KVRequests : WF_vars(kvRequests(self))
        /\ \A self \in KVPaxosManager : WF_vars(kvPaxosManager(self))
        /\ \A self \in ConsensusSet : WF_vars(consensus(self))
        /\ WF_vars(consensusBroadcast)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\*  Every KV node has a consistent database (this is only true if the keys used in PUT operations are distinct)
\* ConsistentDatabase == \A kv1, kv2 \in KVRequests, k \in PutSet :
\*                           database[kv1, k] # NULL /\ database[kv2, k] # NULL => database[kv1, k] = database[kv2, k]

ConsistentDatabase == \A kv1 \in KVRequests, k \in PutSet : database[kv1, k] = NULL_DB_VALUE \/ database[kv1, k] = k

\* Eventually the database of every node is populated with the associated value
\* All PUT operations performed are in the format: Put(key, key)
Progress == \A kv1, kv2 \in KVRequests, k \in PutSet : <>(database[kv1, k] = database[kv2, k])

\* Termination formula:
\* ~(\A k \in PutSet : \E kv \in KVRequests : database[kv, k] # NULL)

=========================================================
