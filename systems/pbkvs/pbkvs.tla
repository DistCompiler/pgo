------------------------------- MODULE pbkvs -------------------------------

(********************
A key-value store that uses primary-backup replication. We used the following
document as the reference:
    http://www.sc.ehu.es/acwlaalm/sdi/replication-schemas.pdf

Assumptions:
    - Crash-stop failure model
    - Having access to a perfect failure detector

In each step of the execution, we consider a replica as the primary that has 
the lowest id amongst all alive replicas. Primary synchronously replicates
requests to backup nodes. Clients must send write requests only to the primary
replica. The primary always has the same state as backups or the primary is one 
step ahead.  Therefore, reading from a backup might return an old value. In
this spec, read requests are sent only to the primary.

If the primary node fails while processing a write request, the client won't
receive any response back. If the primary replicated the write request to at
least one backup node, the request will be applied to the system, otherwise, it
won't. Therefore, the system provides no guarantee when a client don't receive a 
response for its write request. However, it's fine since the client retries and
all operations are idempotent.

We define consistency property for this system as:
    When primary node sends a response back to a client, all replicas (including 
    primary) have a same state.
********************)

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_REPLICAS
CONSTANT NUM_CLIENTS
CONSTANT EXPLORE_FAIL
CONSTANT DEBUG

ASSUME NUM_REPLICAS > 0 /\ NUM_CLIENTS >= 0

(********************

--mpcal pbkvs {

    define {
        NUM_NODES == NUM_REPLICAS + NUM_CLIENTS

        CLIENT_SRC == 1
        PRIMARY_SRC == 2
        BACKUP_SRC == 3

        GET_REQ == 1
        GET_RESP == 2
        PUT_REQ == 3
        PUT_RESP == 4
        SYNC_REQ == 5
        SYNC_RESP == 6

        REQ_INDEX == 1
        RESP_INDEX == 2

        ACK_MSG_BODY == [content |-> "ack-body"]

        KEY1   == "KEY1"
        VALUE1 == "VALUE1"
        VALUE2 == "VALUE2"

        KEY_SET == {KEY1}

        NODE_SET == 1..NUM_NODES
        REPLICA_SET == 1..NUM_REPLICAS
        CLIENT_SET == (NUM_REPLICAS+1)..(NUM_REPLICAS+NUM_CLIENTS)

        MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}

        NULL == 0
    }

    macro mayFail(selfID, netEnabled) {
        if (EXPLORE_FAIL) {
            either { skip; } or {
                netEnabled[<<selfID, REQ_INDEX>>] := FALSE;
                netEnabled[<<selfID, RESP_INDEX>>] := FALSE;
                goto failLabel;
            };
        };
    }

    macro debug(toPrint) {
        if (DEBUG) {
            print toPrint;
        };
    }

    mapping macro ReliableFIFOLink {
        read {
            assert $variable.enabled;
            await Len($variable.queue) > 0;
            with (readMsg = Head($variable.queue)) {
                $variable := [queue |-> Tail($variable.queue), enabled |-> $variable.enabled];
                yield readMsg;
            };
        }

        write {
            await $variable.enabled;
            yield [queue |-> Append($variable.queue, $value), enabled |-> $variable.enabled];
        }
    }

    mapping macro NetworkToggle {
        read { yield $variable.enabled; }

        write {
            yield [queue |-> $variable.queue, enabled |-> $value];
        }
    }

    mapping macro PerfectFD {
        read {
            yield $variable;
        }

        write { yield $value; }
    }

    mapping macro PracticalFD {
        read {
            if ($variable = FALSE) { \* process is alive
                either { yield TRUE; } or { yield FALSE; }; \* no accuracy guarantee
            } else {
                yield $variable; \* (eventual) completeness
            };
        }

        write { yield $value; }
    }

    mapping macro FileSystem {
        read { yield $variable; }

        write { yield $value; }
    }

    mapping macro LeaderElection {
        read {
            if (Cardinality($variable) > 0) {
                \* it's safe to use CHOOSE construct here since the set
                \* {x \in $variable: \A r \in $variable: x =< r} has exactly
                \* one element.
                yield CHOOSE x \in $variable: \A r \in $variable: x =< r;

				\* alternative version using with statement
                \* with (leader \in {x \in $variable: \A r \in $variable: x =< r}) {
                \*     yield leader;
                \* }
            } else {
                yield NULL;
            }
        }

        write {
            yield $variable \ {$value};
        }
    }

    mapping macro NetworkBufferLength {
        read {
            yield Len($variable.queue);
        }

        write {
            assert FALSE;
            yield $value;
        }
    }

    mapping macro Channel {
        read {
            await Len($variable) > 0;
            with (res = Head($variable)) {
                $variable := Tail($variable);
                yield res;
            };
        }

        write {
            yield Append($variable, $value);
        }
    }

    archetype AReplica(ref net[_], ref fs[_][_], ref fd[_], ref netEnabled[_], ref primary, ref netLen[_])
    variables
        req, respBody, respTyp, idx, repReq, repResp, resp, replicaSet, shouldSync = FALSE, lastPutBody = [versionNumber |-> 0], replica;
    {
    replicaLoop:
        while (TRUE) {
            replicaSet := REPLICA_SET \ {self};
            idx := 1;
            mayFail(self, netEnabled);

        syncPrimary:
            if (primary = self /\ shouldSync) {
                shouldSync := FALSE;
            sndSyncReqLoop:
                while (idx <= NUM_REPLICAS) {
                    if (idx # self) {
                        either {
                            repReq := [from |-> self, to |-> idx, body |-> lastPutBody,
                                       srcTyp |-> PRIMARY_SRC, typ |-> SYNC_REQ, id |-> 3];
                            net[<<idx, REQ_INDEX>>] := repReq;
                        } or {
                            await fd[idx];
                        };
                    };
                    idx := idx + 1;
                    mayFail(self, netEnabled);
                };

            rcvSyncRespLoop:
                while (Cardinality(replicaSet) > 0) {
                    either {
                        repResp := net[<<self, RESP_INDEX>>];
                        assert(
                            /\ repResp.id = 3
                            /\ repResp.to = self
                            /\ repResp.srcTyp = BACKUP_SRC
                            /\ repResp.typ = SYNC_RESP
                            /\ \/ repResp.from \in replicaSet
                               \/ fd[repResp.from]
                        );

                        if (repResp.body.versionNumber > lastPutBody.versionNumber) {
                            fs[self][repResp.body.key] := repResp.body.value;
                            lastPutBody := repResp.body;
                            replicaSet := REPLICA_SET \ {self};
                            idx := 1;
                            goto sndSyncReqLoop;
                        } else {
                            replicaSet := replicaSet \ {repResp.from};
                        };
                    } or {
                        \* there is no need for branching here, so for having a better
                        \* verification performance we use CHOOSE construct.
                        replica := CHOOSE r \in replicaSet: TRUE;
                        await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                        replicaSet := replicaSet \ {replica};
                    };
                };
            };

        rcvMsg:
            if (primary = self /\ shouldSync) {
                goto syncPrimary;
            } else {
                req := net[<<self, REQ_INDEX>>];
                debug(<<"ServerRcvReq", self, req>>);
                assert(req.to = self);
                if (primary = self /\ req.srcTyp = CLIENT_SRC) {
                    goto handlePrimary;
                } else {
                    goto handleBackup;
                };
            };

        handleBackup:
            debug(<<"ServerHandleBackup", self>>);
            assert(req.srcTyp = PRIMARY_SRC);
            if (req.typ = GET_REQ) {
                respBody := [content |-> fs[self][req.body.key]];
                respTyp := GET_RESP;
            } else if (req.typ = PUT_REQ) {
                fs[self][req.body.key] := req.body.value;
                assert(req.body.versionNumber >= lastPutBody.versionNumber);
                lastPutBody := req.body;
                respBody := ACK_MSG_BODY;
                respTyp := PUT_RESP;
                shouldSync := TRUE;
            } else if (req.typ = SYNC_REQ) {
                if (req.body.versionNumber > lastPutBody.versionNumber) {
                    fs[self][req.body.key] := req.body.value;
                    lastPutBody := req.body;
                };
                respBody := lastPutBody;
                respTyp := SYNC_RESP;
                shouldSync := TRUE;
            };
            resp := [from |-> self, to |-> req.from, body |-> respBody,
                     srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> req.id];
            either {
                net[<<resp.to, RESP_INDEX>>] := resp;
            } or {
                await fd[resp.to];
            };
            goto replicaLoop;

        handlePrimary:
            debug(<<"ServerHandlePrimary", self>>);
            assert(req.srcTyp = CLIENT_SRC);
            if (req.typ = GET_REQ) {
                respBody := [content |-> fs[self][req.body.key]];
                respTyp := GET_RESP;
                goto sndResp;
            } else if (req.typ = PUT_REQ) {
                fs[self][req.body.key] := req.body.value;
                lastPutBody := [versionNumber |-> lastPutBody.versionNumber+1, key |-> req.body.key, value |-> req.body.value];
                respBody := ACK_MSG_BODY;
                respTyp := PUT_RESP;
                replicaSet := REPLICA_SET \ {self};
                idx := 1;
                goto sndReplicaReqLoop;
            };

        sndReplicaReqLoop:
            while (idx <= NUM_REPLICAS) {
                if (idx # self) {
                    either {
                        repReq := [from |-> self, to |-> idx, body |-> lastPutBody,
                                   srcTyp |-> PRIMARY_SRC, typ |-> PUT_REQ, id |-> req.id];
                        net[<<idx, REQ_INDEX>>] := repReq;
                    } or {
                        await fd[idx];
                    };
                };
                idx := idx + 1;
                mayFail(self, netEnabled);
            };

        rcvReplicaRespLoop:
            while (Cardinality(replicaSet) > 0) {
                either {
                    repResp := net[<<self, RESP_INDEX>>];
                    assert(
                        /\ \/ repResp.from \in replicaSet 
                           \/ fd[repResp.from]
                        /\ repResp.to = self
                        /\ repResp.body = ACK_MSG_BODY
                        /\ repResp.srcTyp = BACKUP_SRC
                        /\ repResp.typ = PUT_RESP
                        /\ repResp.id = req.id
                    );
                    replicaSet := replicaSet \ {repResp.from};
                } or {
                    \* there is no need for branching here, so for having a better
                    \* verification performance we use CHOOSE construct.
                    replica := CHOOSE r \in replicaSet: TRUE;
                    await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                    replicaSet := replicaSet \ {replica};
                };
                mayFail(self, netEnabled);
            };

        sndResp:
            resp := [from |-> self, to |-> req.from, body |-> respBody,
                     srcTyp |-> PRIMARY_SRC, typ |-> respTyp, id |-> req.id];
            net[<<resp.to, RESP_INDEX>>] := resp;
            debug(<<"ServerSendResp", self, req.from>>);
        };

    failLabel:
        fd[self] := TRUE;
        primary := self;
    }

    archetype AClient(ref net[_], ref fd[_], ref primary, ref netLen[_], ref input, ref output)
    variables
        req, resp, msg, replica, idx = 0;
    {
    clientLoop:
        while (TRUE) {
            debug(<<"ClientLoop", self>>);
            msg := input;
            idx := idx + 1;

        sndReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    req := [from |-> self, to |-> replica, body |-> msg.body,
                            srcTyp |-> CLIENT_SRC, typ |-> msg.typ, id |-> idx];
                    net[<<req.to, REQ_INDEX>>] := req;
                    debug(<<"ClientSendReq", self, replica>>);
                } or {
                    await fd[replica];
                    goto sndReq; \* retry the request
                };
            } else {
                goto Done;
            };

        rcvResp:
            debug(<<"ClientRcvRespEither", self>>);
            either {
                resp := net[<<self, RESP_INDEX>>];
                debug(<<"ClientRcvResp", self, replica>>);
                if (resp.id # idx) {
                    goto rcvResp;
                } else {
                    if (msg.typ = PUT_REQ) {
                        assert(
                            /\ resp.to = self
                            /\ resp.from = replica
                            /\ resp.body = ACK_MSG_BODY
                            /\ resp.srcTyp = PRIMARY_SRC
                            /\ resp.typ = PUT_RESP
                            /\ resp.id = idx
                        );
                        output := resp.body.content;
                    } else if (msg.typ = GET_REQ) {
                        assert(
                            /\ resp.to = self
                            /\ resp.from = replica
                            /\ resp.srcTyp = PRIMARY_SRC
                            /\ resp.typ = GET_RESP
                            /\ resp.id = idx
                        );
                        output := resp.body.content;
                    } else {
                        assert FALSE;
                    };
                };
            } or {
                await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                debug(<<"ClientDetectedFail", self, replica>>);
                goto sndReq; \* retry the request
            };
        };
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]];
        fd = [id \in REPLICA_SET |-> FALSE];
        fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]];
        primary = REPLICA_SET;
        clientInput = <<
            [
                typ  |-> PUT_REQ,
                body |-> [key |-> KEY1, value |-> VALUE1]
            ],
            [
                typ  |-> PUT_REQ,
                body |-> [key |-> KEY1, value |-> VALUE2]
            ],
            [
                typ  |-> GET_REQ,
                body |-> [key |-> KEY1]
            ]
        >>;
        clientOutput;

    fair process (Replica \in REPLICA_SET) == instance AReplica(ref network[_], ref fs[_][_], ref fd[_], ref network[_], ref primary, ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_][_] via FileSystem
        mapping @3[_] via PerfectFD
        mapping @4[_] via NetworkToggle
        mapping @5 via LeaderElection
        mapping @6[_] via NetworkBufferLength;

    fair process (Client \in CLIENT_SET) == instance AClient(ref network[_], ref fd[_], ref primary, ref network[_], ref clientInput, ref clientOutput)
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3 via LeaderElection
        mapping @4[_] via NetworkBufferLength
        mapping @5 via Channel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm pbkvs {
  variables network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [id \in REPLICA_SET |-> FALSE]; fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]]; primary = REPLICA_SET; clientInput = <<[typ |-> PUT_REQ, body |-> [key |-> KEY1, value |-> VALUE1]], [typ |-> PUT_REQ, body |-> [key |-> KEY1, value |-> VALUE2]], [typ |-> GET_REQ, body |-> [key |-> KEY1]]>>; clientOutput;
  define{
    NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
    CLIENT_SRC == 1
    PRIMARY_SRC == 2
    BACKUP_SRC == 3
    GET_REQ == 1
    GET_RESP == 2
    PUT_REQ == 3
    PUT_RESP == 4
    SYNC_REQ == 5
    SYNC_RESP == 6
    REQ_INDEX == 1
    RESP_INDEX == 2
    ACK_MSG_BODY == [content |-> "ack-body"]
    KEY1 == "KEY1"
    VALUE1 == "VALUE1"
    VALUE2 == "VALUE2"
    KEY_SET == {KEY1}
    NODE_SET == (1) .. (NUM_NODES)
    REPLICA_SET == (1) .. (NUM_REPLICAS)
    CLIENT_SET == ((NUM_REPLICAS) + (1)) .. ((NUM_REPLICAS) + (NUM_CLIENTS))
    MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}
    NULL == 0
  }
  
  fair process (Replica \in REPLICA_SET)
    variables req; respBody; respTyp; idx; repReq; repResp; resp; replicaSet; shouldSync = FALSE; lastPutBody = [versionNumber |-> 0]; replica;
  {
    replicaLoop:
      if (TRUE) {
        replicaSet := (REPLICA_SET) \ ({self});
        idx := 1;
        if (EXPLORE_FAIL) {
          either {
            skip;
            goto syncPrimary;
          } or {
            with (
              value00 = FALSE, 
              network0 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value00]], 
              value19 = FALSE
            ) {
              network := [network0 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network0)[<<self, RESP_INDEX>>]).queue, enabled |-> value19]];
              goto failLabel;
            };
          };
        } else {
          goto syncPrimary;
        };
      } else {
        goto failLabel;
      };
    syncPrimary:
      if ((Cardinality(primary)) > (0)) {
        with (yielded_primary = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          if (((yielded_primary) = (self)) /\ (shouldSync)) {
            shouldSync := FALSE;
            goto sndSyncReqLoop;
          } else {
            goto rcvMsg;
          };
        };
      } else {
        with (yielded_primary0 = NULL) {
          if (((yielded_primary0) = (self)) /\ (shouldSync)) {
            shouldSync := FALSE;
            goto sndSyncReqLoop;
          } else {
            goto rcvMsg;
          };
        };
      };
    sndSyncReqLoop:
      if ((idx) <= (NUM_REPLICAS)) {
        if ((idx) # (self)) {
          either {
            repReq := [from |-> self, to |-> idx, body |-> lastPutBody, srcTyp |-> PRIMARY_SRC, typ |-> SYNC_REQ, id |-> 3];
            with (value20 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network1 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value20), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if (EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network1;
                    goto sndSyncReqLoop;
                  } or {
                    with (
                      value30 = FALSE, 
                      network2 = [network1 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network1)[<<self, REQ_INDEX>>]).queue, enabled |-> value30]], 
                      value40 = FALSE
                    ) {
                      network := [network2 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network2)[<<self, RESP_INDEX>>]).queue, enabled |-> value40]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network1;
                  goto sndSyncReqLoop;
                };
              };
            };
          } or {
            with (yielded_fd8 = (fd)[idx]) {
              await yielded_fd8;
              idx := (idx) + (1);
              if (EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndSyncReqLoop;
                } or {
                  with (
                    value31 = FALSE, 
                    network3 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value31]], 
                    value41 = FALSE
                  ) {
                    network := [network3 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network3)[<<self, RESP_INDEX>>]).queue, enabled |-> value41]];
                    goto failLabel;
                  };
                };
              } else {
                goto sndSyncReqLoop;
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if (EXPLORE_FAIL) {
            either {
              skip;
              goto sndSyncReqLoop;
            } or {
              with (
                value32 = FALSE, 
                network4 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value32]], 
                value42 = FALSE
              ) {
                network := [network4 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network4)[<<self, RESP_INDEX>>]).queue, enabled |-> value42]];
                goto failLabel;
              };
            };
          } else {
            goto sndSyncReqLoop;
          };
        };
      } else {
        goto rcvSyncRespLoop;
      };
    rcvSyncRespLoop:
      if ((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg00 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
            with (yielded_network6 = readMsg00) {
              repResp := yielded_network6;
              with (yielded_fd00 = (fd)[(repResp).from]) {
                assert ((((((repResp).id) = (3)) /\ (((repResp).to) = (self))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (SYNC_RESP))) /\ ((((repResp).from) \in (replicaSet)) \/ (yielded_fd00));
                if ((((repResp).body).versionNumber) > ((lastPutBody).versionNumber)) {
                  with (value50 = ((repResp).body).value) {
                    fs := [fs EXCEPT ![self][((repResp).body).key] = value50];
                    lastPutBody := (repResp).body;
                    replicaSet := (REPLICA_SET) \ ({self});
                    idx := 1;
                    goto sndSyncReqLoop;
                  };
                } else {
                  replicaSet := (replicaSet) \ ({(repResp).from});
                  goto rcvSyncRespLoop;
                };
              };
            };
          };
        } or {
          replica := CHOOSE r \in replicaSet : TRUE;
          with (
            yielded_fd10 = (fd)[replica], 
            yielded_network00 = Len(((network)[<<self, RESP_INDEX>>]).queue)
          ) {
            await (yielded_fd10) /\ ((yielded_network00) = (0));
            replicaSet := (replicaSet) \ ({replica});
            goto rcvSyncRespLoop;
          };
        };
      } else {
        goto rcvMsg;
      };
    rcvMsg:
      if ((Cardinality(primary)) > (0)) {
        with (yielded_primary3 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          if (((yielded_primary3) = (self)) /\ (shouldSync)) {
            goto syncPrimary;
          } else {
            assert ((network)[<<self, REQ_INDEX>>]).enabled;
            await (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0);
            with (readMsg10 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network10 = readMsg10) {
                req := yielded_network10;
                if (DEBUG) {
                  print <<"ServerRcvReq", self, req>>;
                  assert ((req).to) = (self);
                  if ((Cardinality(primary)) > (0)) {
                    with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                      if (((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  } else {
                    with (yielded_primary2 = NULL) {
                      if (((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  };
                } else {
                  assert ((req).to) = (self);
                  if ((Cardinality(primary)) > (0)) {
                    with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                      if (((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  } else {
                    with (yielded_primary2 = NULL) {
                      if (((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  };
                };
              };
            };
          };
        };
      } else {
        with (yielded_primary4 = NULL) {
          if (((yielded_primary4) = (self)) /\ (shouldSync)) {
            goto syncPrimary;
          } else {
            assert ((network)[<<self, REQ_INDEX>>]).enabled;
            await (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0);
            with (readMsg11 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network11 = readMsg11) {
                req := yielded_network11;
                if (DEBUG) {
                  print <<"ServerRcvReq", self, req>>;
                  assert ((req).to) = (self);
                  if ((Cardinality(primary)) > (0)) {
                    with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                      if (((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  } else {
                    with (yielded_primary2 = NULL) {
                      if (((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  };
                } else {
                  assert ((req).to) = (self);
                  if ((Cardinality(primary)) > (0)) {
                    with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                      if (((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  } else {
                    with (yielded_primary2 = NULL) {
                      if (((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                        goto handlePrimary;
                      } else {
                        goto handleBackup;
                      };
                    };
                  };
                };
              };
            };
          };
        };
      };
    handleBackup:
      if (DEBUG) {
        print <<"ServerHandleBackup", self>>;
        assert ((req).srcTyp) = (PRIMARY_SRC);
        if (((req).typ) = (GET_REQ)) {
          with (yielded_fs1 = ((fs)[self])[((req).body).key]) {
            respBody := [content |-> yielded_fs1];
            respTyp := GET_RESP;
            resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
            either {
              with (value80 = resp) {
                await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value80), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                goto replicaLoop;
              };
            } or {
              with (yielded_fd20 = (fd)[(resp).to]) {
                await yielded_fd20;
                goto replicaLoop;
              };
            };
          };
        } else {
          if (((req).typ) = (PUT_REQ)) {
            with (value60 = ((req).body).value) {
              fs := [fs EXCEPT ![self][((req).body).key] = value60];
              assert (((req).body).versionNumber) >= ((lastPutBody).versionNumber);
              lastPutBody := (req).body;
              respBody := ACK_MSG_BODY;
              respTyp := PUT_RESP;
              shouldSync := TRUE;
              resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
              either {
                with (value81 = resp) {
                  await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value81), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                  goto replicaLoop;
                };
              } or {
                with (yielded_fd21 = (fd)[(resp).to]) {
                  await yielded_fd21;
                  goto replicaLoop;
                };
              };
            };
          } else {
            if (((req).typ) = (SYNC_REQ)) {
              if ((((req).body).versionNumber) > ((lastPutBody).versionNumber)) {
                with (value70 = ((req).body).value) {
                  fs := [fs EXCEPT ![self][((req).body).key] = value70];
                  lastPutBody := (req).body;
                  respBody := lastPutBody;
                  respTyp := SYNC_RESP;
                  shouldSync := TRUE;
                  resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
                  either {
                    with (value82 = resp) {
                      await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                      network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value82), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                      goto replicaLoop;
                    };
                  } or {
                    with (yielded_fd22 = (fd)[(resp).to]) {
                      await yielded_fd22;
                      goto replicaLoop;
                    };
                  };
                };
              } else {
                respBody := lastPutBody;
                respTyp := SYNC_RESP;
                shouldSync := TRUE;
                resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
                either {
                  with (value83 = resp) {
                    await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                    network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value83), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                    goto replicaLoop;
                  };
                } or {
                  with (yielded_fd23 = (fd)[(resp).to]) {
                    await yielded_fd23;
                    goto replicaLoop;
                  };
                };
              };
            } else {
              resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
              either {
                with (value84 = resp) {
                  await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value84), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                  goto replicaLoop;
                };
              } or {
                with (yielded_fd24 = (fd)[(resp).to]) {
                  await yielded_fd24;
                  goto replicaLoop;
                };
              };
            };
          };
        };
      } else {
        assert ((req).srcTyp) = (PRIMARY_SRC);
        if (((req).typ) = (GET_REQ)) {
          with (yielded_fs2 = ((fs)[self])[((req).body).key]) {
            respBody := [content |-> yielded_fs2];
            respTyp := GET_RESP;
            resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
            either {
              with (value85 = resp) {
                await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value85), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                goto replicaLoop;
              };
            } or {
              with (yielded_fd25 = (fd)[(resp).to]) {
                await yielded_fd25;
                goto replicaLoop;
              };
            };
          };
        } else {
          if (((req).typ) = (PUT_REQ)) {
            with (value61 = ((req).body).value) {
              fs := [fs EXCEPT ![self][((req).body).key] = value61];
              assert (((req).body).versionNumber) >= ((lastPutBody).versionNumber);
              lastPutBody := (req).body;
              respBody := ACK_MSG_BODY;
              respTyp := PUT_RESP;
              shouldSync := TRUE;
              resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
              either {
                with (value86 = resp) {
                  await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value86), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                  goto replicaLoop;
                };
              } or {
                with (yielded_fd26 = (fd)[(resp).to]) {
                  await yielded_fd26;
                  goto replicaLoop;
                };
              };
            };
          } else {
            if (((req).typ) = (SYNC_REQ)) {
              if ((((req).body).versionNumber) > ((lastPutBody).versionNumber)) {
                with (value71 = ((req).body).value) {
                  fs := [fs EXCEPT ![self][((req).body).key] = value71];
                  lastPutBody := (req).body;
                  respBody := lastPutBody;
                  respTyp := SYNC_RESP;
                  shouldSync := TRUE;
                  resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
                  either {
                    with (value87 = resp) {
                      await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                      network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value87), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                      goto replicaLoop;
                    };
                  } or {
                    with (yielded_fd27 = (fd)[(resp).to]) {
                      await yielded_fd27;
                      goto replicaLoop;
                    };
                  };
                };
              } else {
                respBody := lastPutBody;
                respTyp := SYNC_RESP;
                shouldSync := TRUE;
                resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
                either {
                  with (value88 = resp) {
                    await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                    network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value88), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                    goto replicaLoop;
                  };
                } or {
                  with (yielded_fd28 = (fd)[(resp).to]) {
                    await yielded_fd28;
                    goto replicaLoop;
                  };
                };
              };
            } else {
              resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
              either {
                with (value89 = resp) {
                  await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value89), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                  goto replicaLoop;
                };
              } or {
                with (yielded_fd29 = (fd)[(resp).to]) {
                  await yielded_fd29;
                  goto replicaLoop;
                };
              };
            };
          };
        };
      };
    handlePrimary:
      if (DEBUG) {
        print <<"ServerHandlePrimary", self>>;
        assert ((req).srcTyp) = (CLIENT_SRC);
        if (((req).typ) = (GET_REQ)) {
          with (yielded_fs00 = ((fs)[self])[((req).body).key]) {
            respBody := [content |-> yielded_fs00];
            respTyp := GET_RESP;
            goto sndResp;
          };
        } else {
          if (((req).typ) = (PUT_REQ)) {
            with (value90 = ((req).body).value) {
              fs := [fs EXCEPT ![self][((req).body).key] = value90];
              lastPutBody := [versionNumber |-> ((lastPutBody).versionNumber) + (1), key |-> ((req).body).key, value |-> ((req).body).value];
              respBody := ACK_MSG_BODY;
              respTyp := PUT_RESP;
              replicaSet := (REPLICA_SET) \ ({self});
              idx := 1;
              goto sndReplicaReqLoop;
            };
          } else {
            goto sndReplicaReqLoop;
          };
        };
      } else {
        assert ((req).srcTyp) = (CLIENT_SRC);
        if (((req).typ) = (GET_REQ)) {
          with (yielded_fs01 = ((fs)[self])[((req).body).key]) {
            respBody := [content |-> yielded_fs01];
            respTyp := GET_RESP;
            goto sndResp;
          };
        } else {
          if (((req).typ) = (PUT_REQ)) {
            with (value91 = ((req).body).value) {
              fs := [fs EXCEPT ![self][((req).body).key] = value91];
              lastPutBody := [versionNumber |-> ((lastPutBody).versionNumber) + (1), key |-> ((req).body).key, value |-> ((req).body).value];
              respBody := ACK_MSG_BODY;
              respTyp := PUT_RESP;
              replicaSet := (REPLICA_SET) \ ({self});
              idx := 1;
              goto sndReplicaReqLoop;
            };
          } else {
            goto sndReplicaReqLoop;
          };
        };
      };
    sndReplicaReqLoop:
      if ((idx) <= (NUM_REPLICAS)) {
        if ((idx) # (self)) {
          either {
            repReq := [from |-> self, to |-> idx, body |-> lastPutBody, srcTyp |-> PRIMARY_SRC, typ |-> PUT_REQ, id |-> (req).id];
            with (value100 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network5 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value100), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if (EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network5;
                    goto sndReplicaReqLoop;
                  } or {
                    with (
                      value110 = FALSE, 
                      network6 = [network5 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network5)[<<self, REQ_INDEX>>]).queue, enabled |-> value110]], 
                      value120 = FALSE
                    ) {
                      network := [network6 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network6)[<<self, RESP_INDEX>>]).queue, enabled |-> value120]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network5;
                  goto sndReplicaReqLoop;
                };
              };
            };
          } or {
            with (yielded_fd30 = (fd)[idx]) {
              await yielded_fd30;
              idx := (idx) + (1);
              if (EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndReplicaReqLoop;
                } or {
                  with (
                    value111 = FALSE, 
                    network7 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value111]], 
                    value121 = FALSE
                  ) {
                    network := [network7 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network7)[<<self, RESP_INDEX>>]).queue, enabled |-> value121]];
                    goto failLabel;
                  };
                };
              } else {
                goto sndReplicaReqLoop;
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if (EXPLORE_FAIL) {
            either {
              skip;
              goto sndReplicaReqLoop;
            } or {
              with (
                value112 = FALSE, 
                network8 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value112]], 
                value122 = FALSE
              ) {
                network := [network8 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network8)[<<self, RESP_INDEX>>]).queue, enabled |-> value122]];
                goto failLabel;
              };
            };
          } else {
            goto sndReplicaReqLoop;
          };
        };
      } else {
        goto rcvReplicaRespLoop;
      };
    rcvReplicaRespLoop:
      if ((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (
            readMsg20 = Head(((network)[<<self, RESP_INDEX>>]).queue), 
            network9 = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]], 
            yielded_network20 = readMsg20
          ) {
            repResp := yielded_network20;
            with (yielded_fd40 = (fd)[(repResp).from]) {
              assert ((((((((repResp).from) \in (replicaSet)) \/ (yielded_fd40)) /\ (((repResp).to) = (self))) /\ (((repResp).body) = (ACK_MSG_BODY))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (PUT_RESP))) /\ (((repResp).id) = ((req).id));
              replicaSet := (replicaSet) \ ({(repResp).from});
              if (EXPLORE_FAIL) {
                either {
                  skip;
                  network := network9;
                  goto rcvReplicaRespLoop;
                } or {
                  with (
                    value130 = FALSE, 
                    network10 = [network9 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network9)[<<self, REQ_INDEX>>]).queue, enabled |-> value130]], 
                    value140 = FALSE
                  ) {
                    network := [network10 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network10)[<<self, RESP_INDEX>>]).queue, enabled |-> value140]];
                    goto failLabel;
                  };
                };
              } else {
                network := network9;
                goto rcvReplicaRespLoop;
              };
            };
          };
        } or {
          replica := CHOOSE r \in replicaSet : TRUE;
          with (
            yielded_fd50 = (fd)[replica], 
            yielded_network30 = Len(((network)[<<self, RESP_INDEX>>]).queue)
          ) {
            await (yielded_fd50) /\ ((yielded_network30) = (0));
            replicaSet := (replicaSet) \ ({replica});
            if (EXPLORE_FAIL) {
              either {
                skip;
                goto rcvReplicaRespLoop;
              } or {
                with (
                  value131 = FALSE, 
                  network11 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value131]], 
                  value141 = FALSE
                ) {
                  network := [network11 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network11)[<<self, RESP_INDEX>>]).queue, enabled |-> value141]];
                  goto failLabel;
                };
              };
            } else {
              goto rcvReplicaRespLoop;
            };
          };
        };
      } else {
        goto sndResp;
      };
    sndResp:
      resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> PRIMARY_SRC, typ |-> respTyp, id |-> (req).id];
      with (value150 = resp) {
        await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
        network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value150), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
        if (DEBUG) {
          print <<"ServerSendResp", self, (req).from>>;
          goto replicaLoop;
        } else {
          goto replicaLoop;
        };
      };
    failLabel:
      with (value160 = TRUE) {
        fd := [fd EXCEPT ![self] = value160];
        with (value170 = self) {
          primary := (primary) \ ({value170});
          goto Done;
        };
      };
  }
  
  fair process (Client \in CLIENT_SET)
    variables req0; resp0; msg; replica0; idx0 = 0;
  {
    clientLoop:
      if (TRUE) {
        if (DEBUG) {
          print <<"ClientLoop", self>>;
          await (Len(clientInput)) > (0);
          with (res00 = Head(clientInput)) {
            clientInput := Tail(clientInput);
            with (yielded_clientInput0 = res00) {
              msg := yielded_clientInput0;
              idx0 := (idx0) + (1);
              goto sndReq;
            };
          };
        } else {
          await (Len(clientInput)) > (0);
          with (res01 = Head(clientInput)) {
            clientInput := Tail(clientInput);
            with (yielded_clientInput1 = res01) {
              msg := yielded_clientInput1;
              idx0 := (idx0) + (1);
              goto sndReq;
            };
          };
        };
      } else {
        goto Done;
      };
    sndReq:
      if ((Cardinality(primary)) > (0)) {
        with (yielded_primary50 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          replica0 := yielded_primary50;
          if ((replica0) # (NULL)) {
            either {
              req0 := [from |-> self, to |-> replica0, body |-> (msg).body, srcTyp |-> CLIENT_SRC, typ |-> (msg).typ, id |-> idx0];
              with (value180 = req0) {
                await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value180), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                if (DEBUG) {
                  print <<"ClientSendReq", self, replica0>>;
                  goto rcvResp;
                } else {
                  goto rcvResp;
                };
              };
            } or {
              with (yielded_fd60 = (fd)[replica0]) {
                await yielded_fd60;
                goto sndReq;
              };
            };
          } else {
            goto Done;
          };
        };
      } else {
        with (yielded_primary60 = NULL) {
          replica0 := yielded_primary60;
          if ((replica0) # (NULL)) {
            either {
              req0 := [from |-> self, to |-> replica0, body |-> (msg).body, srcTyp |-> CLIENT_SRC, typ |-> (msg).typ, id |-> idx0];
              with (value181 = req0) {
                await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value181), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                if (DEBUG) {
                  print <<"ClientSendReq", self, replica0>>;
                  goto rcvResp;
                } else {
                  goto rcvResp;
                };
              };
            } or {
              with (yielded_fd61 = (fd)[replica0]) {
                await yielded_fd61;
                goto sndReq;
              };
            };
          } else {
            goto Done;
          };
        };
      };
    rcvResp:
      if (DEBUG) {
        print <<"ClientRcvRespEither", self>>;
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg30 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
            with (yielded_network40 = readMsg30) {
              resp0 := yielded_network40;
              if (DEBUG) {
                print <<"ClientRcvResp", self, replica0>>;
                if (((resp0).id) # (idx0)) {
                  goto rcvResp;
                } else {
                  if (((msg).typ) = (PUT_REQ)) {
                    assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (idx0));
                    clientOutput := ((resp0).body).content;
                    goto clientLoop;
                  } else {
                    if (((msg).typ) = (GET_REQ)) {
                      assert ((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (GET_RESP))) /\ (((resp0).id) = (idx0));
                      clientOutput := ((resp0).body).content;
                      goto clientLoop;
                    } else {
                      assert FALSE;
                      goto clientLoop;
                    };
                  };
                };
              } else {
                if (((resp0).id) # (idx0)) {
                  goto rcvResp;
                } else {
                  if (((msg).typ) = (PUT_REQ)) {
                    assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (idx0));
                    clientOutput := ((resp0).body).content;
                    goto clientLoop;
                  } else {
                    if (((msg).typ) = (GET_REQ)) {
                      assert ((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (GET_RESP))) /\ (((resp0).id) = (idx0));
                      clientOutput := ((resp0).body).content;
                      goto clientLoop;
                    } else {
                      assert FALSE;
                      goto clientLoop;
                    };
                  };
                };
              };
            };
          };
        } or {
          with (
            yielded_fd70 = (fd)[replica0], 
            yielded_network50 = Len(((network)[<<self, RESP_INDEX>>]).queue)
          ) {
            await (yielded_fd70) /\ ((yielded_network50) = (0));
            if (DEBUG) {
              print <<"ClientDetectedFail", self, replica0>>;
              goto sndReq;
            } else {
              goto sndReq;
            };
          };
        };
      } else {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg31 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
            with (yielded_network41 = readMsg31) {
              resp0 := yielded_network41;
              if (DEBUG) {
                print <<"ClientRcvResp", self, replica0>>;
                if (((resp0).id) # (idx0)) {
                  goto rcvResp;
                } else {
                  if (((msg).typ) = (PUT_REQ)) {
                    assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (idx0));
                    clientOutput := ((resp0).body).content;
                    goto clientLoop;
                  } else {
                    if (((msg).typ) = (GET_REQ)) {
                      assert ((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (GET_RESP))) /\ (((resp0).id) = (idx0));
                      clientOutput := ((resp0).body).content;
                      goto clientLoop;
                    } else {
                      assert FALSE;
                      goto clientLoop;
                    };
                  };
                };
              } else {
                if (((resp0).id) # (idx0)) {
                  goto rcvResp;
                } else {
                  if (((msg).typ) = (PUT_REQ)) {
                    assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (idx0));
                    clientOutput := ((resp0).body).content;
                    goto clientLoop;
                  } else {
                    if (((msg).typ) = (GET_REQ)) {
                      assert ((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (GET_RESP))) /\ (((resp0).id) = (idx0));
                      clientOutput := ((resp0).body).content;
                      goto clientLoop;
                    } else {
                      assert FALSE;
                      goto clientLoop;
                    };
                  };
                };
              };
            };
          };
        } or {
          with (
            yielded_fd71 = (fd)[replica0], 
            yielded_network51 = Len(((network)[<<self, RESP_INDEX>>]).queue)
          ) {
            await (yielded_fd71) /\ ((yielded_network51) = (0));
            if (DEBUG) {
              print <<"ClientDetectedFail", self, replica0>>;
              goto sndReq;
            } else {
              goto sndReq;
            };
          };
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "1e1a110f" /\ chksum(tla) = "79f1fe77")
CONSTANT defaultInitValue
VARIABLES network, fd, fs, primary, clientInput, clientOutput, pc

(* define statement *)
NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
CLIENT_SRC == 1
PRIMARY_SRC == 2
BACKUP_SRC == 3
GET_REQ == 1
GET_RESP == 2
PUT_REQ == 3
PUT_RESP == 4
SYNC_REQ == 5
SYNC_RESP == 6
REQ_INDEX == 1
RESP_INDEX == 2
ACK_MSG_BODY == [content |-> "ack-body"]
KEY1 == "KEY1"
VALUE1 == "VALUE1"
VALUE2 == "VALUE2"
KEY_SET == {KEY1}
NODE_SET == (1) .. (NUM_NODES)
REPLICA_SET == (1) .. (NUM_REPLICAS)
CLIENT_SET == ((NUM_REPLICAS) + (1)) .. ((NUM_REPLICAS) + (NUM_CLIENTS))
MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}
NULL == 0

VARIABLES req, respBody, respTyp, idx, repReq, repResp, resp, replicaSet, 
          shouldSync, lastPutBody, replica, req0, resp0, msg, replica0, idx0

vars == << network, fd, fs, primary, clientInput, clientOutput, pc, req, 
           respBody, respTyp, idx, repReq, repResp, resp, replicaSet, 
           shouldSync, lastPutBody, replica, req0, resp0, msg, replica0, idx0
        >>

ProcSet == (REPLICA_SET) \cup (CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [id \in REPLICA_SET |-> FALSE]
        /\ fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]]
        /\ primary = REPLICA_SET
        /\ clientInput = <<[typ |-> PUT_REQ, body |-> [key |-> KEY1, value |-> VALUE1]], [typ |-> PUT_REQ, body |-> [key |-> KEY1, value |-> VALUE2]], [typ |-> GET_REQ, body |-> [key |-> KEY1]]>>
        /\ clientOutput = defaultInitValue
        (* Process Replica *)
        /\ req = [self \in REPLICA_SET |-> defaultInitValue]
        /\ respBody = [self \in REPLICA_SET |-> defaultInitValue]
        /\ respTyp = [self \in REPLICA_SET |-> defaultInitValue]
        /\ idx = [self \in REPLICA_SET |-> defaultInitValue]
        /\ repReq = [self \in REPLICA_SET |-> defaultInitValue]
        /\ repResp = [self \in REPLICA_SET |-> defaultInitValue]
        /\ resp = [self \in REPLICA_SET |-> defaultInitValue]
        /\ replicaSet = [self \in REPLICA_SET |-> defaultInitValue]
        /\ shouldSync = [self \in REPLICA_SET |-> FALSE]
        /\ lastPutBody = [self \in REPLICA_SET |-> [versionNumber |-> 0]]
        /\ replica = [self \in REPLICA_SET |-> defaultInitValue]
        (* Process Client *)
        /\ req0 = [self \in CLIENT_SET |-> defaultInitValue]
        /\ resp0 = [self \in CLIENT_SET |-> defaultInitValue]
        /\ msg = [self \in CLIENT_SET |-> defaultInitValue]
        /\ replica0 = [self \in CLIENT_SET |-> defaultInitValue]
        /\ idx0 = [self \in CLIENT_SET |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in REPLICA_SET -> "replicaLoop"
                                        [] self \in CLIENT_SET -> "clientLoop"]

replicaLoop(self) == /\ pc[self] = "replicaLoop"
                     /\ IF TRUE
                           THEN /\ replicaSet' = [replicaSet EXCEPT ![self] = (REPLICA_SET) \ ({self})]
                                /\ idx' = [idx EXCEPT ![self] = 1]
                                /\ IF EXPLORE_FAIL
                                      THEN /\ \/ /\ TRUE
                                                 /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                                 /\ UNCHANGED network
                                              \/ /\ LET value00 == FALSE IN
                                                      LET network0 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value00]] IN
                                                        LET value19 == FALSE IN
                                                          /\ network' = [network0 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network0)[<<self, RESP_INDEX>>]).queue, enabled |-> value19]]
                                                          /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                           /\ UNCHANGED network
                           ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                /\ UNCHANGED << network, idx, replicaSet >>
                     /\ UNCHANGED << fd, fs, primary, clientInput, 
                                     clientOutput, req, respBody, respTyp, 
                                     repReq, repResp, resp, shouldSync, 
                                     lastPutBody, replica, req0, resp0, msg, 
                                     replica0, idx0 >>

syncPrimary(self) == /\ pc[self] = "syncPrimary"
                     /\ IF (Cardinality(primary)) > (0)
                           THEN /\ LET yielded_primary == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                     IF ((yielded_primary) = (self)) /\ (shouldSync[self])
                                        THEN /\ shouldSync' = [shouldSync EXCEPT ![self] = FALSE]
                                             /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                             /\ UNCHANGED shouldSync
                           ELSE /\ LET yielded_primary0 == NULL IN
                                     IF ((yielded_primary0) = (self)) /\ (shouldSync[self])
                                        THEN /\ shouldSync' = [shouldSync EXCEPT ![self] = FALSE]
                                             /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                             /\ UNCHANGED shouldSync
                     /\ UNCHANGED << network, fd, fs, primary, clientInput, 
                                     clientOutput, req, respBody, respTyp, idx, 
                                     repReq, repResp, resp, replicaSet, 
                                     lastPutBody, replica, req0, resp0, msg, 
                                     replica0, idx0 >>

sndSyncReqLoop(self) == /\ pc[self] = "sndSyncReqLoop"
                        /\ IF (idx[self]) <= (NUM_REPLICAS)
                              THEN /\ IF (idx[self]) # (self)
                                         THEN /\ \/ /\ repReq' = [repReq EXCEPT ![self] = [from |-> self, to |-> idx[self], body |-> lastPutBody[self], srcTyp |-> PRIMARY_SRC, typ |-> SYNC_REQ, id |-> 3]]
                                                    /\ LET value20 == repReq'[self] IN
                                                         /\ ((network)[<<idx[self], REQ_INDEX>>]).enabled
                                                         /\ LET network1 == [network EXCEPT ![<<idx[self], REQ_INDEX>>] = [queue |-> Append(((network)[<<idx[self], REQ_INDEX>>]).queue, value20), enabled |-> ((network)[<<idx[self], REQ_INDEX>>]).enabled]] IN
                                                              /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                              /\ IF EXPLORE_FAIL
                                                                    THEN /\ \/ /\ TRUE
                                                                               /\ network' = network1
                                                                               /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                            \/ /\ LET value30 == FALSE IN
                                                                                    LET network2 == [network1 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network1)[<<self, REQ_INDEX>>]).queue, enabled |-> value30]] IN
                                                                                      LET value40 == FALSE IN
                                                                                        /\ network' = [network2 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network2)[<<self, RESP_INDEX>>]).queue, enabled |-> value40]]
                                                                                        /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                    ELSE /\ network' = network1
                                                                         /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                 \/ /\ LET yielded_fd8 == (fd)[idx[self]] IN
                                                         /\ yielded_fd8
                                                         /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                         /\ IF EXPLORE_FAIL
                                                               THEN /\ \/ /\ TRUE
                                                                          /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                          /\ UNCHANGED network
                                                                       \/ /\ LET value31 == FALSE IN
                                                                               LET network3 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value31]] IN
                                                                                 LET value41 == FALSE IN
                                                                                   /\ network' = [network3 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network3)[<<self, RESP_INDEX>>]).queue, enabled |-> value41]]
                                                                                   /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                    /\ UNCHANGED network
                                                    /\ UNCHANGED repReq
                                         ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                              /\ IF EXPLORE_FAIL
                                                    THEN /\ \/ /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                               /\ UNCHANGED network
                                                            \/ /\ LET value32 == FALSE IN
                                                                    LET network4 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value32]] IN
                                                                      LET value42 == FALSE IN
                                                                        /\ network' = [network4 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network4)[<<self, RESP_INDEX>>]).queue, enabled |-> value42]]
                                                                        /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                         /\ UNCHANGED network
                                              /\ UNCHANGED repReq
                              ELSE /\ pc' = [pc EXCEPT ![self] = "rcvSyncRespLoop"]
                                   /\ UNCHANGED << network, idx, repReq >>
                        /\ UNCHANGED << fd, fs, primary, clientInput, 
                                        clientOutput, req, respBody, respTyp, 
                                        repResp, resp, replicaSet, shouldSync, 
                                        lastPutBody, replica, req0, resp0, msg, 
                                        replica0, idx0 >>

rcvSyncRespLoop(self) == /\ pc[self] = "rcvSyncRespLoop"
                         /\ IF (Cardinality(replicaSet[self])) > (0)
                               THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                    "Failure of assertion at line 620, column 11.")
                                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                          /\ LET readMsg00 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                                               /\ LET yielded_network6 == readMsg00 IN
                                                    /\ repResp' = [repResp EXCEPT ![self] = yielded_network6]
                                                    /\ LET yielded_fd00 == (fd)[(repResp'[self]).from] IN
                                                         /\ Assert(((((((repResp'[self]).id) = (3)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (SYNC_RESP))) /\ ((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd00)), 
                                                                   "Failure of assertion at line 627, column 17.")
                                                         /\ IF (((repResp'[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber)
                                                               THEN /\ LET value50 == ((repResp'[self]).body).value IN
                                                                         /\ fs' = [fs EXCEPT ![self][((repResp'[self]).body).key] = value50]
                                                                         /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (repResp'[self]).body]
                                                                         /\ replicaSet' = [replicaSet EXCEPT ![self] = (REPLICA_SET) \ ({self})]
                                                                         /\ idx' = [idx EXCEPT ![self] = 1]
                                                                         /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                               ELSE /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({(repResp'[self]).from})]
                                                                    /\ pc' = [pc EXCEPT ![self] = "rcvSyncRespLoop"]
                                                                    /\ UNCHANGED << fs, 
                                                                                    idx, 
                                                                                    lastPutBody >>
                                          /\ UNCHANGED replica
                                       \/ /\ replica' = [replica EXCEPT ![self] = CHOOSE r \in replicaSet[self] : TRUE]
                                          /\ LET yielded_fd10 == (fd)[replica'[self]] IN
                                               LET yielded_network00 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                 /\ (yielded_fd10) /\ ((yielded_network00) = (0))
                                                 /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({replica'[self]})]
                                                 /\ pc' = [pc EXCEPT ![self] = "rcvSyncRespLoop"]
                                          /\ UNCHANGED <<network, fs, idx, repResp, lastPutBody>>
                               ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                    /\ UNCHANGED << network, fs, idx, repResp, 
                                                    replicaSet, lastPutBody, 
                                                    replica >>
                         /\ UNCHANGED << fd, primary, clientInput, 
                                         clientOutput, req, respBody, respTyp, 
                                         repReq, resp, shouldSync, req0, resp0, 
                                         msg, replica0, idx0 >>

rcvMsg(self) == /\ pc[self] = "rcvMsg"
                /\ IF (Cardinality(primary)) > (0)
                      THEN /\ LET yielded_primary3 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                IF ((yielded_primary3) = (self)) /\ (shouldSync[self])
                                   THEN /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                        /\ UNCHANGED << network, req >>
                                   ELSE /\ Assert(((network)[<<self, REQ_INDEX>>]).enabled, 
                                                  "Failure of assertion at line 663, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg10 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network10 == readMsg10 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network10]
                                                  /\ IF DEBUG
                                                        THEN /\ PrintT(<<"ServerRcvReq", self, req'[self]>>)
                                                             /\ Assert(((req'[self]).to) = (self), 
                                                                       "Failure of assertion at line 671, column 19.")
                                                             /\ IF (Cardinality(primary)) > (0)
                                                                   THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                             IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                                   ELSE /\ LET yielded_primary2 == NULL IN
                                                                             IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                        ELSE /\ Assert(((req'[self]).to) = (self), 
                                                                       "Failure of assertion at line 690, column 19.")
                                                             /\ IF (Cardinality(primary)) > (0)
                                                                   THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                             IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                                   ELSE /\ LET yielded_primary2 == NULL IN
                                                                             IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                      ELSE /\ LET yielded_primary4 == NULL IN
                                IF ((yielded_primary4) = (self)) /\ (shouldSync[self])
                                   THEN /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                        /\ UNCHANGED << network, req >>
                                   ELSE /\ Assert(((network)[<<self, REQ_INDEX>>]).enabled, 
                                                  "Failure of assertion at line 718, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg11 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network11 == readMsg11 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network11]
                                                  /\ IF DEBUG
                                                        THEN /\ PrintT(<<"ServerRcvReq", self, req'[self]>>)
                                                             /\ Assert(((req'[self]).to) = (self), 
                                                                       "Failure of assertion at line 726, column 19.")
                                                             /\ IF (Cardinality(primary)) > (0)
                                                                   THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                             IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                                   ELSE /\ LET yielded_primary2 == NULL IN
                                                                             IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                        ELSE /\ Assert(((req'[self]).to) = (self), 
                                                                       "Failure of assertion at line 745, column 19.")
                                                             /\ IF (Cardinality(primary)) > (0)
                                                                   THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                             IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                                   ELSE /\ LET yielded_primary2 == NULL IN
                                                                             IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                /\ UNCHANGED << fd, fs, primary, clientInput, clientOutput, 
                                respBody, respTyp, idx, repReq, repResp, resp, 
                                replicaSet, shouldSync, lastPutBody, replica, 
                                req0, resp0, msg, replica0, idx0 >>

handleBackup(self) == /\ pc[self] = "handleBackup"
                      /\ IF DEBUG
                            THEN /\ PrintT(<<"ServerHandleBackup", self>>)
                                 /\ Assert(((req[self]).srcTyp) = (PRIMARY_SRC), 
                                           "Failure of assertion at line 772, column 9.")
                                 /\ IF ((req[self]).typ) = (GET_REQ)
                                       THEN /\ LET yielded_fs1 == ((fs)[self])[((req[self]).body).key] IN
                                                 /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs1]]
                                                 /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                 /\ \/ /\ LET value80 == resp'[self] IN
                                                            /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                            /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value80), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                    \/ /\ LET yielded_fd20 == (fd)[(resp'[self]).to] IN
                                                            /\ yielded_fd20
                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                       /\ UNCHANGED network
                                            /\ UNCHANGED << fs, shouldSync, 
                                                            lastPutBody >>
                                       ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                                  THEN /\ LET value60 == ((req[self]).body).value IN
                                                            /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value60]
                                                            /\ Assert((((req[self]).body).versionNumber) >= ((lastPutBody[self]).versionNumber), 
                                                                      "Failure of assertion at line 795, column 15.")
                                                            /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                            /\ respBody' = [respBody EXCEPT ![self] = ACK_MSG_BODY]
                                                            /\ respTyp' = [respTyp EXCEPT ![self] = PUT_RESP]
                                                            /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                            /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                            /\ \/ /\ LET value81 == resp'[self] IN
                                                                       /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                       /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value81), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                               \/ /\ LET yielded_fd21 == (fd)[(resp'[self]).to] IN
                                                                       /\ yielded_fd21
                                                                       /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                  /\ UNCHANGED network
                                                  ELSE /\ IF ((req[self]).typ) = (SYNC_REQ)
                                                             THEN /\ IF (((req[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber)
                                                                        THEN /\ LET value70 == ((req[self]).body).value IN
                                                                                  /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value70]
                                                                                  /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                                                  /\ respBody' = [respBody EXCEPT ![self] = lastPutBody'[self]]
                                                                                  /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                                  /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                                  /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                                  /\ \/ /\ LET value82 == resp'[self] IN
                                                                                             /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                                             /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value82), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                     \/ /\ LET yielded_fd22 == (fd)[(resp'[self]).to] IN
                                                                                             /\ yielded_fd22
                                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                        /\ UNCHANGED network
                                                                        ELSE /\ respBody' = [respBody EXCEPT ![self] = lastPutBody[self]]
                                                                             /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                             /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                             /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                             /\ \/ /\ LET value83 == resp'[self] IN
                                                                                        /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                                        /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value83), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                                        /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                \/ /\ LET yielded_fd23 == (fd)[(resp'[self]).to] IN
                                                                                        /\ yielded_fd23
                                                                                        /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                   /\ UNCHANGED network
                                                                             /\ UNCHANGED << fs, 
                                                                                             lastPutBody >>
                                                             ELSE /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                                                                  /\ \/ /\ LET value84 == resp'[self] IN
                                                                             /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                             /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value84), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                     \/ /\ LET yielded_fd24 == (fd)[(resp'[self]).to] IN
                                                                             /\ yielded_fd24
                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                        /\ UNCHANGED network
                                                                  /\ UNCHANGED << fs, 
                                                                                  respBody, 
                                                                                  respTyp, 
                                                                                  shouldSync, 
                                                                                  lastPutBody >>
                            ELSE /\ Assert(((req[self]).srcTyp) = (PRIMARY_SRC), 
                                           "Failure of assertion at line 873, column 9.")
                                 /\ IF ((req[self]).typ) = (GET_REQ)
                                       THEN /\ LET yielded_fs2 == ((fs)[self])[((req[self]).body).key] IN
                                                 /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs2]]
                                                 /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                 /\ \/ /\ LET value85 == resp'[self] IN
                                                            /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                            /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value85), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                    \/ /\ LET yielded_fd25 == (fd)[(resp'[self]).to] IN
                                                            /\ yielded_fd25
                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                       /\ UNCHANGED network
                                            /\ UNCHANGED << fs, shouldSync, 
                                                            lastPutBody >>
                                       ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                                  THEN /\ LET value61 == ((req[self]).body).value IN
                                                            /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value61]
                                                            /\ Assert((((req[self]).body).versionNumber) >= ((lastPutBody[self]).versionNumber), 
                                                                      "Failure of assertion at line 896, column 15.")
                                                            /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                            /\ respBody' = [respBody EXCEPT ![self] = ACK_MSG_BODY]
                                                            /\ respTyp' = [respTyp EXCEPT ![self] = PUT_RESP]
                                                            /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                            /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                            /\ \/ /\ LET value86 == resp'[self] IN
                                                                       /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                       /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value86), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                               \/ /\ LET yielded_fd26 == (fd)[(resp'[self]).to] IN
                                                                       /\ yielded_fd26
                                                                       /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                  /\ UNCHANGED network
                                                  ELSE /\ IF ((req[self]).typ) = (SYNC_REQ)
                                                             THEN /\ IF (((req[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber)
                                                                        THEN /\ LET value71 == ((req[self]).body).value IN
                                                                                  /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value71]
                                                                                  /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                                                  /\ respBody' = [respBody EXCEPT ![self] = lastPutBody'[self]]
                                                                                  /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                                  /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                                  /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                                  /\ \/ /\ LET value87 == resp'[self] IN
                                                                                             /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                                             /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value87), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                     \/ /\ LET yielded_fd27 == (fd)[(resp'[self]).to] IN
                                                                                             /\ yielded_fd27
                                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                        /\ UNCHANGED network
                                                                        ELSE /\ respBody' = [respBody EXCEPT ![self] = lastPutBody[self]]
                                                                             /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                             /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                             /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                             /\ \/ /\ LET value88 == resp'[self] IN
                                                                                        /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                                        /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value88), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                                        /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                \/ /\ LET yielded_fd28 == (fd)[(resp'[self]).to] IN
                                                                                        /\ yielded_fd28
                                                                                        /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                                   /\ UNCHANGED network
                                                                             /\ UNCHANGED << fs, 
                                                                                             lastPutBody >>
                                                             ELSE /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                                                                  /\ \/ /\ LET value89 == resp'[self] IN
                                                                             /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                             /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value89), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                     \/ /\ LET yielded_fd29 == (fd)[(resp'[self]).to] IN
                                                                             /\ yielded_fd29
                                                                             /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                        /\ UNCHANGED network
                                                                  /\ UNCHANGED << fs, 
                                                                                  respBody, 
                                                                                  respTyp, 
                                                                                  shouldSync, 
                                                                                  lastPutBody >>
                      /\ UNCHANGED << fd, primary, clientInput, clientOutput, 
                                      req, idx, repReq, repResp, replicaSet, 
                                      replica, req0, resp0, msg, replica0, 
                                      idx0 >>

handlePrimary(self) == /\ pc[self] = "handlePrimary"
                       /\ IF DEBUG
                             THEN /\ PrintT(<<"ServerHandlePrimary", self>>)
                                  /\ Assert(((req[self]).srcTyp) = (CLIENT_SRC), 
                                            "Failure of assertion at line 977, column 9.")
                                  /\ IF ((req[self]).typ) = (GET_REQ)
                                        THEN /\ LET yielded_fs00 == ((fs)[self])[((req[self]).body).key] IN
                                                  /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs00]]
                                                  /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                                  /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                             /\ UNCHANGED << fs, idx, 
                                                             replicaSet, 
                                                             lastPutBody >>
                                        ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                                   THEN /\ LET value90 == ((req[self]).body).value IN
                                                             /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value90]
                                                             /\ lastPutBody' = [lastPutBody EXCEPT ![self] = [versionNumber |-> ((lastPutBody[self]).versionNumber) + (1), key |-> ((req[self]).body).key, value |-> ((req[self]).body).value]]
                                                             /\ respBody' = [respBody EXCEPT ![self] = ACK_MSG_BODY]
                                                             /\ respTyp' = [respTyp EXCEPT ![self] = PUT_RESP]
                                                             /\ replicaSet' = [replicaSet EXCEPT ![self] = (REPLICA_SET) \ ({self})]
                                                             /\ idx' = [idx EXCEPT ![self] = 1]
                                                             /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                        /\ UNCHANGED << fs, 
                                                                        respBody, 
                                                                        respTyp, 
                                                                        idx, 
                                                                        replicaSet, 
                                                                        lastPutBody >>
                             ELSE /\ Assert(((req[self]).srcTyp) = (CLIENT_SRC), 
                                            "Failure of assertion at line 1000, column 9.")
                                  /\ IF ((req[self]).typ) = (GET_REQ)
                                        THEN /\ LET yielded_fs01 == ((fs)[self])[((req[self]).body).key] IN
                                                  /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs01]]
                                                  /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                                  /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                             /\ UNCHANGED << fs, idx, 
                                                             replicaSet, 
                                                             lastPutBody >>
                                        ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                                   THEN /\ LET value91 == ((req[self]).body).value IN
                                                             /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value91]
                                                             /\ lastPutBody' = [lastPutBody EXCEPT ![self] = [versionNumber |-> ((lastPutBody[self]).versionNumber) + (1), key |-> ((req[self]).body).key, value |-> ((req[self]).body).value]]
                                                             /\ respBody' = [respBody EXCEPT ![self] = ACK_MSG_BODY]
                                                             /\ respTyp' = [respTyp EXCEPT ![self] = PUT_RESP]
                                                             /\ replicaSet' = [replicaSet EXCEPT ![self] = (REPLICA_SET) \ ({self})]
                                                             /\ idx' = [idx EXCEPT ![self] = 1]
                                                             /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                        /\ UNCHANGED << fs, 
                                                                        respBody, 
                                                                        respTyp, 
                                                                        idx, 
                                                                        replicaSet, 
                                                                        lastPutBody >>
                       /\ UNCHANGED << network, fd, primary, clientInput, 
                                       clientOutput, req, repReq, repResp, 
                                       resp, shouldSync, replica, req0, resp0, 
                                       msg, replica0, idx0 >>

sndReplicaReqLoop(self) == /\ pc[self] = "sndReplicaReqLoop"
                           /\ IF (idx[self]) <= (NUM_REPLICAS)
                                 THEN /\ IF (idx[self]) # (self)
                                            THEN /\ \/ /\ repReq' = [repReq EXCEPT ![self] = [from |-> self, to |-> idx[self], body |-> lastPutBody[self], srcTyp |-> PRIMARY_SRC, typ |-> PUT_REQ, id |-> (req[self]).id]]
                                                       /\ LET value100 == repReq'[self] IN
                                                            /\ ((network)[<<idx[self], REQ_INDEX>>]).enabled
                                                            /\ LET network5 == [network EXCEPT ![<<idx[self], REQ_INDEX>>] = [queue |-> Append(((network)[<<idx[self], REQ_INDEX>>]).queue, value100), enabled |-> ((network)[<<idx[self], REQ_INDEX>>]).enabled]] IN
                                                                 /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                                 /\ IF EXPLORE_FAIL
                                                                       THEN /\ \/ /\ TRUE
                                                                                  /\ network' = network5
                                                                                  /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                               \/ /\ LET value110 == FALSE IN
                                                                                       LET network6 == [network5 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network5)[<<self, REQ_INDEX>>]).queue, enabled |-> value110]] IN
                                                                                         LET value120 == FALSE IN
                                                                                           /\ network' = [network6 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network6)[<<self, RESP_INDEX>>]).queue, enabled |-> value120]]
                                                                                           /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                       ELSE /\ network' = network5
                                                                            /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                    \/ /\ LET yielded_fd30 == (fd)[idx[self]] IN
                                                            /\ yielded_fd30
                                                            /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                            /\ IF EXPLORE_FAIL
                                                                  THEN /\ \/ /\ TRUE
                                                                             /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                             /\ UNCHANGED network
                                                                          \/ /\ LET value111 == FALSE IN
                                                                                  LET network7 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value111]] IN
                                                                                    LET value121 == FALSE IN
                                                                                      /\ network' = [network7 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network7)[<<self, RESP_INDEX>>]).queue, enabled |-> value121]]
                                                                                      /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                       /\ UNCHANGED network
                                                       /\ UNCHANGED repReq
                                            ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                 /\ IF EXPLORE_FAIL
                                                       THEN /\ \/ /\ TRUE
                                                                  /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                  /\ UNCHANGED network
                                                               \/ /\ LET value112 == FALSE IN
                                                                       LET network8 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value112]] IN
                                                                         LET value122 == FALSE IN
                                                                           /\ network' = [network8 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network8)[<<self, RESP_INDEX>>]).queue, enabled |-> value122]]
                                                                           /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                            /\ UNCHANGED network
                                                 /\ UNCHANGED repReq
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                      /\ UNCHANGED << network, idx, repReq >>
                           /\ UNCHANGED << fd, fs, primary, clientInput, 
                                           clientOutput, req, respBody, 
                                           respTyp, repResp, resp, replicaSet, 
                                           shouldSync, lastPutBody, replica, 
                                           req0, resp0, msg, replica0, idx0 >>

rcvReplicaRespLoop(self) == /\ pc[self] = "rcvReplicaRespLoop"
                            /\ IF (Cardinality(replicaSet[self])) > (0)
                                  THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                       "Failure of assertion at line 1102, column 11.")
                                             /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                             /\ LET readMsg20 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                  LET network9 == [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]] IN
                                                    LET yielded_network20 == readMsg20 IN
                                                      /\ repResp' = [repResp EXCEPT ![self] = yielded_network20]
                                                      /\ LET yielded_fd40 == (fd)[(repResp'[self]).from] IN
                                                           /\ Assert(((((((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd40)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).body) = (ACK_MSG_BODY))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (PUT_RESP))) /\ (((repResp'[self]).id) = ((req[self]).id)), 
                                                                     "Failure of assertion at line 1111, column 15.")
                                                           /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({(repResp'[self]).from})]
                                                           /\ IF EXPLORE_FAIL
                                                                 THEN /\ \/ /\ TRUE
                                                                            /\ network' = network9
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                                         \/ /\ LET value130 == FALSE IN
                                                                                 LET network10 == [network9 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network9)[<<self, REQ_INDEX>>]).queue, enabled |-> value130]] IN
                                                                                   LET value140 == FALSE IN
                                                                                     /\ network' = [network10 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network10)[<<self, RESP_INDEX>>]).queue, enabled |-> value140]]
                                                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                 ELSE /\ network' = network9
                                                                      /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                             /\ UNCHANGED replica
                                          \/ /\ replica' = [replica EXCEPT ![self] = CHOOSE r \in replicaSet[self] : TRUE]
                                             /\ LET yielded_fd50 == (fd)[replica'[self]] IN
                                                  LET yielded_network30 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                    /\ (yielded_fd50) /\ ((yielded_network30) = (0))
                                                    /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({replica'[self]})]
                                                    /\ IF EXPLORE_FAIL
                                                          THEN /\ \/ /\ TRUE
                                                                     /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                                     /\ UNCHANGED network
                                                                  \/ /\ LET value131 == FALSE IN
                                                                          LET network11 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value131]] IN
                                                                            LET value141 == FALSE IN
                                                                              /\ network' = [network11 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network11)[<<self, RESP_INDEX>>]).queue, enabled |-> value141]]
                                                                              /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                               /\ UNCHANGED network
                                             /\ UNCHANGED repResp
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                       /\ UNCHANGED << network, repResp, 
                                                       replicaSet, replica >>
                            /\ UNCHANGED << fd, fs, primary, clientInput, 
                                            clientOutput, req, respBody, 
                                            respTyp, idx, repReq, resp, 
                                            shouldSync, lastPutBody, req0, 
                                            resp0, msg, replica0, idx0 >>

sndResp(self) == /\ pc[self] = "sndResp"
                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> PRIMARY_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                 /\ LET value150 == resp'[self] IN
                      /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                      /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value150), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                      /\ IF DEBUG
                            THEN /\ PrintT(<<"ServerSendResp", self, (req[self]).from>>)
                                 /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                 /\ UNCHANGED << fd, fs, primary, clientInput, clientOutput, 
                                 req, respBody, respTyp, idx, repReq, repResp, 
                                 replicaSet, shouldSync, lastPutBody, replica, 
                                 req0, resp0, msg, replica0, idx0 >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value160 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value160]
                        /\ LET value170 == self IN
                             /\ primary' = (primary) \ ({value170})
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, fs, clientInput, clientOutput, req, 
                                   respBody, respTyp, idx, repReq, repResp, 
                                   resp, replicaSet, shouldSync, lastPutBody, 
                                   replica, req0, resp0, msg, replica0, idx0 >>

Replica(self) == replicaLoop(self) \/ syncPrimary(self)
                    \/ sndSyncReqLoop(self) \/ rcvSyncRespLoop(self)
                    \/ rcvMsg(self) \/ handleBackup(self)
                    \/ handlePrimary(self) \/ sndReplicaReqLoop(self)
                    \/ rcvReplicaRespLoop(self) \/ sndResp(self)
                    \/ failLabel(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ IF DEBUG
                                     THEN /\ PrintT(<<"ClientLoop", self>>)
                                          /\ (Len(clientInput)) > (0)
                                          /\ LET res00 == Head(clientInput) IN
                                               /\ clientInput' = Tail(clientInput)
                                               /\ LET yielded_clientInput0 == res00 IN
                                                    /\ msg' = [msg EXCEPT ![self] = yielded_clientInput0]
                                                    /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                     ELSE /\ (Len(clientInput)) > (0)
                                          /\ LET res01 == Head(clientInput) IN
                                               /\ clientInput' = Tail(clientInput)
                                               /\ LET yielded_clientInput1 == res01 IN
                                                    /\ msg' = [msg EXCEPT ![self] = yielded_clientInput1]
                                                    /\ idx0' = [idx0 EXCEPT ![self] = (idx0[self]) + (1)]
                                                    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << clientInput, msg, idx0 >>
                    /\ UNCHANGED << network, fd, fs, primary, clientOutput, 
                                    req, respBody, respTyp, idx, repReq, 
                                    repResp, resp, replicaSet, shouldSync, 
                                    lastPutBody, replica, req0, resp0, 
                                    replica0 >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (Cardinality(primary)) > (0)
                      THEN /\ LET yielded_primary50 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary50]
                                /\ IF (replica0'[self]) # (NULL)
                                      THEN /\ \/ /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> (msg[self]).body, srcTyp |-> CLIENT_SRC, typ |-> (msg[self]).typ, id |-> idx0[self]]]
                                                 /\ LET value180 == req0'[self] IN
                                                      /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                      /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value180), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                      /\ IF DEBUG
                                                            THEN /\ PrintT(<<"ClientSendReq", self, replica0'[self]>>)
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                              \/ /\ LET yielded_fd60 == (fd)[replica0'[self]] IN
                                                      /\ yielded_fd60
                                                      /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                 /\ UNCHANGED <<network, req0>>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           /\ UNCHANGED << network, req0 >>
                      ELSE /\ LET yielded_primary60 == NULL IN
                                /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary60]
                                /\ IF (replica0'[self]) # (NULL)
                                      THEN /\ \/ /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> (msg[self]).body, srcTyp |-> CLIENT_SRC, typ |-> (msg[self]).typ, id |-> idx0[self]]]
                                                 /\ LET value181 == req0'[self] IN
                                                      /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                      /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value181), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                      /\ IF DEBUG
                                                            THEN /\ PrintT(<<"ClientSendReq", self, replica0'[self]>>)
                                                                 /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                              \/ /\ LET yielded_fd61 == (fd)[replica0'[self]] IN
                                                      /\ yielded_fd61
                                                      /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                                 /\ UNCHANGED <<network, req0>>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           /\ UNCHANGED << network, req0 >>
                /\ UNCHANGED << fd, fs, primary, clientInput, clientOutput, 
                                req, respBody, respTyp, idx, repReq, repResp, 
                                resp, replicaSet, shouldSync, lastPutBody, 
                                replica, resp0, msg, idx0 >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ IF DEBUG
                       THEN /\ PrintT(<<"ClientRcvRespEither", self>>)
                            /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                            "Failure of assertion at line 1274, column 11.")
                                  /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                  /\ LET readMsg30 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                       /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                                       /\ LET yielded_network40 == readMsg30 IN
                                            /\ resp0' = [resp0 EXCEPT ![self] = yielded_network40]
                                            /\ IF DEBUG
                                                  THEN /\ PrintT(<<"ClientRcvResp", self, replica0[self]>>)
                                                       /\ IF ((resp0'[self]).id) # (idx0[self])
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED clientOutput
                                                             ELSE /\ IF ((msg[self]).typ) = (PUT_REQ)
                                                                        THEN /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                       "Failure of assertion at line 1286, column 21.")
                                                                             /\ clientOutput' = ((resp0'[self]).body).content
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ IF ((msg[self]).typ) = (GET_REQ)
                                                                                   THEN /\ Assert(((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (GET_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                                  "Failure of assertion at line 1291, column 23.")
                                                                                        /\ clientOutput' = ((resp0'[self]).body).content
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                   ELSE /\ Assert(FALSE, 
                                                                                                  "Failure of assertion at line 1295, column 23.")
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                        /\ UNCHANGED clientOutput
                                                  ELSE /\ IF ((resp0'[self]).id) # (idx0[self])
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED clientOutput
                                                             ELSE /\ IF ((msg[self]).typ) = (PUT_REQ)
                                                                        THEN /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                       "Failure of assertion at line 1305, column 21.")
                                                                             /\ clientOutput' = ((resp0'[self]).body).content
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ IF ((msg[self]).typ) = (GET_REQ)
                                                                                   THEN /\ Assert(((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (GET_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                                  "Failure of assertion at line 1310, column 23.")
                                                                                        /\ clientOutput' = ((resp0'[self]).body).content
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                   ELSE /\ Assert(FALSE, 
                                                                                                  "Failure of assertion at line 1314, column 23.")
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                        /\ UNCHANGED clientOutput
                               \/ /\ LET yielded_fd70 == (fd)[replica0[self]] IN
                                       LET yielded_network50 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                         /\ (yielded_fd70) /\ ((yielded_network50) = (0))
                                         /\ IF DEBUG
                                               THEN /\ PrintT(<<"ClientDetectedFail", self, replica0[self]>>)
                                                    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                  /\ UNCHANGED <<network, clientOutput, resp0>>
                       ELSE /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                            "Failure of assertion at line 1338, column 11.")
                                  /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                  /\ LET readMsg31 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                       /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                                       /\ LET yielded_network41 == readMsg31 IN
                                            /\ resp0' = [resp0 EXCEPT ![self] = yielded_network41]
                                            /\ IF DEBUG
                                                  THEN /\ PrintT(<<"ClientRcvResp", self, replica0[self]>>)
                                                       /\ IF ((resp0'[self]).id) # (idx0[self])
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED clientOutput
                                                             ELSE /\ IF ((msg[self]).typ) = (PUT_REQ)
                                                                        THEN /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                       "Failure of assertion at line 1350, column 21.")
                                                                             /\ clientOutput' = ((resp0'[self]).body).content
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ IF ((msg[self]).typ) = (GET_REQ)
                                                                                   THEN /\ Assert(((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (GET_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                                  "Failure of assertion at line 1355, column 23.")
                                                                                        /\ clientOutput' = ((resp0'[self]).body).content
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                   ELSE /\ Assert(FALSE, 
                                                                                                  "Failure of assertion at line 1359, column 23.")
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                        /\ UNCHANGED clientOutput
                                                  ELSE /\ IF ((resp0'[self]).id) # (idx0[self])
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                                  /\ UNCHANGED clientOutput
                                                             ELSE /\ IF ((msg[self]).typ) = (PUT_REQ)
                                                                        THEN /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                       "Failure of assertion at line 1369, column 21.")
                                                                             /\ clientOutput' = ((resp0'[self]).body).content
                                                                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                        ELSE /\ IF ((msg[self]).typ) = (GET_REQ)
                                                                                   THEN /\ Assert(((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (GET_RESP))) /\ (((resp0'[self]).id) = (idx0[self])), 
                                                                                                  "Failure of assertion at line 1374, column 23.")
                                                                                        /\ clientOutput' = ((resp0'[self]).body).content
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                   ELSE /\ Assert(FALSE, 
                                                                                                  "Failure of assertion at line 1378, column 23.")
                                                                                        /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                                                        /\ UNCHANGED clientOutput
                               \/ /\ LET yielded_fd71 == (fd)[replica0[self]] IN
                                       LET yielded_network51 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                         /\ (yielded_fd71) /\ ((yielded_network51) = (0))
                                         /\ IF DEBUG
                                               THEN /\ PrintT(<<"ClientDetectedFail", self, replica0[self]>>)
                                                    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                  /\ UNCHANGED <<network, clientOutput, resp0>>
                 /\ UNCHANGED << fd, fs, primary, clientInput, req, respBody, 
                                 respTyp, idx, repReq, repResp, resp, 
                                 replicaSet, shouldSync, lastPutBody, replica, 
                                 req0, msg, replica0, idx0 >>

Client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in REPLICA_SET: Replica(self))
           \/ (\E self \in CLIENT_SET: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in REPLICA_SET : WF_vars(Replica(self))
        /\ \A self \in CLIENT_SET : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Constraints

ReplicaVersionNumber(r) == lastPutBody[r].versionNumber < 5
VersionNumberCnst == \A r \in REPLICA_SET: ReplicaVersionNumber(r)

\* Invariants

IsAlive(r) == /\ pc[r] # "failLabel"
              /\ pc[r] # "Done"
AliveReplicas == {r \in REPLICA_SET: IsAlive(r)}
AtLeastOneAlive == \E r \in REPLICA_SET: IsAlive(r)
Primary == IF AtLeastOneAlive
               THEN CHOOSE r \in REPLICA_SET:
                   /\ IsAlive(r)
                   /\ \A p \in AliveReplicas: (r =< p)
           ELSE <<>>
ConsistencyOK == (AtLeastOneAlive /\ pc[Primary] = "sndResp") => 
                    \A r \in AliveReplicas: \A key \in KEY_SET: fs[Primary][key] = fs[r][key]

\* Properties

ReceiveResp(client) == pc[client] = "sndReq" ~> pc[client] = "rcvResp"
ClientsOK == \A client \in CLIENT_SET: ReceiveResp(client)

=============================================================================
\* Modification History
\* Last modified Wed Oct 20 13:55:55 PDT 2021 by shayan
\* Created Fri Sep 03 15:43:20 PDT 2021 by shayan
