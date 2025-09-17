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
CONSTANT NUM_PUT_CLIENTS
CONSTANT NUM_GET_CLIENTS
CONSTANT EXPLORE_FAIL

CONSTANT GET_CLIENT_RUN
CONSTANT PUT_CLIENT_RUN

ASSUME NUM_REPLICAS > 0 /\ NUM_PUT_CLIENTS >= 0 /\ NUM_GET_CLIENTS >= 0

(********************

--mpcal pbkvs {

    define {
        NUM_NODES == NUM_REPLICAS + NUM_PUT_CLIENTS + NUM_GET_CLIENTS

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

        NODE_SET == 1..NUM_NODES
        REPLICA_SET == 1..NUM_REPLICAS
        PUT_CLIENT_SET == (NUM_REPLICAS+1)..(NUM_REPLICAS+NUM_PUT_CLIENTS)
        GET_CLIENT_SET == (NUM_REPLICAS+NUM_PUT_CLIENTS+1)..(NUM_REPLICAS+NUM_PUT_CLIENTS+NUM_GET_CLIENTS)

        MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}

        KEY_SET == {KEY1}
        VALUE_SET == {VALUE1}
        
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
                assert(req.to = self);
                if (primary = self /\ req.srcTyp = CLIENT_SRC) {
                    goto handlePrimary;
                } else {
                    goto handleBackup;
                };
            };

        handleBackup:
            assert(req.srcTyp = PRIMARY_SRC);
            if (req.typ = GET_REQ) {
                respBody := [content |-> fs[self][req.body.key]];
                respTyp := GET_RESP;
            } else if (req.typ = PUT_REQ) {
                fs[self][req.body.key] := req.body.value;
                assert(req.body.versionNumber > lastPutBody.versionNumber);
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
        };

    failLabel:
        fd[self] := TRUE;
        primary := self;
    }

    archetype APutClient(ref net[_], ref fd[_], ref primary, ref netLen[_], ref input, ref output)
    variables
        req, resp, body, replica;
    {
    putClientLoop:
        while (PUT_CLIENT_RUN) {
            body := input;

        sndPutReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    req := [from |-> self, to |-> replica, body |-> body,
                            srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
                    net[<<req.to, REQ_INDEX>>] := req;
                } or {
                    await fd[replica];
                    goto sndPutReq; \* retry the request
                };
            } else {
                goto Done;
            };

        rcvPutResp:
            either {
                resp := net[<<self, RESP_INDEX>>];
                assert(
                    /\ resp.to = self
                    /\ resp.from = replica
                    /\ resp.body = ACK_MSG_BODY
                    /\ resp.srcTyp = PRIMARY_SRC
                    /\ resp.typ = PUT_RESP
                    /\ resp.id = 1
                );
                output := resp;
                \* print <<"PUT RESP: ", resp>>;
            } or {
                await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                goto sndPutReq; \* retry the request
            };
        };
    }

    archetype AGetClient(ref net[_], ref fd[_], ref primary, ref netLen[_], ref input, ref output)
    variables
        req, resp, body, replica;
    {
    getClientLoop:
        while (GET_CLIENT_RUN) {
            body := input;

        sndGetReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    req := [from |-> self, to |-> replica, body |-> body,
                            srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
                    net[<<req.to, REQ_INDEX>>] := req;
                } or {
                    await fd[replica];
                    goto sndGetReq; \* retry the request
                };
            } else {
                goto Done;
            };

        rcvGetResp:
            either {
                resp := net[<<self, RESP_INDEX>>];
                assert(
                    /\ resp.to = self
                    /\ resp.from = replica
                    /\ resp.srcTyp = PRIMARY_SRC
                    /\ resp.typ = GET_RESP
                    /\ resp.id = 2
                );
                output := resp;
                \* print <<"GET RESP: ", resp>>;
            } or {
                await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                goto sndGetReq; \* retry the request
            };
        };
    }

    archetype AClient(ref net[_], ref fd[_], ref primary, ref netLen[_], ref input, ref output)
    variables
        req, resp, msg, replica, idx = 0;
    {
    clientLoop:
        while (TRUE) {
            either {
                msg := input;
                idx := idx + 1;
            } or {
                resp := net[<<self, RESP_INDEX>>]; \* discard, this is out of sequence
            };

        sndReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    req := [from |-> self, to |-> replica, body |-> msg.body,
                            srcTyp |-> CLIENT_SRC, typ |-> msg.typ, id |-> idx];
                    net[<<req.to, REQ_INDEX>>] := req;
                } or {
                    await fd[replica];
                    goto sndReq; \* retry the request
                };
            } else {
                goto Done;
            };

        rcvResp:
            either {
                resp := net[<<self, RESP_INDEX>>];
                if(resp.id # idx) {
                    goto rcvResp;
                } else {
                    if(msg.typ = PUT_REQ) {
                        assert(
                            /\ resp.to = self
                            /\ resp.from = replica
                            /\ resp.body = ACK_MSG_BODY
                            /\ resp.srcTyp = PRIMARY_SRC
                            /\ resp.typ = PUT_RESP
                            /\ resp.id = idx
                        );
                        output := resp.body.content;
                    } else if(msg.typ = GET_REQ) {
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
                goto sndReq; \* retry the request
            };
        };
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]];
        fd = [id \in REPLICA_SET |-> FALSE];
        fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]];
        primary = REPLICA_SET;
        putInput = [key |-> KEY1, value |-> VALUE1], putOutput;
        getInput = [key |-> KEY1], getOutput;

    fair process (Replica \in REPLICA_SET) == instance AReplica(ref network[_], ref fs[_][_], ref fd[_], ref network[_], ref primary, ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_][_] via FileSystem
        mapping @3[_] via PerfectFD
        mapping @4[_] via NetworkToggle
        mapping @5 via LeaderElection
        mapping @6[_] via NetworkBufferLength;

    fair process (PutClient \in PUT_CLIENT_SET) == instance APutClient(ref network[_], ref fd[_], ref primary, ref network[_], ref putInput, putOutput)
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3 via LeaderElection
        mapping @4[_] via NetworkBufferLength;

    fair process (GetClient \in GET_CLIENT_SET) == instance AGetClient(ref network[_], ref fd[_], ref primary, ref network[_], ref getInput, ref getOutput)
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3 via LeaderElection
        mapping @4[_] via NetworkBufferLength;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm pbkvs {
  variables network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [id \in REPLICA_SET |-> FALSE]; fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]]; primary = REPLICA_SET; putInput = [key |-> KEY1, value |-> VALUE1]; putOutput; getInput = [key |-> KEY1]; getOutput;
  define{
    NUM_NODES == ((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (NUM_GET_CLIENTS)
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
    NODE_SET == (1) .. (NUM_NODES)
    REPLICA_SET == (1) .. (NUM_REPLICAS)
    PUT_CLIENT_SET == ((NUM_REPLICAS) + (1)) .. ((NUM_REPLICAS) + (NUM_PUT_CLIENTS))
    GET_CLIENT_SET == (((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (1)) .. (((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (NUM_GET_CLIENTS))
    MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}
    KEY_SET == {KEY1}
    VALUE_SET == {VALUE1}
    NULL == 0
  }
  
  fair process (Replica \in REPLICA_SET)
    variables req; respBody; respTyp; idx; repReq; repResp; resp; replicaSet; shouldSync = FALSE; lastPutBody = [versionNumber |-> 0]; replica;
  {
    replicaLoop:
      if(TRUE) {
        replicaSet := (REPLICA_SET) \ ({self});
        idx := 1;
        if(EXPLORE_FAIL) {
          either {
            skip;
            goto syncPrimary;
          } or {
            with (value00 = FALSE) {
              with (network0 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value00]]) {
                with (value110 = FALSE) {
                  network := [network0 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network0)[<<self, RESP_INDEX>>]).queue, enabled |-> value110]];
                  goto failLabel;
                };
              };
            };
          };
        } else {
          goto syncPrimary;
        };
      } else {
        goto failLabel;
      };
    syncPrimary:
      if((Cardinality(primary)) > (0)) {
        with (yielded_primary = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          if(((yielded_primary) = (self)) /\ (shouldSync)) {
            shouldSync := TRUE;
            goto sndSyncReqLoop;
          } else {
            goto rcvMsg;
          };
        };
      } else {
        with (yielded_primary0 = NULL) {
          if(((yielded_primary0) = (self)) /\ (shouldSync)) {
            shouldSync := TRUE;
            goto sndSyncReqLoop;
          } else {
            goto rcvMsg;
          };
        };
      };
    sndSyncReqLoop:
      if((idx) <= (NUM_REPLICAS)) {
        if((idx) # (self)) {
          either {
            repReq := [from |-> self, to |-> idx, body |-> lastPutBody, srcTyp |-> PRIMARY_SRC, typ |-> SYNC_REQ, id |-> 3];
            with (value20 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network1 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value20), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if(EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network1;
                    goto sndSyncReqLoop;
                  } or {
                    with (value30 = FALSE) {
                      with (network2 = [network1 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network1)[<<self, REQ_INDEX>>]).queue, enabled |-> value30]]) {
                        with (value40 = FALSE) {
                          network := [network1 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network1)[<<self, RESP_INDEX>>]).queue, enabled |-> value40]];
                          goto failLabel;
                        };
                      };
                    };
                  };
                } else {
                  network := network1;
                  goto sndSyncReqLoop;
                };
              };
            };
          } or {
            with (yielded_fd10 = (fd)[idx]) {
              await yielded_fd10;
              idx := (idx) + (1);
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndSyncReqLoop;
                } or {
                  with (value31 = FALSE) {
                    with (network3 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value31]]) {
                      with (value41 = FALSE) {
                        network := [network3 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network3)[<<self, RESP_INDEX>>]).queue, enabled |-> value41]];
                        goto failLabel;
                      };
                    };
                  };
                };
              } else {
                goto sndSyncReqLoop;
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if(EXPLORE_FAIL) {
            either {
              skip;
              goto sndSyncReqLoop;
            } or {
              with (value32 = FALSE) {
                with (network4 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value32]]) {
                  with (value42 = FALSE) {
                    network := [network4 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network4)[<<self, RESP_INDEX>>]).queue, enabled |-> value42]];
                    goto failLabel;
                  };
                };
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
      if((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg00 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
            with (yielded_network8 = readMsg00) {
              repResp := yielded_network8;
              with (yielded_fd00 = (fd)[(repResp).from]) {
                assert ((((((repResp).id) = (3)) /\ (((repResp).to) = (self))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (SYNC_RESP))) /\ ((((repResp).from) \in (replicaSet)) \/ (yielded_fd00));
                if((((repResp).body).versionNumber) > ((lastPutBody).versionNumber)) {
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
          with (yielded_fd11 = (fd)[replica]) {
            with (yielded_network00 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
              await (yielded_fd11) /\ ((yielded_network00) = (0));
              replicaSet := (replicaSet) \ ({replica});
              goto rcvSyncRespLoop;
            };
          };
        };
      } else {
        goto rcvMsg;
      };
    rcvMsg:
      if((Cardinality(primary)) > (0)) {
        with (yielded_primary3 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          if(((yielded_primary3) = (self)) /\ (shouldSync)) {
            goto syncPrimary;
          } else {
            assert ((network)[<<self, REQ_INDEX>>]).enabled;
            await (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0);
            with (readMsg10 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network10 = readMsg10) {
                req := yielded_network10;
                assert ((req).to) = (self);
                if((Cardinality(primary)) > (0)) {
                  with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                    if(((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                      goto handlePrimary;
                    } else {
                      goto handleBackup;
                    };
                  };
                } else {
                  with (yielded_primary2 = NULL) {
                    if(((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
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
      } else {
        with (yielded_primary4 = NULL) {
          if(((yielded_primary4) = (self)) /\ (shouldSync)) {
            goto syncPrimary;
          } else {
            assert ((network)[<<self, REQ_INDEX>>]).enabled;
            await (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0);
            with (readMsg11 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network11 = readMsg11) {
                req := yielded_network11;
                assert ((req).to) = (self);
                if((Cardinality(primary)) > (0)) {
                  with (yielded_primary1 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
                    if(((yielded_primary1) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
                      goto handlePrimary;
                    } else {
                      goto handleBackup;
                    };
                  };
                } else {
                  with (yielded_primary2 = NULL) {
                    if(((yielded_primary2) = (self)) /\ (((req).srcTyp) = (CLIENT_SRC))) {
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
    handleBackup:
      assert ((req).srcTyp) = (PRIMARY_SRC);
      if(((req).typ) = (GET_REQ)) {
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
        if(((req).typ) = (PUT_REQ)) {
          with (value60 = ((req).body).value) {
            fs := [fs EXCEPT ![self][((req).body).key] = value60];
            assert (((req).body).versionNumber) > ((lastPutBody).versionNumber);
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
          if(((req).typ) = (SYNC_REQ)) {
            if((((req).body).versionNumber) > ((lastPutBody).versionNumber)) {
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
    handlePrimary:
      assert ((req).srcTyp) = (CLIENT_SRC);
      if(((req).typ) = (GET_REQ)) {
        with (yielded_fs00 = ((fs)[self])[((req).body).key]) {
          respBody := [content |-> yielded_fs00];
          respTyp := GET_RESP;
          goto sndResp;
        };
      } else {
        if(((req).typ) = (PUT_REQ)) {
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
    sndReplicaReqLoop:
      if((idx) <= (NUM_REPLICAS)) {
        if((idx) # (self)) {
          either {
            repReq := [from |-> self, to |-> idx, body |-> lastPutBody, srcTyp |-> PRIMARY_SRC, typ |-> PUT_REQ, id |-> (req).id];
            with (value100 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network5 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value100), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if(EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network5;
                    goto sndReplicaReqLoop;
                  } or {
                    with (value111 = FALSE) {
                      with (network6 = [network5 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network5)[<<self, REQ_INDEX>>]).queue, enabled |-> value111]]) {
                        with (value120 = FALSE) {
                          network := [network5 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network5)[<<self, RESP_INDEX>>]).queue, enabled |-> value120]];
                          goto failLabel;
                        };
                      };
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
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndReplicaReqLoop;
                } or {
                  with (value112 = FALSE) {
                    with (network7 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value112]]) {
                      with (value121 = FALSE) {
                        network := [network7 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network7)[<<self, RESP_INDEX>>]).queue, enabled |-> value121]];
                        goto failLabel;
                      };
                    };
                  };
                };
              } else {
                goto sndReplicaReqLoop;
              };
            };
          };
        } else {
          idx := (idx) + (1);
          if(EXPLORE_FAIL) {
            either {
              skip;
              goto sndReplicaReqLoop;
            } or {
              with (value113 = FALSE) {
                with (network8 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value113]]) {
                  with (value122 = FALSE) {
                    network := [network8 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network8)[<<self, RESP_INDEX>>]).queue, enabled |-> value122]];
                    goto failLabel;
                  };
                };
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
      if((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg20 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            with (network9 = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]) {
              with (yielded_network20 = readMsg20) {
                repResp := yielded_network20;
                with (yielded_fd40 = (fd)[(repResp).from]) {
                  assert ((((((((repResp).from) \in (replicaSet)) \/ (yielded_fd40)) /\ (((repResp).to) = (self))) /\ (((repResp).body) = (ACK_MSG_BODY))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (PUT_RESP))) /\ (((repResp).id) = ((req).id));
                  replicaSet := (replicaSet) \ ({(repResp).from});
                  if(EXPLORE_FAIL) {
                    either {
                      skip;
                      network := network9;
                      goto rcvReplicaRespLoop;
                    } or {
                      with (value130 = FALSE) {
                        with (network10 = [network9 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network9)[<<self, REQ_INDEX>>]).queue, enabled |-> value130]]) {
                          with (value140 = FALSE) {
                            network := [network9 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network9)[<<self, RESP_INDEX>>]).queue, enabled |-> value140]];
                            goto failLabel;
                          };
                        };
                      };
                    };
                  } else {
                    network := network9;
                    goto rcvReplicaRespLoop;
                  };
                };
              };
            };
          };
        } or {
          replica := CHOOSE r \in replicaSet : TRUE;
          with (yielded_fd50 = (fd)[replica]) {
            with (yielded_network30 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
              await (yielded_fd50) /\ ((yielded_network30) = (0));
              replicaSet := (replicaSet) \ ({replica});
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto rcvReplicaRespLoop;
                } or {
                  with (value131 = FALSE) {
                    with (network11 = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value131]]) {
                      with (value141 = FALSE) {
                        network := [network11 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network11)[<<self, RESP_INDEX>>]).queue, enabled |-> value141]];
                        goto failLabel;
                      };
                    };
                  };
                };
              } else {
                goto rcvReplicaRespLoop;
              };
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
        goto replicaLoop;
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
  
  fair process (PutClient \in PUT_CLIENT_SET)
    variables req0; resp0; body; replica0; output = putOutput;
  {
    putClientLoop:
      if(PUT_CLIENT_RUN) {
        body := putInput;
        goto sndPutReq;
      } else {
        goto Done;
      };
    sndPutReq:
      if((Cardinality(primary)) > (0)) {
        with (yielded_primary50 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          replica0 := yielded_primary50;
          if((replica0) # (NULL)) {
            either {
              req0 := [from |-> self, to |-> replica0, body |-> body, srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
              with (value180 = req0) {
                await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value180), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                goto rcvPutResp;
              };
            } or {
              with (yielded_fd60 = (fd)[replica0]) {
                await yielded_fd60;
                goto sndPutReq;
              };
            };
          } else {
            goto Done;
          };
        };
      } else {
        with (yielded_primary60 = NULL) {
          replica0 := yielded_primary60;
          if((replica0) # (NULL)) {
            either {
              req0 := [from |-> self, to |-> replica0, body |-> body, srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
              with (value181 = req0) {
                await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value181), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                goto rcvPutResp;
              };
            } or {
              with (yielded_fd61 = (fd)[replica0]) {
                await yielded_fd61;
                goto sndPutReq;
              };
            };
          } else {
            goto Done;
          };
        };
      };
    rcvPutResp:
      either {
        assert ((network)[<<self, RESP_INDEX>>]).enabled;
        await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
        with (readMsg30 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
          network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
          with (yielded_network40 = readMsg30) {
            resp0 := yielded_network40;
            assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (1));
            output := resp0;
            goto putClientLoop;
          };
        };
      } or {
        with (yielded_fd70 = (fd)[replica0]) {
          with (yielded_network50 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
            await (yielded_fd70) /\ ((yielded_network50) = (0));
            goto sndPutReq;
          };
        };
      };
  }
  
  fair process (GetClient \in GET_CLIENT_SET)
    variables req1; resp1; body0; replica1;
  {
    getClientLoop:
      if(GET_CLIENT_RUN) {
        body0 := getInput;
        goto sndGetReq;
      } else {
        goto Done;
      };
    sndGetReq:
      if((Cardinality(primary)) > (0)) {
        with (yielded_primary70 = CHOOSE x \in primary : \A r \in primary : (x) <= (r)) {
          replica1 := yielded_primary70;
          if((replica1) # (NULL)) {
            either {
              req1 := [from |-> self, to |-> replica1, body |-> body0, srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
              with (value190 = req1) {
                await ((network)[<<(req1).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req1).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1).to, REQ_INDEX>>]).queue, value190), enabled |-> ((network)[<<(req1).to, REQ_INDEX>>]).enabled]];
                goto rcvGetResp;
              };
            } or {
              with (yielded_fd80 = (fd)[replica1]) {
                await yielded_fd80;
                goto sndGetReq;
              };
            };
          } else {
            goto Done;
          };
        };
      } else {
        with (yielded_primary80 = NULL) {
          replica1 := yielded_primary80;
          if((replica1) # (NULL)) {
            either {
              req1 := [from |-> self, to |-> replica1, body |-> body0, srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
              with (value191 = req1) {
                await ((network)[<<(req1).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req1).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1).to, REQ_INDEX>>]).queue, value191), enabled |-> ((network)[<<(req1).to, REQ_INDEX>>]).enabled]];
                goto rcvGetResp;
              };
            } or {
              with (yielded_fd81 = (fd)[replica1]) {
                await yielded_fd81;
                goto sndGetReq;
              };
            };
          } else {
            goto Done;
          };
        };
      };
    rcvGetResp:
      either {
        assert ((network)[<<self, RESP_INDEX>>]).enabled;
        await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
        with (readMsg40 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
          network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
          with (yielded_network60 = readMsg40) {
            resp1 := yielded_network60;
            assert ((((((resp1).to) = (self)) /\ (((resp1).from) = (replica1))) /\ (((resp1).srcTyp) = (PRIMARY_SRC))) /\ (((resp1).typ) = (GET_RESP))) /\ (((resp1).id) = (2));
            getOutput := resp1;
            goto getClientLoop;
          };
        };
      } or {
        with (yielded_fd90 = (fd)[replica1]) {
          with (yielded_network70 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
            await (yielded_fd90) /\ ((yielded_network70) = (0));
            goto sndGetReq;
          };
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "a6e2760d" /\ chksum(tla) = "3f4282be")
CONSTANT defaultInitValue
VARIABLES network, fd, fs, primary, putInput, putOutput, getInput, getOutput, 
          pc

(* define statement *)
NUM_NODES == ((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (NUM_GET_CLIENTS)
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
NODE_SET == (1) .. (NUM_NODES)
REPLICA_SET == (1) .. (NUM_REPLICAS)
PUT_CLIENT_SET == ((NUM_REPLICAS) + (1)) .. ((NUM_REPLICAS) + (NUM_PUT_CLIENTS))
GET_CLIENT_SET == (((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (1)) .. (((NUM_REPLICAS) + (NUM_PUT_CLIENTS)) + (NUM_GET_CLIENTS))
MSG_INDEX_SET == {REQ_INDEX, RESP_INDEX}
KEY_SET == {KEY1}
VALUE_SET == {VALUE1}
NULL == 0

VARIABLES req, respBody, respTyp, idx, repReq, repResp, resp, replicaSet, 
          shouldSync, lastPutBody, replica, req0, resp0, body, replica0, 
          output, req1, resp1, body0, replica1

vars == << network, fd, fs, primary, putInput, putOutput, getInput, getOutput, 
           pc, req, respBody, respTyp, idx, repReq, repResp, resp, replicaSet, 
           shouldSync, lastPutBody, replica, req0, resp0, body, replica0, 
           output, req1, resp1, body0, replica1 >>

ProcSet == (REPLICA_SET) \cup (PUT_CLIENT_SET) \cup (GET_CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [id \in REPLICA_SET |-> FALSE]
        /\ fs = [id \in REPLICA_SET |-> [key \in KEY_SET |-> ""]]
        /\ primary = REPLICA_SET
        /\ putInput = [key |-> KEY1, value |-> VALUE1]
        /\ putOutput = defaultInitValue
        /\ getInput = [key |-> KEY1]
        /\ getOutput = defaultInitValue
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
        (* Process PutClient *)
        /\ req0 = [self \in PUT_CLIENT_SET |-> defaultInitValue]
        /\ resp0 = [self \in PUT_CLIENT_SET |-> defaultInitValue]
        /\ body = [self \in PUT_CLIENT_SET |-> defaultInitValue]
        /\ replica0 = [self \in PUT_CLIENT_SET |-> defaultInitValue]
        /\ output = [self \in PUT_CLIENT_SET |-> putOutput]
        (* Process GetClient *)
        /\ req1 = [self \in GET_CLIENT_SET |-> defaultInitValue]
        /\ resp1 = [self \in GET_CLIENT_SET |-> defaultInitValue]
        /\ body0 = [self \in GET_CLIENT_SET |-> defaultInitValue]
        /\ replica1 = [self \in GET_CLIENT_SET |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in REPLICA_SET -> "replicaLoop"
                                        [] self \in PUT_CLIENT_SET -> "putClientLoop"
                                        [] self \in GET_CLIENT_SET -> "getClientLoop"]

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
                                                        LET value110 == FALSE IN
                                                          /\ network' = [network0 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network0)[<<self, RESP_INDEX>>]).queue, enabled |-> value110]]
                                                          /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                           /\ UNCHANGED network
                           ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                /\ UNCHANGED << network, idx, replicaSet >>
                     /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                     getInput, getOutput, req, respBody, 
                                     respTyp, repReq, repResp, resp, 
                                     shouldSync, lastPutBody, replica, req0, 
                                     resp0, body, replica0, output, req1, 
                                     resp1, body0, replica1 >>

syncPrimary(self) == /\ pc[self] = "syncPrimary"
                     /\ IF (Cardinality(primary)) > (0)
                           THEN /\ LET yielded_primary == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                     IF ((yielded_primary) = (self)) /\ (shouldSync[self])
                                        THEN /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                             /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                             /\ UNCHANGED shouldSync
                           ELSE /\ LET yielded_primary0 == NULL IN
                                     IF ((yielded_primary0) = (self)) /\ (shouldSync[self])
                                        THEN /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                             /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                             /\ UNCHANGED shouldSync
                     /\ UNCHANGED << network, fd, fs, primary, putInput, 
                                     putOutput, getInput, getOutput, req, 
                                     respBody, respTyp, idx, repReq, repResp, 
                                     resp, replicaSet, lastPutBody, replica, 
                                     req0, resp0, body, replica0, output, req1, 
                                     resp1, body0, replica1 >>

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
                                                                                        /\ network' = [network1 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network1)[<<self, RESP_INDEX>>]).queue, enabled |-> value40]]
                                                                                        /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                    ELSE /\ network' = network1
                                                                         /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                 \/ /\ LET yielded_fd10 == (fd)[idx[self]] IN
                                                         /\ yielded_fd10
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
                        /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                        getInput, getOutput, req, respBody, 
                                        respTyp, repResp, resp, replicaSet, 
                                        shouldSync, lastPutBody, replica, req0, 
                                        resp0, body, replica0, output, req1, 
                                        resp1, body0, replica1 >>

rcvSyncRespLoop(self) == /\ pc[self] = "rcvSyncRespLoop"
                         /\ IF (Cardinality(replicaSet[self])) > (0)
                               THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                    "Failure of assertion at line 613, column 11.")
                                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                          /\ LET readMsg00 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                                               /\ LET yielded_network8 == readMsg00 IN
                                                    /\ repResp' = [repResp EXCEPT ![self] = yielded_network8]
                                                    /\ LET yielded_fd00 == (fd)[(repResp'[self]).from] IN
                                                         /\ Assert(((((((repResp'[self]).id) = (3)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (SYNC_RESP))) /\ ((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd00)), 
                                                                   "Failure of assertion at line 620, column 17.")
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
                                          /\ LET yielded_fd11 == (fd)[replica'[self]] IN
                                               LET yielded_network00 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                 /\ (yielded_fd11) /\ ((yielded_network00) = (0))
                                                 /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({replica'[self]})]
                                                 /\ pc' = [pc EXCEPT ![self] = "rcvSyncRespLoop"]
                                          /\ UNCHANGED <<network, fs, idx, repResp, lastPutBody>>
                               ELSE /\ pc' = [pc EXCEPT ![self] = "rcvMsg"]
                                    /\ UNCHANGED << network, fs, idx, repResp, 
                                                    replicaSet, lastPutBody, 
                                                    replica >>
                         /\ UNCHANGED << fd, primary, putInput, putOutput, 
                                         getInput, getOutput, req, respBody, 
                                         respTyp, repReq, resp, shouldSync, 
                                         req0, resp0, body, replica0, output, 
                                         req1, resp1, body0, replica1 >>

rcvMsg(self) == /\ pc[self] = "rcvMsg"
                /\ IF (Cardinality(primary)) > (0)
                      THEN /\ LET yielded_primary3 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                IF ((yielded_primary3) = (self)) /\ (shouldSync[self])
                                   THEN /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                        /\ UNCHANGED << network, req >>
                                   ELSE /\ Assert(((network)[<<self, REQ_INDEX>>]).enabled, 
                                                  "Failure of assertion at line 655, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg10 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network10 == readMsg10 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network10]
                                                  /\ Assert(((req'[self]).to) = (self), 
                                                            "Failure of assertion at line 661, column 17.")
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
                                                  "Failure of assertion at line 688, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg11 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network11 == readMsg11 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network11]
                                                  /\ Assert(((req'[self]).to) = (self), 
                                                            "Failure of assertion at line 694, column 17.")
                                                  /\ IF (Cardinality(primary)) > (0)
                                                        THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                  IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                        ELSE /\ LET yielded_primary2 == NULL IN
                                                                  IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                /\ UNCHANGED << fd, fs, primary, putInput, putOutput, getInput, 
                                getOutput, respBody, respTyp, idx, repReq, 
                                repResp, resp, replicaSet, shouldSync, 
                                lastPutBody, replica, req0, resp0, body, 
                                replica0, output, req1, resp1, body0, replica1 >>

handleBackup(self) == /\ pc[self] = "handleBackup"
                      /\ Assert(((req[self]).srcTyp) = (PRIMARY_SRC), 
                                "Failure of assertion at line 718, column 7.")
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
                                 /\ UNCHANGED << fs, shouldSync, lastPutBody >>
                            ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                       THEN /\ LET value60 == ((req[self]).body).value IN
                                                 /\ fs' = [fs EXCEPT ![self][((req[self]).body).key] = value60]
                                                 /\ Assert((((req[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber), 
                                                           "Failure of assertion at line 741, column 13.")
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
                      /\ UNCHANGED << fd, primary, putInput, putOutput, 
                                      getInput, getOutput, req, idx, repReq, 
                                      repResp, replicaSet, replica, req0, 
                                      resp0, body, replica0, output, req1, 
                                      resp1, body0, replica1 >>

handlePrimary(self) == /\ pc[self] = "handlePrimary"
                       /\ Assert(((req[self]).srcTyp) = (CLIENT_SRC), 
                                 "Failure of assertion at line 819, column 7.")
                       /\ IF ((req[self]).typ) = (GET_REQ)
                             THEN /\ LET yielded_fs00 == ((fs)[self])[((req[self]).body).key] IN
                                       /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs00]]
                                       /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                       /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                  /\ UNCHANGED << fs, idx, replicaSet, 
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
                                             /\ UNCHANGED << fs, respBody, 
                                                             respTyp, idx, 
                                                             replicaSet, 
                                                             lastPutBody >>
                       /\ UNCHANGED << network, fd, primary, putInput, 
                                       putOutput, getInput, getOutput, req, 
                                       repReq, repResp, resp, shouldSync, 
                                       replica, req0, resp0, body, replica0, 
                                       output, req1, resp1, body0, replica1 >>

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
                                                                               \/ /\ LET value111 == FALSE IN
                                                                                       LET network6 == [network5 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network5)[<<self, REQ_INDEX>>]).queue, enabled |-> value111]] IN
                                                                                         LET value120 == FALSE IN
                                                                                           /\ network' = [network5 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network5)[<<self, RESP_INDEX>>]).queue, enabled |-> value120]]
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
                                                                          \/ /\ LET value112 == FALSE IN
                                                                                  LET network7 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value112]] IN
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
                                                               \/ /\ LET value113 == FALSE IN
                                                                       LET network8 == [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value113]] IN
                                                                         LET value122 == FALSE IN
                                                                           /\ network' = [network8 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network8)[<<self, RESP_INDEX>>]).queue, enabled |-> value122]]
                                                                           /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                            /\ UNCHANGED network
                                                 /\ UNCHANGED repReq
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                      /\ UNCHANGED << network, idx, repReq >>
                           /\ UNCHANGED << fd, fs, primary, putInput, 
                                           putOutput, getInput, getOutput, req, 
                                           respBody, respTyp, repResp, resp, 
                                           replicaSet, shouldSync, lastPutBody, 
                                           replica, req0, resp0, body, 
                                           replica0, output, req1, resp1, 
                                           body0, replica1 >>

rcvReplicaRespLoop(self) == /\ pc[self] = "rcvReplicaRespLoop"
                            /\ IF (Cardinality(replicaSet[self])) > (0)
                                  THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                       "Failure of assertion at line 920, column 11.")
                                             /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                             /\ LET readMsg20 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                  LET network9 == [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]] IN
                                                    LET yielded_network20 == readMsg20 IN
                                                      /\ repResp' = [repResp EXCEPT ![self] = yielded_network20]
                                                      /\ LET yielded_fd40 == (fd)[(repResp'[self]).from] IN
                                                           /\ Assert(((((((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd40)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).body) = (ACK_MSG_BODY))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (PUT_RESP))) /\ (((repResp'[self]).id) = ((req[self]).id)), 
                                                                     "Failure of assertion at line 927, column 19.")
                                                           /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({(repResp'[self]).from})]
                                                           /\ IF EXPLORE_FAIL
                                                                 THEN /\ \/ /\ TRUE
                                                                            /\ network' = network9
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                                         \/ /\ LET value130 == FALSE IN
                                                                                 LET network10 == [network9 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network9)[<<self, REQ_INDEX>>]).queue, enabled |-> value130]] IN
                                                                                   LET value140 == FALSE IN
                                                                                     /\ network' = [network9 EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> ((network9)[<<self, RESP_INDEX>>]).queue, enabled |-> value140]]
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
                            /\ UNCHANGED << fd, fs, primary, putInput, 
                                            putOutput, getInput, getOutput, 
                                            req, respBody, respTyp, idx, 
                                            repReq, resp, shouldSync, 
                                            lastPutBody, req0, resp0, body, 
                                            replica0, output, req1, resp1, 
                                            body0, replica1 >>

sndResp(self) == /\ pc[self] = "sndResp"
                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> PRIMARY_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                 /\ LET value150 == resp'[self] IN
                      /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                      /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value150), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                      /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                 /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                 getInput, getOutput, req, respBody, respTyp, 
                                 idx, repReq, repResp, replicaSet, shouldSync, 
                                 lastPutBody, replica, req0, resp0, body, 
                                 replica0, output, req1, resp1, body0, 
                                 replica1 >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value160 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value160]
                        /\ LET value170 == self IN
                             /\ primary' = (primary) \ ({value170})
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, fs, putInput, putOutput, getInput, 
                                   getOutput, req, respBody, respTyp, idx, 
                                   repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, req0, 
                                   resp0, body, replica0, output, req1, resp1, 
                                   body0, replica1 >>

Replica(self) == replicaLoop(self) \/ syncPrimary(self)
                    \/ sndSyncReqLoop(self) \/ rcvSyncRespLoop(self)
                    \/ rcvMsg(self) \/ handleBackup(self)
                    \/ handlePrimary(self) \/ sndReplicaReqLoop(self)
                    \/ rcvReplicaRespLoop(self) \/ sndResp(self)
                    \/ failLabel(self)

putClientLoop(self) == /\ pc[self] = "putClientLoop"
                       /\ IF PUT_CLIENT_RUN
                             THEN /\ body' = [body EXCEPT ![self] = putInput]
                                  /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ body' = body
                       /\ UNCHANGED << network, fd, fs, primary, putInput, 
                                       putOutput, getInput, getOutput, req, 
                                       respBody, respTyp, idx, repReq, repResp, 
                                       resp, replicaSet, shouldSync, 
                                       lastPutBody, replica, req0, resp0, 
                                       replica0, output, req1, resp1, body0, 
                                       replica1 >>

sndPutReq(self) == /\ pc[self] = "sndPutReq"
                   /\ IF (Cardinality(primary)) > (0)
                         THEN /\ LET yielded_primary50 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                   /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary50]
                                   /\ IF (replica0'[self]) # (NULL)
                                         THEN /\ \/ /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> body[self], srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1]]
                                                    /\ LET value180 == req0'[self] IN
                                                         /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value180), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvPutResp"]
                                                 \/ /\ LET yielded_fd60 == (fd)[replica0'[self]] IN
                                                         /\ yielded_fd60
                                                         /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                                                    /\ UNCHANGED <<network, req0>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req0 >>
                         ELSE /\ LET yielded_primary60 == NULL IN
                                   /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary60]
                                   /\ IF (replica0'[self]) # (NULL)
                                         THEN /\ \/ /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> body[self], srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1]]
                                                    /\ LET value181 == req0'[self] IN
                                                         /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value181), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvPutResp"]
                                                 \/ /\ LET yielded_fd61 == (fd)[replica0'[self]] IN
                                                         /\ yielded_fd61
                                                         /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                                                    /\ UNCHANGED <<network, req0>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req0 >>
                   /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                   getInput, getOutput, req, respBody, respTyp, 
                                   idx, repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, resp0, 
                                   body, output, req1, resp1, body0, replica1 >>

rcvPutResp(self) == /\ pc[self] = "rcvPutResp"
                    /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                    "Failure of assertion at line 1054, column 9.")
                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                          /\ LET readMsg30 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                               /\ LET yielded_network40 == readMsg30 IN
                                    /\ resp0' = [resp0 EXCEPT ![self] = yielded_network40]
                                    /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (1)), 
                                              "Failure of assertion at line 1060, column 13.")
                                    /\ output' = [output EXCEPT ![self] = resp0'[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "putClientLoop"]
                       \/ /\ LET yielded_fd70 == (fd)[replica0[self]] IN
                               LET yielded_network50 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                 /\ (yielded_fd70) /\ ((yielded_network50) = (0))
                                 /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                          /\ UNCHANGED <<network, resp0, output>>
                    /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                    getInput, getOutput, req, respBody, 
                                    respTyp, idx, repReq, repResp, resp, 
                                    replicaSet, shouldSync, lastPutBody, 
                                    replica, req0, body, replica0, req1, resp1, 
                                    body0, replica1 >>

PutClient(self) == putClientLoop(self) \/ sndPutReq(self)
                      \/ rcvPutResp(self)

getClientLoop(self) == /\ pc[self] = "getClientLoop"
                       /\ IF GET_CLIENT_RUN
                             THEN /\ body0' = [body0 EXCEPT ![self] = getInput]
                                  /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ body0' = body0
                       /\ UNCHANGED << network, fd, fs, primary, putInput, 
                                       putOutput, getInput, getOutput, req, 
                                       respBody, respTyp, idx, repReq, repResp, 
                                       resp, replicaSet, shouldSync, 
                                       lastPutBody, replica, req0, resp0, body, 
                                       replica0, output, req1, resp1, replica1 >>

sndGetReq(self) == /\ pc[self] = "sndGetReq"
                   /\ IF (Cardinality(primary)) > (0)
                         THEN /\ LET yielded_primary70 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                   /\ replica1' = [replica1 EXCEPT ![self] = yielded_primary70]
                                   /\ IF (replica1'[self]) # (NULL)
                                         THEN /\ \/ /\ req1' = [req1 EXCEPT ![self] = [from |-> self, to |-> replica1'[self], body |-> body0[self], srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2]]
                                                    /\ LET value190 == req1'[self] IN
                                                         /\ ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req1'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1'[self]).to, REQ_INDEX>>]).queue, value190), enabled |-> ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvGetResp"]
                                                 \/ /\ LET yielded_fd80 == (fd)[replica1'[self]] IN
                                                         /\ yielded_fd80
                                                         /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                                                    /\ UNCHANGED <<network, req1>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req1 >>
                         ELSE /\ LET yielded_primary80 == NULL IN
                                   /\ replica1' = [replica1 EXCEPT ![self] = yielded_primary80]
                                   /\ IF (replica1'[self]) # (NULL)
                                         THEN /\ \/ /\ req1' = [req1 EXCEPT ![self] = [from |-> self, to |-> replica1'[self], body |-> body0[self], srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2]]
                                                    /\ LET value191 == req1'[self] IN
                                                         /\ ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req1'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1'[self]).to, REQ_INDEX>>]).queue, value191), enabled |-> ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvGetResp"]
                                                 \/ /\ LET yielded_fd81 == (fd)[replica1'[self]] IN
                                                         /\ yielded_fd81
                                                         /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                                                    /\ UNCHANGED <<network, req1>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req1 >>
                   /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                   getInput, getOutput, req, respBody, respTyp, 
                                   idx, repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, req0, 
                                   resp0, body, replica0, output, resp1, body0 >>

rcvGetResp(self) == /\ pc[self] = "rcvGetResp"
                    /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                    "Failure of assertion at line 1131, column 9.")
                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                          /\ LET readMsg40 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                               /\ LET yielded_network60 == readMsg40 IN
                                    /\ resp1' = [resp1 EXCEPT ![self] = yielded_network60]
                                    /\ Assert(((((((resp1'[self]).to) = (self)) /\ (((resp1'[self]).from) = (replica1[self]))) /\ (((resp1'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp1'[self]).typ) = (GET_RESP))) /\ (((resp1'[self]).id) = (2)), 
                                              "Failure of assertion at line 1137, column 13.")
                                    /\ getOutput' = resp1'[self]
                                    /\ pc' = [pc EXCEPT ![self] = "getClientLoop"]
                       \/ /\ LET yielded_fd90 == (fd)[replica1[self]] IN
                               LET yielded_network70 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                 /\ (yielded_fd90) /\ ((yielded_network70) = (0))
                                 /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                          /\ UNCHANGED <<network, getOutput, resp1>>
                    /\ UNCHANGED << fd, fs, primary, putInput, putOutput, 
                                    getInput, req, respBody, respTyp, idx, 
                                    repReq, repResp, resp, replicaSet, 
                                    shouldSync, lastPutBody, replica, req0, 
                                    resp0, body, replica0, output, req1, body0, 
                                    replica1 >>

GetClient(self) == getClientLoop(self) \/ sndGetReq(self)
                      \/ rcvGetResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in REPLICA_SET: Replica(self))
           \/ (\E self \in PUT_CLIENT_SET: PutClient(self))
           \/ (\E self \in GET_CLIENT_SET: GetClient(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in REPLICA_SET : WF_vars(Replica(self))
        /\ \A self \in PUT_CLIENT_SET : WF_vars(PutClient(self))
        /\ \A self \in GET_CLIENT_SET : WF_vars(GetClient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Constraints

ReplicaVersionNumber(r) == lastPutBody[r].versionNumber < 2
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

ReceivePutResp(putClient) == pc[putClient] = "sndPutReq" ~> pc[putClient] = "rcvPutResp"
PutClientsOK == \A putClient \in PUT_CLIENT_SET : ReceivePutResp(putClient)

ReceiveGetResp(getClient) == pc[getClient] = "sndGetReq" ~> pc[getClient] = "rcvGetResp"
GetClientsOK == \A getClient \in GET_CLIENT_SET : ReceiveGetResp(getClient)

=============================================================================
\* Modification History
\* Last modified Wed Oct 20 13:55:55 PDT 2021 by shayan
\* Created Fri Sep 03 15:43:20 PDT 2021 by shayan
