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
response for its write request. The request might have applied or not.

We define consistency property for this system as:
    When primary node sends a response back to a client, all replicas (including 
    primary) have a same state.
********************)

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_REPLICAS
CONSTANT NUM_PUT_CLIENTS
CONSTANT NUM_GET_CLIENTS
CONSTANT EXPLORE_FAIL

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
                \* netEnabled[<<selfID, RESP_INDEX>>] := FALSE;
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
                yield CHOOSE x \in $variable: \A r \in $variable: x =< r;
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

    archetype AReplica(ref net[_], ref fs[_], ref fd[_], ref netEnabled[_], ref primary, ref netLen[_])
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
                shouldSync := TRUE;
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
                            fs[<<self, repResp.body.key>>] := repResp.body.value;
                            lastPutBody := repResp.body;
                            replicaSet := REPLICA_SET \ {self};
                            idx := 1;
                            goto sndSyncReqLoop;
                        } else {
                            replicaSet := replicaSet \ {repResp.from};
                        };
                    } or {
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
                respBody := [content |-> fs[<<self, req.body.key>>]];
                respTyp := GET_RESP;
            } else if (req.typ = PUT_REQ) {
                fs[<<self, req.body.key>>] := req.body.value;
                assert(req.body.versionNumber > lastPutBody.versionNumber);
                lastPutBody := req.body;
                respBody := ACK_MSG_BODY;
                respTyp := PUT_RESP;
                shouldSync := TRUE;
            } else if (req.typ = SYNC_REQ) {
                if (req.body.versionNumber > lastPutBody.versionNumber) {
                    fs[<<self, req.body.key>>] := req.body.value;
                    lastPutBody := req.body;
                };
                respBody := lastPutBody;
                respTyp := SYNC_RESP;
                shouldSync := TRUE;
            };
            resp := [from |-> self, to |-> req.from, body |-> respBody,
                     srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> req.id];
            net[<<resp.to, RESP_INDEX>>] := resp;
            goto replicaLoop;

        handlePrimary:
            assert(req.srcTyp = CLIENT_SRC);
            if (req.typ = GET_REQ) {
                respBody := [content |-> fs[<<self, req.body.key>>]];
                respTyp := GET_RESP;
                goto sndResp;
            } else if (req.typ = PUT_REQ) {
                fs[<<self, req.body.key>>] := req.body.value;
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

    archetype APutClient(ref net[_], ref fd[_], ref primary, ref netLen[_])
    variables
        req, resp, body, replica;
    {
    putClientLoop:
        while (TRUE) {

        sndPutReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    with (key \in KEY_SET, value \in VALUE_SET) {
                        body := [key |-> key, value |-> value];
                    };
                    req := [from |-> self, to |-> replica, body |-> body,
                            srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
                    net[<<req.to, REQ_INDEX>>] := req;
                } or {
                    await fd[replica];
                    goto sndPutReq;
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
                \* print <<"PUT RESP: ", resp>>;
            } or {
                await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                goto sndPutReq;
            };
        };
    }

    archetype AGetClient(ref net[_], ref fd[_], ref primary, ref netLen[_])
    variables
        req, resp, body, replica;
    {
    getClientLoop:
        while (TRUE) {

        sndGetReq:
            replica := primary;
            if (replica # NULL) {
                either {
                    body := [key |-> KEY1];
                    req := [from |-> self, to |-> replica, body |-> body,
                            srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
                    net[<<req.to, REQ_INDEX>>] := req;
                } or {
                    await fd[replica];
                    goto sndGetReq;
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
                \* print <<"GET RESP: ", resp>>;
            } or {
                await fd[replica] /\ netLen[<<self, RESP_INDEX>>] = 0;
                goto sndGetReq;
            };
        };
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]];
        fd = [id \in REPLICA_SET |-> FALSE];
        fs = [id \in REPLICA_SET, key \in KEY_SET |-> ""];
        primary = REPLICA_SET;

    fair process (Replica \in REPLICA_SET) == instance AReplica(ref network[_], ref fs[_], ref fd[_], ref network[_], ref primary, ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via FileSystem
        mapping @3[_] via PerfectFD
        mapping @4[_] via NetworkToggle
        mapping @5 via LeaderElection
        mapping @6[_] via NetworkBufferLength;

    fair process (PutClient \in PUT_CLIENT_SET) == instance APutClient(ref network[_], ref fd[_], ref primary, ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3 via LeaderElection
        mapping @4[_] via NetworkBufferLength;

    fair process (GetClient \in GET_CLIENT_SET) == instance AGetClient(ref network[_], ref fd[_], ref primary, ref network[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via PerfectFD
        mapping @3 via LeaderElection
        mapping @4[_] via NetworkBufferLength;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm pbkvs {
  variables network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [id \in REPLICA_SET |-> FALSE]; fs = [id \in REPLICA_SET, key \in KEY_SET |-> ""]; primary = REPLICA_SET;
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
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value00]];
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
            with (value17 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network0 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value17), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if(EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network0;
                    goto sndSyncReqLoop;
                  } or {
                    with (value20 = FALSE) {
                      network := [network0 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network0)[<<self, REQ_INDEX>>]).queue, enabled |-> value20]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network0;
                  goto sndSyncReqLoop;
                };
              };
            };
          } or {
            with (yielded_fd9 = (fd)[idx]) {
              await yielded_fd9;
              idx := (idx) + (1);
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndSyncReqLoop;
                } or {
                  with (value21 = FALSE) {
                    network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value21]];
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
          if(EXPLORE_FAIL) {
            either {
              skip;
              goto sndSyncReqLoop;
            } or {
              with (value22 = FALSE) {
                network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value22]];
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
      if((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg0 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
            with (yielded_network8 = readMsg0) {
              repResp := yielded_network8;
              with (yielded_fd00 = (fd)[(repResp).from]) {
                assert ((((((repResp).id) = (3)) /\ (((repResp).to) = (self))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (SYNC_RESP))) /\ ((((repResp).from) \in (replicaSet)) \/ (yielded_fd00));
                if((((repResp).body).versionNumber) > ((lastPutBody).versionNumber)) {
                  with (value30 = ((repResp).body).value) {
                    fs := [fs EXCEPT ![<<self, ((repResp).body).key>>] = value30];
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
          with (yielded_fd10 = (fd)[replica]) {
            with (yielded_network00 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
              await (yielded_fd10) /\ ((yielded_network00) = (0));
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
            with (readMsg1 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network10 = readMsg1) {
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
            with (readMsg2 = Head(((network)[<<self, REQ_INDEX>>]).queue)) {
              network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]];
              with (yielded_network11 = readMsg2) {
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
        with (yielded_fs1 = (fs)[<<self, ((req).body).key>>]) {
          respBody := [content |-> yielded_fs1];
          respTyp := GET_RESP;
          resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
          with (value60 = resp) {
            await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
            network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value60), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
            goto replicaLoop;
          };
        };
      } else {
        if(((req).typ) = (PUT_REQ)) {
          with (value40 = ((req).body).value) {
            fs := [fs EXCEPT ![<<self, ((req).body).key>>] = value40];
            assert (((req).body).versionNumber) > ((lastPutBody).versionNumber);
            lastPutBody := (req).body;
            respBody := ACK_MSG_BODY;
            respTyp := PUT_RESP;
            shouldSync := TRUE;
            resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
            with (value61 = resp) {
              await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
              network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value61), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
              goto replicaLoop;
            };
          };
        } else {
          if(((req).typ) = (SYNC_REQ)) {
            if((((req).body).versionNumber) > ((lastPutBody).versionNumber)) {
              with (value50 = ((req).body).value) {
                fs := [fs EXCEPT ![<<self, ((req).body).key>>] = value50];
                lastPutBody := (req).body;
                respBody := lastPutBody;
                respTyp := SYNC_RESP;
                shouldSync := TRUE;
                resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
                with (value62 = resp) {
                  await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value62), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                  goto replicaLoop;
                };
              };
            } else {
              respBody := lastPutBody;
              respTyp := SYNC_RESP;
              shouldSync := TRUE;
              resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
              with (value63 = resp) {
                await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value63), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
                goto replicaLoop;
              };
            };
          } else {
            resp := [from |-> self, to |-> (req).from, body |-> respBody, srcTyp |-> BACKUP_SRC, typ |-> respTyp, id |-> (req).id];
            with (value64 = resp) {
              await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
              network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value64), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
              goto replicaLoop;
            };
          };
        };
      };
    handlePrimary:
      assert ((req).srcTyp) = (CLIENT_SRC);
      if(((req).typ) = (GET_REQ)) {
        with (yielded_fs00 = (fs)[<<self, ((req).body).key>>]) {
          respBody := [content |-> yielded_fs00];
          respTyp := GET_RESP;
          goto sndResp;
        };
      } else {
        if(((req).typ) = (PUT_REQ)) {
          with (value70 = ((req).body).value) {
            fs := [fs EXCEPT ![<<self, ((req).body).key>>] = value70];
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
            with (value80 = repReq) {
              await ((network)[<<idx, REQ_INDEX>>]).enabled;
              with (network1 = [network EXCEPT ![<<idx, REQ_INDEX>>] = [queue |-> Append(((network)[<<idx, REQ_INDEX>>]).queue, value80), enabled |-> ((network)[<<idx, REQ_INDEX>>]).enabled]]) {
                idx := (idx) + (1);
                if(EXPLORE_FAIL) {
                  either {
                    skip;
                    network := network1;
                    goto sndReplicaReqLoop;
                  } or {
                    with (value90 = FALSE) {
                      network := [network1 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network1)[<<self, REQ_INDEX>>]).queue, enabled |-> value90]];
                      goto failLabel;
                    };
                  };
                } else {
                  network := network1;
                  goto sndReplicaReqLoop;
                };
              };
            };
          } or {
            with (yielded_fd20 = (fd)[idx]) {
              await yielded_fd20;
              idx := (idx) + (1);
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto sndReplicaReqLoop;
                } or {
                  with (value91 = FALSE) {
                    network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value91]];
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
          if(EXPLORE_FAIL) {
            either {
              skip;
              goto sndReplicaReqLoop;
            } or {
              with (value92 = FALSE) {
                network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value92]];
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
      if((Cardinality(replicaSet)) > (0)) {
        either {
          assert ((network)[<<self, RESP_INDEX>>]).enabled;
          await (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0);
          with (readMsg3 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
            with (network2 = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]) {
              with (yielded_network20 = readMsg3) {
                repResp := yielded_network20;
                with (yielded_fd30 = (fd)[(repResp).from]) {
                  assert ((((((((repResp).from) \in (replicaSet)) \/ (yielded_fd30)) /\ (((repResp).to) = (self))) /\ (((repResp).body) = (ACK_MSG_BODY))) /\ (((repResp).srcTyp) = (BACKUP_SRC))) /\ (((repResp).typ) = (PUT_RESP))) /\ (((repResp).id) = ((req).id));
                  replicaSet := (replicaSet) \ ({(repResp).from});
                  if(EXPLORE_FAIL) {
                    either {
                      skip;
                      network := network2;
                      goto rcvReplicaRespLoop;
                    } or {
                      with (value100 = FALSE) {
                        network := [network2 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network2)[<<self, REQ_INDEX>>]).queue, enabled |-> value100]];
                        goto failLabel;
                      };
                    };
                  } else {
                    network := network2;
                    goto rcvReplicaRespLoop;
                  };
                };
              };
            };
          };
        } or {
          replica := CHOOSE r \in replicaSet : TRUE;
          with (yielded_fd40 = (fd)[replica]) {
            with (yielded_network30 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
              await (yielded_fd40) /\ ((yielded_network30) = (0));
              replicaSet := (replicaSet) \ ({replica});
              if(EXPLORE_FAIL) {
                either {
                  skip;
                  goto rcvReplicaRespLoop;
                } or {
                  with (value101 = FALSE) {
                    network := [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value101]];
                    goto failLabel;
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
      with (value110 = resp) {
        await ((network)[<<(resp).to, RESP_INDEX>>]).enabled;
        network := [network EXCEPT ![<<(resp).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp).to, RESP_INDEX>>]).queue, value110), enabled |-> ((network)[<<(resp).to, RESP_INDEX>>]).enabled]];
        goto replicaLoop;
      };
    failLabel:
      with (value120 = TRUE) {
        fd := [fd EXCEPT ![self] = value120];
        with (value130 = self) {
          primary := (primary) \ ({value130});
          goto Done;
        };
      };
  }
  
  fair process (PutClient \in PUT_CLIENT_SET)
    variables req0; resp0; body; replica0;
  {
    putClientLoop:
      if(TRUE) {
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
              with (key1 \in KEY_SET, value18 \in VALUE_SET) {
                body := [key |-> key1, value |-> value18];
                req0 := [from |-> self, to |-> replica0, body |-> body, srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
                with (value140 = req0) {
                  await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value140), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                  goto rcvPutResp;
                };
              };
            } or {
              with (yielded_fd50 = (fd)[replica0]) {
                await yielded_fd50;
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
              with (key2 \in KEY_SET, value19 \in VALUE_SET) {
                body := [key |-> key2, value |-> value19];
                req0 := [from |-> self, to |-> replica0, body |-> body, srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1];
                with (value141 = req0) {
                  await ((network)[<<(req0).to, REQ_INDEX>>]).enabled;
                  network := [network EXCEPT ![<<(req0).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0).to, REQ_INDEX>>]).queue, value141), enabled |-> ((network)[<<(req0).to, REQ_INDEX>>]).enabled]];
                  goto rcvPutResp;
                };
              };
            } or {
              with (yielded_fd51 = (fd)[replica0]) {
                await yielded_fd51;
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
        with (readMsg4 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
          network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
          with (yielded_network40 = readMsg4) {
            resp0 := yielded_network40;
            assert (((((((resp0).to) = (self)) /\ (((resp0).from) = (replica0))) /\ (((resp0).body) = (ACK_MSG_BODY))) /\ (((resp0).srcTyp) = (PRIMARY_SRC))) /\ (((resp0).typ) = (PUT_RESP))) /\ (((resp0).id) = (1));
            goto putClientLoop;
          };
        };
      } or {
        with (yielded_fd60 = (fd)[replica0]) {
          with (yielded_network50 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
            await (yielded_fd60) /\ ((yielded_network50) = (0));
            goto sndPutReq;
          };
        };
      };
  }
  
  fair process (GetClient \in GET_CLIENT_SET)
    variables req1; resp1; body0; replica1;
  {
    getClientLoop:
      if(TRUE) {
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
              body0 := [key |-> KEY1];
              req1 := [from |-> self, to |-> replica1, body |-> body0, srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
              with (value150 = req1) {
                await ((network)[<<(req1).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req1).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1).to, REQ_INDEX>>]).queue, value150), enabled |-> ((network)[<<(req1).to, REQ_INDEX>>]).enabled]];
                goto rcvGetResp;
              };
            } or {
              with (yielded_fd70 = (fd)[replica1]) {
                await yielded_fd70;
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
              body0 := [key |-> KEY1];
              req1 := [from |-> self, to |-> replica1, body |-> body0, srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2];
              with (value151 = req1) {
                await ((network)[<<(req1).to, REQ_INDEX>>]).enabled;
                network := [network EXCEPT ![<<(req1).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1).to, REQ_INDEX>>]).queue, value151), enabled |-> ((network)[<<(req1).to, REQ_INDEX>>]).enabled]];
                goto rcvGetResp;
              };
            } or {
              with (yielded_fd71 = (fd)[replica1]) {
                await yielded_fd71;
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
        with (readMsg5 = Head(((network)[<<self, RESP_INDEX>>]).queue)) {
          network := [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]];
          with (yielded_network60 = readMsg5) {
            resp1 := yielded_network60;
            assert ((((((resp1).to) = (self)) /\ (((resp1).from) = (replica1))) /\ (((resp1).srcTyp) = (PRIMARY_SRC))) /\ (((resp1).typ) = (GET_RESP))) /\ (((resp1).id) = (2));
            goto getClientLoop;
          };
        };
      } or {
        with (yielded_fd80 = (fd)[replica1]) {
          with (yielded_network70 = Len(((network)[<<self, RESP_INDEX>>]).queue)) {
            await (yielded_fd80) /\ ((yielded_network70) = (0));
            goto sndGetReq;
          };
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "d83ab16b" /\ chksum(tla) = "93dc9f05")
CONSTANT defaultInitValue
VARIABLES network, fd, fs, primary, pc

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
          shouldSync, lastPutBody, replica, req0, resp0, body, replica0, req1, 
          resp1, body0, replica1

vars == << network, fd, fs, primary, pc, req, respBody, respTyp, idx, repReq, 
           repResp, resp, replicaSet, shouldSync, lastPutBody, replica, req0, 
           resp0, body, replica0, req1, resp1, body0, replica1 >>

ProcSet == (REPLICA_SET) \cup (PUT_CLIENT_SET) \cup (GET_CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_INDEX_SET |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [id \in REPLICA_SET |-> FALSE]
        /\ fs = [id \in REPLICA_SET, key \in KEY_SET |-> ""]
        /\ primary = REPLICA_SET
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
                                                      /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value00]]
                                                      /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                           /\ UNCHANGED network
                           ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                /\ UNCHANGED << network, idx, replicaSet >>
                     /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, 
                                     repReq, repResp, resp, shouldSync, 
                                     lastPutBody, replica, req0, resp0, body, 
                                     replica0, req1, resp1, body0, replica1 >>

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
                     /\ UNCHANGED << network, fd, fs, primary, req, respBody, 
                                     respTyp, idx, repReq, repResp, resp, 
                                     replicaSet, lastPutBody, replica, req0, 
                                     resp0, body, replica0, req1, resp1, body0, 
                                     replica1 >>

sndSyncReqLoop(self) == /\ pc[self] = "sndSyncReqLoop"
                        /\ IF (idx[self]) <= (NUM_REPLICAS)
                              THEN /\ IF (idx[self]) # (self)
                                         THEN /\ \/ /\ repReq' = [repReq EXCEPT ![self] = [from |-> self, to |-> idx[self], body |-> lastPutBody[self], srcTyp |-> PRIMARY_SRC, typ |-> SYNC_REQ, id |-> 3]]
                                                    /\ LET value17 == repReq'[self] IN
                                                         /\ ((network)[<<idx[self], REQ_INDEX>>]).enabled
                                                         /\ LET network0 == [network EXCEPT ![<<idx[self], REQ_INDEX>>] = [queue |-> Append(((network)[<<idx[self], REQ_INDEX>>]).queue, value17), enabled |-> ((network)[<<idx[self], REQ_INDEX>>]).enabled]] IN
                                                              /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                              /\ IF EXPLORE_FAIL
                                                                    THEN /\ \/ /\ TRUE
                                                                               /\ network' = network0
                                                                               /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                            \/ /\ LET value20 == FALSE IN
                                                                                    /\ network' = [network0 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network0)[<<self, REQ_INDEX>>]).queue, enabled |-> value20]]
                                                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                    ELSE /\ network' = network0
                                                                         /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                 \/ /\ LET yielded_fd9 == (fd)[idx[self]] IN
                                                         /\ yielded_fd9
                                                         /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                         /\ IF EXPLORE_FAIL
                                                               THEN /\ \/ /\ TRUE
                                                                          /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                          /\ UNCHANGED network
                                                                       \/ /\ LET value21 == FALSE IN
                                                                               /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value21]]
                                                                               /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                                    /\ UNCHANGED network
                                                    /\ UNCHANGED repReq
                                         ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                              /\ IF EXPLORE_FAIL
                                                    THEN /\ \/ /\ TRUE
                                                               /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                               /\ UNCHANGED network
                                                            \/ /\ LET value22 == FALSE IN
                                                                    /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value22]]
                                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "sndSyncReqLoop"]
                                                         /\ UNCHANGED network
                                              /\ UNCHANGED repReq
                              ELSE /\ pc' = [pc EXCEPT ![self] = "rcvSyncRespLoop"]
                                   /\ UNCHANGED << network, idx, repReq >>
                        /\ UNCHANGED << fd, fs, primary, req, respBody, 
                                        respTyp, repResp, resp, replicaSet, 
                                        shouldSync, lastPutBody, replica, req0, 
                                        resp0, body, replica0, req1, resp1, 
                                        body0, replica1 >>

rcvSyncRespLoop(self) == /\ pc[self] = "rcvSyncRespLoop"
                         /\ IF (Cardinality(replicaSet[self])) > (0)
                               THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                    "Failure of assertion at line 562, column 11.")
                                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                          /\ LET readMsg0 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                                               /\ LET yielded_network8 == readMsg0 IN
                                                    /\ repResp' = [repResp EXCEPT ![self] = yielded_network8]
                                                    /\ LET yielded_fd00 == (fd)[(repResp'[self]).from] IN
                                                         /\ Assert(((((((repResp'[self]).id) = (3)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (SYNC_RESP))) /\ ((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd00)), 
                                                                   "Failure of assertion at line 569, column 17.")
                                                         /\ IF (((repResp'[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber)
                                                               THEN /\ LET value30 == ((repResp'[self]).body).value IN
                                                                         /\ fs' = [fs EXCEPT ![<<self, ((repResp'[self]).body).key>>] = value30]
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
                         /\ UNCHANGED << fd, primary, req, respBody, respTyp, 
                                         repReq, resp, shouldSync, req0, resp0, 
                                         body, replica0, req1, resp1, body0, 
                                         replica1 >>

rcvMsg(self) == /\ pc[self] = "rcvMsg"
                /\ IF (Cardinality(primary)) > (0)
                      THEN /\ LET yielded_primary3 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                IF ((yielded_primary3) = (self)) /\ (shouldSync[self])
                                   THEN /\ pc' = [pc EXCEPT ![self] = "syncPrimary"]
                                        /\ UNCHANGED << network, req >>
                                   ELSE /\ Assert(((network)[<<self, REQ_INDEX>>]).enabled, 
                                                  "Failure of assertion at line 604, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg1 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network10 == readMsg1 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network10]
                                                  /\ Assert(((req'[self]).to) = (self), 
                                                            "Failure of assertion at line 610, column 17.")
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
                                                  "Failure of assertion at line 637, column 13.")
                                        /\ (Len(((network)[<<self, REQ_INDEX>>]).queue)) > (0)
                                        /\ LET readMsg2 == Head(((network)[<<self, REQ_INDEX>>]).queue) IN
                                             /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> Tail(((network)[<<self, REQ_INDEX>>]).queue), enabled |-> ((network)[<<self, REQ_INDEX>>]).enabled]]
                                             /\ LET yielded_network11 == readMsg2 IN
                                                  /\ req' = [req EXCEPT ![self] = yielded_network11]
                                                  /\ Assert(((req'[self]).to) = (self), 
                                                            "Failure of assertion at line 643, column 17.")
                                                  /\ IF (Cardinality(primary)) > (0)
                                                        THEN /\ LET yielded_primary1 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                                                  IF ((yielded_primary1) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                                                        ELSE /\ LET yielded_primary2 == NULL IN
                                                                  IF ((yielded_primary2) = (self)) /\ (((req'[self]).srcTyp) = (CLIENT_SRC))
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "handlePrimary"]
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "handleBackup"]
                /\ UNCHANGED << fd, fs, primary, respBody, respTyp, idx, 
                                repReq, repResp, resp, replicaSet, shouldSync, 
                                lastPutBody, replica, req0, resp0, body, 
                                replica0, req1, resp1, body0, replica1 >>

handleBackup(self) == /\ pc[self] = "handleBackup"
                      /\ Assert(((req[self]).srcTyp) = (PRIMARY_SRC), 
                                "Failure of assertion at line 667, column 7.")
                      /\ IF ((req[self]).typ) = (GET_REQ)
                            THEN /\ LET yielded_fs1 == (fs)[<<self, ((req[self]).body).key>>] IN
                                      /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs1]]
                                      /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                      /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                      /\ LET value60 == resp'[self] IN
                                           /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                           /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value60), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                           /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                 /\ UNCHANGED << fs, shouldSync, lastPutBody >>
                            ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                       THEN /\ LET value40 == ((req[self]).body).value IN
                                                 /\ fs' = [fs EXCEPT ![<<self, ((req[self]).body).key>>] = value40]
                                                 /\ Assert((((req[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber), 
                                                           "Failure of assertion at line 683, column 13.")
                                                 /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                 /\ respBody' = [respBody EXCEPT ![self] = ACK_MSG_BODY]
                                                 /\ respTyp' = [respTyp EXCEPT ![self] = PUT_RESP]
                                                 /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                 /\ LET value61 == resp'[self] IN
                                                      /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                      /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value61), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                      /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                       ELSE /\ IF ((req[self]).typ) = (SYNC_REQ)
                                                  THEN /\ IF (((req[self]).body).versionNumber) > ((lastPutBody[self]).versionNumber)
                                                             THEN /\ LET value50 == ((req[self]).body).value IN
                                                                       /\ fs' = [fs EXCEPT ![<<self, ((req[self]).body).key>>] = value50]
                                                                       /\ lastPutBody' = [lastPutBody EXCEPT ![self] = (req[self]).body]
                                                                       /\ respBody' = [respBody EXCEPT ![self] = lastPutBody'[self]]
                                                                       /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                       /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                       /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                       /\ LET value62 == resp'[self] IN
                                                                            /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                            /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value62), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                             ELSE /\ respBody' = [respBody EXCEPT ![self] = lastPutBody[self]]
                                                                  /\ respTyp' = [respTyp EXCEPT ![self] = SYNC_RESP]
                                                                  /\ shouldSync' = [shouldSync EXCEPT ![self] = TRUE]
                                                                  /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody'[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp'[self], id |-> (req[self]).id]]
                                                                  /\ LET value63 == resp'[self] IN
                                                                       /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                                       /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value63), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                                  /\ UNCHANGED << fs, 
                                                                                  lastPutBody >>
                                                  ELSE /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> BACKUP_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                                                       /\ LET value64 == resp'[self] IN
                                                            /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                                                            /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value64), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                                                            /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                                       /\ UNCHANGED << fs, 
                                                                       respBody, 
                                                                       respTyp, 
                                                                       shouldSync, 
                                                                       lastPutBody >>
                      /\ UNCHANGED << fd, primary, req, idx, repReq, repResp, 
                                      replicaSet, replica, req0, resp0, body, 
                                      replica0, req1, resp1, body0, replica1 >>

handlePrimary(self) == /\ pc[self] = "handlePrimary"
                       /\ Assert(((req[self]).srcTyp) = (CLIENT_SRC), 
                                 "Failure of assertion at line 733, column 7.")
                       /\ IF ((req[self]).typ) = (GET_REQ)
                             THEN /\ LET yielded_fs00 == (fs)[<<self, ((req[self]).body).key>>] IN
                                       /\ respBody' = [respBody EXCEPT ![self] = [content |-> yielded_fs00]]
                                       /\ respTyp' = [respTyp EXCEPT ![self] = GET_RESP]
                                       /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                  /\ UNCHANGED << fs, idx, replicaSet, 
                                                  lastPutBody >>
                             ELSE /\ IF ((req[self]).typ) = (PUT_REQ)
                                        THEN /\ LET value70 == ((req[self]).body).value IN
                                                  /\ fs' = [fs EXCEPT ![<<self, ((req[self]).body).key>>] = value70]
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
                       /\ UNCHANGED << network, fd, primary, req, repReq, 
                                       repResp, resp, shouldSync, replica, 
                                       req0, resp0, body, replica0, req1, 
                                       resp1, body0, replica1 >>

sndReplicaReqLoop(self) == /\ pc[self] = "sndReplicaReqLoop"
                           /\ IF (idx[self]) <= (NUM_REPLICAS)
                                 THEN /\ IF (idx[self]) # (self)
                                            THEN /\ \/ /\ repReq' = [repReq EXCEPT ![self] = [from |-> self, to |-> idx[self], body |-> lastPutBody[self], srcTyp |-> PRIMARY_SRC, typ |-> PUT_REQ, id |-> (req[self]).id]]
                                                       /\ LET value80 == repReq'[self] IN
                                                            /\ ((network)[<<idx[self], REQ_INDEX>>]).enabled
                                                            /\ LET network1 == [network EXCEPT ![<<idx[self], REQ_INDEX>>] = [queue |-> Append(((network)[<<idx[self], REQ_INDEX>>]).queue, value80), enabled |-> ((network)[<<idx[self], REQ_INDEX>>]).enabled]] IN
                                                                 /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                                 /\ IF EXPLORE_FAIL
                                                                       THEN /\ \/ /\ TRUE
                                                                                  /\ network' = network1
                                                                                  /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                               \/ /\ LET value90 == FALSE IN
                                                                                       /\ network' = [network1 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network1)[<<self, REQ_INDEX>>]).queue, enabled |-> value90]]
                                                                                       /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                       ELSE /\ network' = network1
                                                                            /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                    \/ /\ LET yielded_fd20 == (fd)[idx[self]] IN
                                                            /\ yielded_fd20
                                                            /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                            /\ IF EXPLORE_FAIL
                                                                  THEN /\ \/ /\ TRUE
                                                                             /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                             /\ UNCHANGED network
                                                                          \/ /\ LET value91 == FALSE IN
                                                                                  /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value91]]
                                                                                  /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                       /\ UNCHANGED network
                                                       /\ UNCHANGED repReq
                                            ELSE /\ idx' = [idx EXCEPT ![self] = (idx[self]) + (1)]
                                                 /\ IF EXPLORE_FAIL
                                                       THEN /\ \/ /\ TRUE
                                                                  /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                                  /\ UNCHANGED network
                                                               \/ /\ LET value92 == FALSE IN
                                                                       /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value92]]
                                                                       /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "sndReplicaReqLoop"]
                                                            /\ UNCHANGED network
                                                 /\ UNCHANGED repReq
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                      /\ UNCHANGED << network, idx, repReq >>
                           /\ UNCHANGED << fd, fs, primary, req, respBody, 
                                           respTyp, repResp, resp, replicaSet, 
                                           shouldSync, lastPutBody, replica, 
                                           req0, resp0, body, replica0, req1, 
                                           resp1, body0, replica1 >>

rcvReplicaRespLoop(self) == /\ pc[self] = "rcvReplicaRespLoop"
                            /\ IF (Cardinality(replicaSet[self])) > (0)
                                  THEN /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                                       "Failure of assertion at line 822, column 11.")
                                             /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                                             /\ LET readMsg3 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                  LET network2 == [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]] IN
                                                    LET yielded_network20 == readMsg3 IN
                                                      /\ repResp' = [repResp EXCEPT ![self] = yielded_network20]
                                                      /\ LET yielded_fd30 == (fd)[(repResp'[self]).from] IN
                                                           /\ Assert(((((((((repResp'[self]).from) \in (replicaSet[self])) \/ (yielded_fd30)) /\ (((repResp'[self]).to) = (self))) /\ (((repResp'[self]).body) = (ACK_MSG_BODY))) /\ (((repResp'[self]).srcTyp) = (BACKUP_SRC))) /\ (((repResp'[self]).typ) = (PUT_RESP))) /\ (((repResp'[self]).id) = ((req[self]).id)), 
                                                                     "Failure of assertion at line 829, column 19.")
                                                           /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({(repResp'[self]).from})]
                                                           /\ IF EXPLORE_FAIL
                                                                 THEN /\ \/ /\ TRUE
                                                                            /\ network' = network2
                                                                            /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                                         \/ /\ LET value100 == FALSE IN
                                                                                 /\ network' = [network2 EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network2)[<<self, REQ_INDEX>>]).queue, enabled |-> value100]]
                                                                                 /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                                 ELSE /\ network' = network2
                                                                      /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                             /\ UNCHANGED replica
                                          \/ /\ replica' = [replica EXCEPT ![self] = CHOOSE r \in replicaSet[self] : TRUE]
                                             /\ LET yielded_fd40 == (fd)[replica'[self]] IN
                                                  LET yielded_network30 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                                    /\ (yielded_fd40) /\ ((yielded_network30) = (0))
                                                    /\ replicaSet' = [replicaSet EXCEPT ![self] = (replicaSet[self]) \ ({replica'[self]})]
                                                    /\ IF EXPLORE_FAIL
                                                          THEN /\ \/ /\ TRUE
                                                                     /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                                     /\ UNCHANGED network
                                                                  \/ /\ LET value101 == FALSE IN
                                                                          /\ network' = [network EXCEPT ![<<self, REQ_INDEX>>] = [queue |-> ((network)[<<self, REQ_INDEX>>]).queue, enabled |-> value101]]
                                                                          /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "rcvReplicaRespLoop"]
                                                               /\ UNCHANGED network
                                             /\ UNCHANGED repResp
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "sndResp"]
                                       /\ UNCHANGED << network, repResp, 
                                                       replicaSet, replica >>
                            /\ UNCHANGED << fd, fs, primary, req, respBody, 
                                            respTyp, idx, repReq, resp, 
                                            shouldSync, lastPutBody, req0, 
                                            resp0, body, replica0, req1, resp1, 
                                            body0, replica1 >>

sndResp(self) == /\ pc[self] = "sndResp"
                 /\ resp' = [resp EXCEPT ![self] = [from |-> self, to |-> (req[self]).from, body |-> respBody[self], srcTyp |-> PRIMARY_SRC, typ |-> respTyp[self], id |-> (req[self]).id]]
                 /\ LET value110 == resp'[self] IN
                      /\ ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled
                      /\ network' = [network EXCEPT ![<<(resp'[self]).to, RESP_INDEX>>] = [queue |-> Append(((network)[<<(resp'[self]).to, RESP_INDEX>>]).queue, value110), enabled |-> ((network)[<<(resp'[self]).to, RESP_INDEX>>]).enabled]]
                      /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                 /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, idx, 
                                 repReq, repResp, replicaSet, shouldSync, 
                                 lastPutBody, replica, req0, resp0, body, 
                                 replica0, req1, resp1, body0, replica1 >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value120 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value120]
                        /\ LET value130 == self IN
                             /\ primary' = (primary) \ ({value130})
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, fs, req, respBody, respTyp, idx, 
                                   repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, req0, 
                                   resp0, body, replica0, req1, resp1, body0, 
                                   replica1 >>

Replica(self) == replicaLoop(self) \/ syncPrimary(self)
                    \/ sndSyncReqLoop(self) \/ rcvSyncRespLoop(self)
                    \/ rcvMsg(self) \/ handleBackup(self)
                    \/ handlePrimary(self) \/ sndReplicaReqLoop(self)
                    \/ rcvReplicaRespLoop(self) \/ sndResp(self)
                    \/ failLabel(self)

putClientLoop(self) == /\ pc[self] = "putClientLoop"
                       /\ IF TRUE
                             THEN /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << network, fd, fs, primary, req, respBody, 
                                       respTyp, idx, repReq, repResp, resp, 
                                       replicaSet, shouldSync, lastPutBody, 
                                       replica, req0, resp0, body, replica0, 
                                       req1, resp1, body0, replica1 >>

sndPutReq(self) == /\ pc[self] = "sndPutReq"
                   /\ IF (Cardinality(primary)) > (0)
                         THEN /\ LET yielded_primary50 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                   /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary50]
                                   /\ IF (replica0'[self]) # (NULL)
                                         THEN /\ \/ /\ \E key1 \in KEY_SET:
                                                         \E value18 \in VALUE_SET:
                                                           /\ body' = [body EXCEPT ![self] = [key |-> key1, value |-> value18]]
                                                           /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> body'[self], srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1]]
                                                           /\ LET value140 == req0'[self] IN
                                                                /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                                /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value140), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                                /\ pc' = [pc EXCEPT ![self] = "rcvPutResp"]
                                                 \/ /\ LET yielded_fd50 == (fd)[replica0'[self]] IN
                                                         /\ yielded_fd50
                                                         /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                                                    /\ UNCHANGED <<network, req0, body>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req0, 
                                                              body >>
                         ELSE /\ LET yielded_primary60 == NULL IN
                                   /\ replica0' = [replica0 EXCEPT ![self] = yielded_primary60]
                                   /\ IF (replica0'[self]) # (NULL)
                                         THEN /\ \/ /\ \E key2 \in KEY_SET:
                                                         \E value19 \in VALUE_SET:
                                                           /\ body' = [body EXCEPT ![self] = [key |-> key2, value |-> value19]]
                                                           /\ req0' = [req0 EXCEPT ![self] = [from |-> self, to |-> replica0'[self], body |-> body'[self], srcTyp |-> CLIENT_SRC, typ |-> PUT_REQ, id |-> 1]]
                                                           /\ LET value141 == req0'[self] IN
                                                                /\ ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled
                                                                /\ network' = [network EXCEPT ![<<(req0'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req0'[self]).to, REQ_INDEX>>]).queue, value141), enabled |-> ((network)[<<(req0'[self]).to, REQ_INDEX>>]).enabled]]
                                                                /\ pc' = [pc EXCEPT ![self] = "rcvPutResp"]
                                                 \/ /\ LET yielded_fd51 == (fd)[replica0'[self]] IN
                                                         /\ yielded_fd51
                                                         /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                                                    /\ UNCHANGED <<network, req0, body>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req0, 
                                                              body >>
                   /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, 
                                   idx, repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, resp0, 
                                   req1, resp1, body0, replica1 >>

rcvPutResp(self) == /\ pc[self] = "rcvPutResp"
                    /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                    "Failure of assertion at line 953, column 9.")
                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                          /\ LET readMsg4 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                               /\ LET yielded_network40 == readMsg4 IN
                                    /\ resp0' = [resp0 EXCEPT ![self] = yielded_network40]
                                    /\ Assert((((((((resp0'[self]).to) = (self)) /\ (((resp0'[self]).from) = (replica0[self]))) /\ (((resp0'[self]).body) = (ACK_MSG_BODY))) /\ (((resp0'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp0'[self]).typ) = (PUT_RESP))) /\ (((resp0'[self]).id) = (1)), 
                                              "Failure of assertion at line 959, column 13.")
                                    /\ pc' = [pc EXCEPT ![self] = "putClientLoop"]
                       \/ /\ LET yielded_fd60 == (fd)[replica0[self]] IN
                               LET yielded_network50 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                 /\ (yielded_fd60) /\ ((yielded_network50) = (0))
                                 /\ pc' = [pc EXCEPT ![self] = "sndPutReq"]
                          /\ UNCHANGED <<network, resp0>>
                    /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, 
                                    idx, repReq, repResp, resp, replicaSet, 
                                    shouldSync, lastPutBody, replica, req0, 
                                    body, replica0, req1, resp1, body0, 
                                    replica1 >>

PutClient(self) == putClientLoop(self) \/ sndPutReq(self)
                      \/ rcvPutResp(self)

getClientLoop(self) == /\ pc[self] = "getClientLoop"
                       /\ IF TRUE
                             THEN /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << network, fd, fs, primary, req, respBody, 
                                       respTyp, idx, repReq, repResp, resp, 
                                       replicaSet, shouldSync, lastPutBody, 
                                       replica, req0, resp0, body, replica0, 
                                       req1, resp1, body0, replica1 >>

sndGetReq(self) == /\ pc[self] = "sndGetReq"
                   /\ IF (Cardinality(primary)) > (0)
                         THEN /\ LET yielded_primary70 == CHOOSE x \in primary : \A r \in primary : (x) <= (r) IN
                                   /\ replica1' = [replica1 EXCEPT ![self] = yielded_primary70]
                                   /\ IF (replica1'[self]) # (NULL)
                                         THEN /\ \/ /\ body0' = [body0 EXCEPT ![self] = [key |-> KEY1]]
                                                    /\ req1' = [req1 EXCEPT ![self] = [from |-> self, to |-> replica1'[self], body |-> body0'[self], srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2]]
                                                    /\ LET value150 == req1'[self] IN
                                                         /\ ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req1'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1'[self]).to, REQ_INDEX>>]).queue, value150), enabled |-> ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvGetResp"]
                                                 \/ /\ LET yielded_fd70 == (fd)[replica1'[self]] IN
                                                         /\ yielded_fd70
                                                         /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                                                    /\ UNCHANGED <<network, req1, body0>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req1, 
                                                              body0 >>
                         ELSE /\ LET yielded_primary80 == NULL IN
                                   /\ replica1' = [replica1 EXCEPT ![self] = yielded_primary80]
                                   /\ IF (replica1'[self]) # (NULL)
                                         THEN /\ \/ /\ body0' = [body0 EXCEPT ![self] = [key |-> KEY1]]
                                                    /\ req1' = [req1 EXCEPT ![self] = [from |-> self, to |-> replica1'[self], body |-> body0'[self], srcTyp |-> CLIENT_SRC, typ |-> GET_REQ, id |-> 2]]
                                                    /\ LET value151 == req1'[self] IN
                                                         /\ ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled
                                                         /\ network' = [network EXCEPT ![<<(req1'[self]).to, REQ_INDEX>>] = [queue |-> Append(((network)[<<(req1'[self]).to, REQ_INDEX>>]).queue, value151), enabled |-> ((network)[<<(req1'[self]).to, REQ_INDEX>>]).enabled]]
                                                         /\ pc' = [pc EXCEPT ![self] = "rcvGetResp"]
                                                 \/ /\ LET yielded_fd71 == (fd)[replica1'[self]] IN
                                                         /\ yielded_fd71
                                                         /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                                                    /\ UNCHANGED <<network, req1, body0>>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, req1, 
                                                              body0 >>
                   /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, 
                                   idx, repReq, repResp, resp, replicaSet, 
                                   shouldSync, lastPutBody, replica, req0, 
                                   resp0, body, replica0, resp1 >>

rcvGetResp(self) == /\ pc[self] = "rcvGetResp"
                    /\ \/ /\ Assert(((network)[<<self, RESP_INDEX>>]).enabled, 
                                    "Failure of assertion at line 1030, column 9.")
                          /\ (Len(((network)[<<self, RESP_INDEX>>]).queue)) > (0)
                          /\ LET readMsg5 == Head(((network)[<<self, RESP_INDEX>>]).queue) IN
                               /\ network' = [network EXCEPT ![<<self, RESP_INDEX>>] = [queue |-> Tail(((network)[<<self, RESP_INDEX>>]).queue), enabled |-> ((network)[<<self, RESP_INDEX>>]).enabled]]
                               /\ LET yielded_network60 == readMsg5 IN
                                    /\ resp1' = [resp1 EXCEPT ![self] = yielded_network60]
                                    /\ Assert(((((((resp1'[self]).to) = (self)) /\ (((resp1'[self]).from) = (replica1[self]))) /\ (((resp1'[self]).srcTyp) = (PRIMARY_SRC))) /\ (((resp1'[self]).typ) = (GET_RESP))) /\ (((resp1'[self]).id) = (2)), 
                                              "Failure of assertion at line 1036, column 13.")
                                    /\ pc' = [pc EXCEPT ![self] = "getClientLoop"]
                       \/ /\ LET yielded_fd80 == (fd)[replica1[self]] IN
                               LET yielded_network70 == Len(((network)[<<self, RESP_INDEX>>]).queue) IN
                                 /\ (yielded_fd80) /\ ((yielded_network70) = (0))
                                 /\ pc' = [pc EXCEPT ![self] = "sndGetReq"]
                          /\ UNCHANGED <<network, resp1>>
                    /\ UNCHANGED << fd, fs, primary, req, respBody, respTyp, 
                                    idx, repReq, repResp, resp, replicaSet, 
                                    shouldSync, lastPutBody, replica, req0, 
                                    resp0, body, replica0, req1, body0, 
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
                    \A r \in AliveReplicas: \A key \in KEY_SET: fs[<<Primary, key>>] = fs[<<r, key>>]

\* Properties

ReceivePutResp(putClient) == pc[putClient] = "sndPutReq" ~> pc[putClient] = "rcvPutResp"
PutClientsOK == \A putClient \in PUT_CLIENT_SET : ReceivePutResp(putClient)

ReceiveGetResp(getClient) == pc[getClient] = "sndGetReq" ~> pc[getClient] = "rcvGetResp"
GetClientsOK == \A getClient \in GET_CLIENT_SET : ReceiveGetResp(getClient)

=============================================================================
\* Modification History
\* Last modified Sun Sep 19 10:21:35 PDT 2021 by shayan
\* Created Fri Sep 03 15:43:20 PDT 2021 by shayan
