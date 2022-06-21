-------------------------------- MODULE kv --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT Debug

CONSTANT NumServers
CONSTANT NumClients

CONSTANT BufferSize

\* This is only used for model checking / simulation
CONSTANT NumRequests

(********************

--mpcal kv {

    define {
        Nil == 0

        ProposeMessage == "prm"
        AcceptMessage  == "acm"

        ClientPutRequest  == "pq"
        ClientPutResponse == "pp"
        ClientGetRequest  == "gq"
        ClientGetResponse == "gp"

        Put == "p"
        Get == "g"

        ServerPropSet == (7*NumServers+1)..(8*NumServers)
        ServerAcctSet == (8*NumServers+1)..(9*NumServers)

        ServerSet == ServerPropSet
        ClientSet == (9*NumServers+1)..(9*NumServers+NumClients)
        NodeSet   == ServerSet \cup ClientSet 

        Key1   == "key1"
        Key2   == "key2"
        Value1 == "value1"
        KeySet == {}
    }

    macro debug(toPrint) {
        if (Debug) {
            print toPrint;
        };
    }

    macro Send(net, dest, fd, m) {
        either {
            net[dest] := m;
        } or {
            await fd[dest];
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
            await Len($variable.queue) < BufferSize;
            yield [queue |-> Append($variable.queue, $value), enabled |-> $variable.enabled];
        }
    }

    mapping macro PerfectFD {
        read {
            yield $variable;
        }

        write { yield $value; }
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

    mapping macro ProposeChan {
        read {
            assert FALSE;
        }

        write {
            yield [i \in ServerSet |-> Append($variable[i], $value)];
        }
    }

    mapping macro AcceptChan {
        read {
            await Len($variable) > 0;
            with (m = Head($variable)) {
                assert m.mtype = ProposeMessage;

                $variable := Tail($variable);
                yield [
                    mtype |-> AcceptMessage,
                    mcmd  |-> m.mcmd
                ];
            };
        }

        write {
            assert FALSE;
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

    archetype AServerProp(srvId, ref net[_], ref propCh) {
    serverPropLoop:
        while (TRUE) {
            with (msg = net[srvId]) {
                debug(<<"ServerPropose", srvId, msg>>);
                assert msg.mdest = srvId;

                propCh := [
                    mtype |-> ProposeMessage,
                    mcmd  |-> [
                        mmsg |-> msg,
                        msrv |-> srvId
                    ]
                ];
            };
        };
    }

    archetype AServerAcct(srvId, ref net[_], ref acctCh[_])
    variables m, sm = [k \in KeySet |-> Nil], smDomain = KeySet;
    {
    serverAccLoop:
        while (TRUE) {
            m := acctCh[srvId];
            debug(<<"ServerAccept", srvId, m>>);
            assert m.mtype = AcceptMessage;

            with (
                cmd = m.mcmd,
                msg = cmd.mmsg,
                srv = cmd.msrv
            ) {
                if (msg.mtype = ClientPutRequest) {
                    sm       := sm @@ (msg.mkey :> msg.mvalue);
                    smDomain := smDomain \cup {msg.mkey};
                };

                if (srv = srvId) {
                    with (
                        i = srvId,
                        j = msg.msource,
                        respType = IF msg.mtype = ClientPutRequest
                                   THEN ClientPutResponse
                                   ELSE ClientGetResponse,
                        respOk   = msg.mkey \in smDomain,
                        value    = IF respOk
                                   THEN sm[msg.mkey]
                                   ELSE Nil 
                    ) {
                        net[j] := [
                            mtype     |-> respType,
                            mresponse |-> [
                                idx   |-> msg.midx,
                                key   |-> msg.mkey,
                                value |-> value,
                                ok    |-> respOk
                            ],
                            msource   |-> i,
                            mdest     |-> j
                        ];
                    };
                };
            };
        };
    }

    archetype AClient(ref net[_], ref netLen[_], ref fd[_], ref reqCh, ref respCh, ref timeout)
    variable server = Nil, req, reqIdx = 0, resp;
    {
    clientLoop:
        while (TRUE) {
            req := reqCh;
            reqIdx := reqIdx + 1;

        sndReq:
            if (server = Nil) {
                with (s \in ServerSet) {
                    server := s;
                };
            };
            with (
                value = IF req.type = Put
                        THEN req.value
                        ELSE Nil,
                mtype = IF req.type = Put
                        THEN ClientPutRequest
                        ELSE ClientGetRequest
            ) {
                debug(<<"ClientSndReq", self, server, reqIdx, req>>);
                Send(net, server, fd, [
                    mtype   |-> mtype,
                    mkey    |-> req.key,
                    mvalue  |-> value,
                    midx    |-> reqIdx,
                    msource |-> self,
                    mdest   |-> server
                ]);
            };
        
        rcvResp:
            either {
                resp := net[self];
                debug(<<"ClientRcvResp", self, server, reqIdx, resp>>);
                assert resp.mdest = self;

                if (resp.mresponse.idx /= reqIdx) {
                    goto rcvResp;
                } else {
                    assert /\ req.type = Get => resp.mtype = ClientGetResponse
                           /\ req.type = Put => resp.mtype = ClientPutResponse
                           /\ resp.mresponse.idx = reqIdx
                           /\ resp.mresponse.key = req.key;

                    respCh := resp;
                    debug(<<"ClientRcvChDone", self, server, reqIdx, resp>>);
                };
            } or {
                await \/ /\ fd[server]
                         /\ netLen[self] = 0
                      \/ timeout;
                debug(<<"ClientTimeout", self, server, reqIdx>>);
                server := Nil;
                goto sndReq;
            };
        };
    }

    variables
        network = [i \in NodeSet |-> [queue |-> << >>, enabled |-> TRUE]];
        fd      = [i \in ServerSet |-> FALSE];

        rsm = [i \in ServerSet |-> <<>>];

        allReqs = <<
            [type |-> Put, key |-> Key1, value |-> Value1],
            [type |-> Get, key |-> Key2],
            [type |-> Get, key |-> Key1]
        >>;

        reqCh = SubSeq(allReqs, 1, NumRequests);
        respCh;

        acctSrvId = [i \in ServerAcctSet |-> i - NumServers];

    fair process (s0 \in ServerPropSet) == instance AServerProp(
        s0, ref network[_], ref rsm
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3    via ProposeChan;
    
    fair process (s1 \in ServerAcctSet) == instance AServerAcct(
        acctSrvId[s1], ref network[_], ref rsm[_]
    )
        mapping @2[_] via ReliableFIFOLink
        mapping @3[_] via AcceptChan;

    fair process (client \in ClientSet) == instance AClient(
        ref network[_], ref network[_], ref fd[_],
        ref reqCh, ref respCh, FALSE
    )
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via NetworkBufferLength
        mapping @3[_] via PerfectFD
        mapping @4    via Channel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm kv {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; rsm = [i \in ServerSet |-> <<>>]; allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>; reqCh = SubSeq(allReqs, 1, NumRequests); respCh; acctSrvId = [i \in ServerAcctSet |-> (i) - (NumServers)];
  define{
    Nil == 0
    ProposeMessage == "prm"
    AcceptMessage == "acm"
    ClientPutRequest == "pq"
    ClientPutResponse == "pp"
    ClientGetRequest == "gq"
    ClientGetResponse == "gp"
    Put == "p"
    Get == "g"
    ServerPropSet == (((7) * (NumServers)) + (1)) .. ((8) * (NumServers))
    ServerAcctSet == (((8) * (NumServers)) + (1)) .. ((9) * (NumServers))
    ServerSet == ServerPropSet
    ClientSet == (((9) * (NumServers)) + (1)) .. (((9) * (NumServers)) + (NumClients))
    NodeSet == (ServerSet) \union (ClientSet)
    Key1 == "key1"
    Key2 == "key2"
    Value1 == "value1"
    KeySet == {}
  }
  
  fair process (s0 \in ServerPropSet)
    variables srvId = self;
  {
    serverPropLoop:
      if (TRUE) {
        assert ((network)[srvId]).enabled;
        await (Len(((network)[srvId]).queue)) > (0);
        with (readMsg0 = Head(((network)[srvId]).queue)) {
          network := [network EXCEPT ![srvId] = [queue |-> Tail(((network)[srvId]).queue), enabled |-> ((network)[srvId]).enabled]];
          with (
            yielded_network = readMsg0, 
            msg = yielded_network
          ) {
            if (Debug) {
              print <<"ServerPropose", srvId, msg>>;
              assert ((msg).mdest) = (srvId);
              with (value00 = [mtype |-> ProposeMessage, mcmd |-> [mmsg |-> msg, msrv |-> srvId]]) {
                rsm := [i \in ServerSet |-> Append((rsm)[i], value00)];
                goto serverPropLoop;
              };
            } else {
              assert ((msg).mdest) = (srvId);
              with (value01 = [mtype |-> ProposeMessage, mcmd |-> [mmsg |-> msg, msrv |-> srvId]]) {
                rsm := [i \in ServerSet |-> Append((rsm)[i], value01)];
                goto serverPropLoop;
              };
            };
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (s1 \in ServerAcctSet)
    variables m; sm = [k \in KeySet |-> Nil]; smDomain = KeySet; srvId0 = (acctSrvId)[self];
  {
    serverAccLoop:
      if (TRUE) {
        await (Len((rsm)[srvId0])) > (0);
        with (m00 = Head((rsm)[srvId0])) {
          assert ((m00).mtype) = (ProposeMessage);
          rsm := [rsm EXCEPT ![srvId0] = Tail((rsm)[srvId0])];
          with (yielded_rsm0 = [mtype |-> AcceptMessage, mcmd |-> (m00).mcmd]) {
            m := yielded_rsm0;
            if (Debug) {
              print <<"ServerAccept", srvId0, m>>;
              assert ((m).mtype) = (AcceptMessage);
              with (
                cmd = (m).mcmd, 
                msg = (cmd).mmsg, 
                srv = (cmd).msrv
              ) {
                if (((msg).mtype) = (ClientPutRequest)) {
                  sm := (sm) @@ (((msg).mkey) :> ((msg).mvalue));
                  smDomain := (smDomain) \union ({(msg).mkey});
                  if ((srv) = (srvId0)) {
                    with (
                      i = srvId0, 
                      j = (msg).msource, 
                      respType = IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse, 
                      respOk = ((msg).mkey) \in (smDomain), 
                      value = IF respOk THEN (sm)[(msg).mkey] ELSE Nil, 
                      value10 = [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]];
                      goto serverAccLoop;
                    };
                  } else {
                    goto serverAccLoop;
                  };
                } else {
                  if ((srv) = (srvId0)) {
                    with (
                      i = srvId0, 
                      j = (msg).msource, 
                      respType = IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse, 
                      respOk = ((msg).mkey) \in (smDomain), 
                      value = IF respOk THEN (sm)[(msg).mkey] ELSE Nil, 
                      value11 = [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]];
                      goto serverAccLoop;
                    };
                  } else {
                    goto serverAccLoop;
                  };
                };
              };
            } else {
              assert ((m).mtype) = (AcceptMessage);
              with (
                cmd = (m).mcmd, 
                msg = (cmd).mmsg, 
                srv = (cmd).msrv
              ) {
                if (((msg).mtype) = (ClientPutRequest)) {
                  sm := (sm) @@ (((msg).mkey) :> ((msg).mvalue));
                  smDomain := (smDomain) \union ({(msg).mkey});
                  if ((srv) = (srvId0)) {
                    with (
                      i = srvId0, 
                      j = (msg).msource, 
                      respType = IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse, 
                      respOk = ((msg).mkey) \in (smDomain), 
                      value = IF respOk THEN (sm)[(msg).mkey] ELSE Nil, 
                      value12 = [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]];
                      goto serverAccLoop;
                    };
                  } else {
                    goto serverAccLoop;
                  };
                } else {
                  if ((srv) = (srvId0)) {
                    with (
                      i = srvId0, 
                      j = (msg).msource, 
                      respType = IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse, 
                      respOk = ((msg).mkey) \in (smDomain), 
                      value = IF respOk THEN (sm)[(msg).mkey] ELSE Nil, 
                      value13 = [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                    ) {
                      await ((network)[j]).enabled;
                      await (Len(((network)[j]).queue)) < (BufferSize);
                      network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]];
                      goto serverAccLoop;
                    };
                  } else {
                    goto serverAccLoop;
                  };
                };
              };
            };
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (client \in ClientSet)
    variables server = Nil; req; reqIdx = 0; resp; timeout = FALSE;
  {
    clientLoop:
      if (TRUE) {
        await (Len(reqCh)) > (0);
        with (res00 = Head(reqCh)) {
          reqCh := Tail(reqCh);
          with (yielded_reqCh0 = res00) {
            req := yielded_reqCh0;
            reqIdx := (reqIdx) + (1);
            goto sndReq;
          };
        };
      } else {
        goto Done;
      };
    sndReq:
      if ((server) = (Nil)) {
        with (s3 \in ServerSet) {
          server := s3;
          with (
            value = IF ((req).type) = (Put) THEN (req).value ELSE Nil, 
            mtype = IF ((req).type) = (Put) THEN ClientPutRequest ELSE ClientGetRequest
          ) {
            if (Debug) {
              print <<"ClientSndReq", self, server, reqIdx, req>>;
              either {
                with (value20 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
                  await ((network)[server]).enabled;
                  await (Len(((network)[server]).queue)) < (BufferSize);
                  network := [network EXCEPT ![server] = [queue |-> Append(((network)[server]).queue, value20), enabled |-> ((network)[server]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd1 = (fd)[server]) {
                  await yielded_fd1;
                  goto rcvResp;
                };
              };
            } else {
              either {
                with (value21 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
                  await ((network)[server]).enabled;
                  await (Len(((network)[server]).queue)) < (BufferSize);
                  network := [network EXCEPT ![server] = [queue |-> Append(((network)[server]).queue, value21), enabled |-> ((network)[server]).enabled]];
                  goto rcvResp;
                };
              } or {
                with (yielded_fd2 = (fd)[server]) {
                  await yielded_fd2;
                  goto rcvResp;
                };
              };
            };
          };
        };
      } else {
        with (
          value = IF ((req).type) = (Put) THEN (req).value ELSE Nil, 
          mtype = IF ((req).type) = (Put) THEN ClientPutRequest ELSE ClientGetRequest
        ) {
          if (Debug) {
            print <<"ClientSndReq", self, server, reqIdx, req>>;
            either {
              with (value22 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
                await ((network)[server]).enabled;
                await (Len(((network)[server]).queue)) < (BufferSize);
                network := [network EXCEPT ![server] = [queue |-> Append(((network)[server]).queue, value22), enabled |-> ((network)[server]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd3 = (fd)[server]) {
                await yielded_fd3;
                goto rcvResp;
              };
            };
          } else {
            either {
              with (value23 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
                await ((network)[server]).enabled;
                await (Len(((network)[server]).queue)) < (BufferSize);
                network := [network EXCEPT ![server] = [queue |-> Append(((network)[server]).queue, value23), enabled |-> ((network)[server]).enabled]];
                goto rcvResp;
              };
            } or {
              with (yielded_fd4 = (fd)[server]) {
                await yielded_fd4;
                goto rcvResp;
              };
            };
          };
        };
      };
    rcvResp:
      either {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg10 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network00 = readMsg10) {
            resp := yielded_network00;
            if (Debug) {
              print <<"ClientRcvResp", self, server, reqIdx, resp>>;
              assert ((resp).mdest) = (self);
              if ((((resp).mresponse).idx) # (reqIdx)) {
                goto rcvResp;
              } else {
                assert ((((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))) /\ ((((resp).mresponse).idx) = (reqIdx))) /\ ((((resp).mresponse).key) = ((req).key));
                respCh := resp;
                if (Debug) {
                  print <<"ClientRcvChDone", self, server, reqIdx, resp>>;
                  goto clientLoop;
                } else {
                  goto clientLoop;
                };
              };
            } else {
              assert ((resp).mdest) = (self);
              if ((((resp).mresponse).idx) # (reqIdx)) {
                goto rcvResp;
              } else {
                assert ((((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))) /\ ((((resp).mresponse).idx) = (reqIdx))) /\ ((((resp).mresponse).key) = ((req).key));
                respCh := resp;
                if (Debug) {
                  print <<"ClientRcvChDone", self, server, reqIdx, resp>>;
                  goto clientLoop;
                } else {
                  goto clientLoop;
                };
              };
            };
          };
        };
      } or {
        with (
          yielded_fd00 = (fd)[server], 
          yielded_network10 = Len(((network)[self]).queue)
        ) {
          await ((yielded_fd00) /\ ((yielded_network10) = (0))) \/ (timeout);
          if (Debug) {
            print <<"ClientTimeout", self, server, reqIdx>>;
            server := Nil;
            goto sndReq;
          } else {
            server := Nil;
            goto sndReq;
          };
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "ccaf264c" /\ chksum(tla) = "63f4dec8")
CONSTANT defaultInitValue
VARIABLES network, fd, rsm, allReqs, reqCh, respCh, acctSrvId, pc

(* define statement *)
Nil == 0
ProposeMessage == "prm"
AcceptMessage == "acm"
ClientPutRequest == "pq"
ClientPutResponse == "pp"
ClientGetRequest == "gq"
ClientGetResponse == "gp"
Put == "p"
Get == "g"
ServerPropSet == (((7) * (NumServers)) + (1)) .. ((8) * (NumServers))
ServerAcctSet == (((8) * (NumServers)) + (1)) .. ((9) * (NumServers))
ServerSet == ServerPropSet
ClientSet == (((9) * (NumServers)) + (1)) .. (((9) * (NumServers)) + (NumClients))
NodeSet == (ServerSet) \union (ClientSet)
Key1 == "key1"
Key2 == "key2"
Value1 == "value1"
KeySet == {}

VARIABLES srvId, m, sm, smDomain, srvId0, server, req, reqIdx, resp, timeout

vars == << network, fd, rsm, allReqs, reqCh, respCh, acctSrvId, pc, srvId, m, 
           sm, smDomain, srvId0, server, req, reqIdx, resp, timeout >>

ProcSet == (ServerPropSet) \cup (ServerAcctSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [i \in ServerSet |-> FALSE]
        /\ rsm = [i \in ServerSet |-> <<>>]
        /\ allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>
        /\ reqCh = SubSeq(allReqs, 1, NumRequests)
        /\ respCh = defaultInitValue
        /\ acctSrvId = [i \in ServerAcctSet |-> (i) - (NumServers)]
        (* Process s0 *)
        /\ srvId = [self \in ServerPropSet |-> self]
        (* Process s1 *)
        /\ m = [self \in ServerAcctSet |-> defaultInitValue]
        /\ sm = [self \in ServerAcctSet |-> [k \in KeySet |-> Nil]]
        /\ smDomain = [self \in ServerAcctSet |-> KeySet]
        /\ srvId0 = [self \in ServerAcctSet |-> (acctSrvId)[self]]
        (* Process client *)
        /\ server = [self \in ClientSet |-> Nil]
        /\ req = [self \in ClientSet |-> defaultInitValue]
        /\ reqIdx = [self \in ClientSet |-> 0]
        /\ resp = [self \in ClientSet |-> defaultInitValue]
        /\ timeout = [self \in ClientSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerPropSet -> "serverPropLoop"
                                        [] self \in ServerAcctSet -> "serverAccLoop"
                                        [] self \in ClientSet -> "clientLoop"]

serverPropLoop(self) == /\ pc[self] = "serverPropLoop"
                        /\ IF TRUE
                              THEN /\ Assert(((network)[srvId[self]]).enabled, 
                                             "Failure of assertion at line 334, column 9.")
                                   /\ (Len(((network)[srvId[self]]).queue)) > (0)
                                   /\ LET readMsg0 == Head(((network)[srvId[self]]).queue) IN
                                        /\ network' = [network EXCEPT ![srvId[self]] = [queue |-> Tail(((network)[srvId[self]]).queue), enabled |-> ((network)[srvId[self]]).enabled]]
                                        /\ LET yielded_network == readMsg0 IN
                                             LET msg == yielded_network IN
                                               IF Debug
                                                  THEN /\ PrintT(<<"ServerPropose", srvId[self], msg>>)
                                                       /\ Assert(((msg).mdest) = (srvId[self]), 
                                                                 "Failure of assertion at line 344, column 15.")
                                                       /\ LET value00 == [mtype |-> ProposeMessage, mcmd |-> [mmsg |-> msg, msrv |-> srvId[self]]] IN
                                                            /\ rsm' = [i \in ServerSet |-> Append((rsm)[i], value00)]
                                                            /\ pc' = [pc EXCEPT ![self] = "serverPropLoop"]
                                                  ELSE /\ Assert(((msg).mdest) = (srvId[self]), 
                                                                 "Failure of assertion at line 350, column 15.")
                                                       /\ LET value01 == [mtype |-> ProposeMessage, mcmd |-> [mmsg |-> msg, msrv |-> srvId[self]]] IN
                                                            /\ rsm' = [i \in ServerSet |-> Append((rsm)[i], value01)]
                                                            /\ pc' = [pc EXCEPT ![self] = "serverPropLoop"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << network, rsm >>
                        /\ UNCHANGED << fd, allReqs, reqCh, respCh, acctSrvId, 
                                        srvId, m, sm, smDomain, srvId0, server, 
                                        req, reqIdx, resp, timeout >>

s0(self) == serverPropLoop(self)

serverAccLoop(self) == /\ pc[self] = "serverAccLoop"
                       /\ IF TRUE
                             THEN /\ (Len((rsm)[srvId0[self]])) > (0)
                                  /\ LET m00 == Head((rsm)[srvId0[self]]) IN
                                       /\ Assert(((m00).mtype) = (ProposeMessage), 
                                                 "Failure of assertion at line 370, column 11.")
                                       /\ rsm' = [rsm EXCEPT ![srvId0[self]] = Tail((rsm)[srvId0[self]])]
                                       /\ LET yielded_rsm0 == [mtype |-> AcceptMessage, mcmd |-> (m00).mcmd] IN
                                            /\ m' = [m EXCEPT ![self] = yielded_rsm0]
                                            /\ IF Debug
                                                  THEN /\ PrintT(<<"ServerAccept", srvId0[self], m'[self]>>)
                                                       /\ Assert(((m'[self]).mtype) = (AcceptMessage), 
                                                                 "Failure of assertion at line 376, column 15.")
                                                       /\ LET cmd == (m'[self]).mcmd IN
                                                            LET msg == (cmd).mmsg IN
                                                              LET srv == (cmd).msrv IN
                                                                IF ((msg).mtype) = (ClientPutRequest)
                                                                   THEN /\ sm' = [sm EXCEPT ![self] = (sm[self]) @@ (((msg).mkey) :> ((msg).mvalue))]
                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (smDomain[self]) \union ({(msg).mkey})]
                                                                        /\ IF (srv) = (srvId0[self])
                                                                              THEN /\ LET i == srvId0[self] IN
                                                                                        LET j == (msg).msource IN
                                                                                          LET respType == IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                            LET respOk == ((msg).mkey) \in (smDomain'[self]) IN
                                                                                              LET value == IF respOk THEN (sm'[self])[(msg).mkey] ELSE Nil IN
                                                                                                LET value10 == [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                                                  /\ ((network)[j]).enabled
                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                                   /\ UNCHANGED network
                                                                   ELSE /\ IF (srv) = (srvId0[self])
                                                                              THEN /\ LET i == srvId0[self] IN
                                                                                        LET j == (msg).msource IN
                                                                                          LET respType == IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                            LET respOk == ((msg).mkey) \in (smDomain[self]) IN
                                                                                              LET value == IF respOk THEN (sm[self])[(msg).mkey] ELSE Nil IN
                                                                                                LET value11 == [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                                                  /\ ((network)[j]).enabled
                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                                   /\ UNCHANGED network
                                                                        /\ UNCHANGED << sm, 
                                                                                        smDomain >>
                                                  ELSE /\ Assert(((m'[self]).mtype) = (AcceptMessage), 
                                                                 "Failure of assertion at line 423, column 15.")
                                                       /\ LET cmd == (m'[self]).mcmd IN
                                                            LET msg == (cmd).mmsg IN
                                                              LET srv == (cmd).msrv IN
                                                                IF ((msg).mtype) = (ClientPutRequest)
                                                                   THEN /\ sm' = [sm EXCEPT ![self] = (sm[self]) @@ (((msg).mkey) :> ((msg).mvalue))]
                                                                        /\ smDomain' = [smDomain EXCEPT ![self] = (smDomain[self]) \union ({(msg).mkey})]
                                                                        /\ IF (srv) = (srvId0[self])
                                                                              THEN /\ LET i == srvId0[self] IN
                                                                                        LET j == (msg).msource IN
                                                                                          LET respType == IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                            LET respOk == ((msg).mkey) \in (smDomain'[self]) IN
                                                                                              LET value == IF respOk THEN (sm'[self])[(msg).mkey] ELSE Nil IN
                                                                                                LET value12 == [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                                                  /\ ((network)[j]).enabled
                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value12), enabled |-> ((network)[j]).enabled]]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                                   /\ UNCHANGED network
                                                                   ELSE /\ IF (srv) = (srvId0[self])
                                                                              THEN /\ LET i == srvId0[self] IN
                                                                                        LET j == (msg).msource IN
                                                                                          LET respType == IF ((msg).mtype) = (ClientPutRequest) THEN ClientPutResponse ELSE ClientGetResponse IN
                                                                                            LET respOk == ((msg).mkey) \in (smDomain[self]) IN
                                                                                              LET value == IF respOk THEN (sm[self])[(msg).mkey] ELSE Nil IN
                                                                                                LET value13 == [mtype |-> respType, mresponse |-> [idx |-> (msg).midx, key |-> (msg).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                                                  /\ ((network)[j]).enabled
                                                                                                  /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                                                  /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value13), enabled |-> ((network)[j]).enabled]]
                                                                                                  /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                                                   /\ UNCHANGED network
                                                                        /\ UNCHANGED << sm, 
                                                                                        smDomain >>
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << network, rsm, m, sm, 
                                                  smDomain >>
                       /\ UNCHANGED << fd, allReqs, reqCh, respCh, acctSrvId, 
                                       srvId, srvId0, server, req, reqIdx, 
                                       resp, timeout >>

s1(self) == serverAccLoop(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ (Len(reqCh)) > (0)
                               /\ LET res00 == Head(reqCh) IN
                                    /\ reqCh' = Tail(reqCh)
                                    /\ LET yielded_reqCh0 == res00 IN
                                         /\ req' = [req EXCEPT ![self] = yielded_reqCh0]
                                         /\ reqIdx' = [reqIdx EXCEPT ![self] = (reqIdx[self]) + (1)]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << reqCh, req, reqIdx >>
                    /\ UNCHANGED << network, fd, rsm, allReqs, respCh, 
                                    acctSrvId, srvId, m, sm, smDomain, srvId0, 
                                    server, resp, timeout >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (server[self]) = (Nil)
                      THEN /\ \E s3 \in ServerSet:
                                /\ server' = [server EXCEPT ![self] = s3]
                                /\ LET value == IF ((req[self]).type) = (Put) THEN (req[self]).value ELSE Nil IN
                                     LET mtype == IF ((req[self]).type) = (Put) THEN ClientPutRequest ELSE ClientGetRequest IN
                                       IF Debug
                                          THEN /\ PrintT(<<"ClientSndReq", self, server'[self], reqIdx[self], req[self]>>)
                                               /\ \/ /\ LET value20 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> value, midx |-> reqIdx[self], msource |-> self, mdest |-> server'[self]] IN
                                                          /\ ((network)[server'[self]]).enabled
                                                          /\ (Len(((network)[server'[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![server'[self]] = [queue |-> Append(((network)[server'[self]]).queue, value20), enabled |-> ((network)[server'[self]]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                  \/ /\ LET yielded_fd1 == (fd)[server'[self]] IN
                                                          /\ yielded_fd1
                                                          /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                     /\ UNCHANGED network
                                          ELSE /\ \/ /\ LET value21 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> value, midx |-> reqIdx[self], msource |-> self, mdest |-> server'[self]] IN
                                                          /\ ((network)[server'[self]]).enabled
                                                          /\ (Len(((network)[server'[self]]).queue)) < (BufferSize)
                                                          /\ network' = [network EXCEPT ![server'[self]] = [queue |-> Append(((network)[server'[self]]).queue, value21), enabled |-> ((network)[server'[self]]).enabled]]
                                                          /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                  \/ /\ LET yielded_fd2 == (fd)[server'[self]] IN
                                                          /\ yielded_fd2
                                                          /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                     /\ UNCHANGED network
                      ELSE /\ LET value == IF ((req[self]).type) = (Put) THEN (req[self]).value ELSE Nil IN
                                LET mtype == IF ((req[self]).type) = (Put) THEN ClientPutRequest ELSE ClientGetRequest IN
                                  IF Debug
                                     THEN /\ PrintT(<<"ClientSndReq", self, server[self], reqIdx[self], req[self]>>)
                                          /\ \/ /\ LET value22 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> value, midx |-> reqIdx[self], msource |-> self, mdest |-> server[self]] IN
                                                     /\ ((network)[server[self]]).enabled
                                                     /\ (Len(((network)[server[self]]).queue)) < (BufferSize)
                                                     /\ network' = [network EXCEPT ![server[self]] = [queue |-> Append(((network)[server[self]]).queue, value22), enabled |-> ((network)[server[self]]).enabled]]
                                                     /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                             \/ /\ LET yielded_fd3 == (fd)[server[self]] IN
                                                     /\ yielded_fd3
                                                     /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                /\ UNCHANGED network
                                     ELSE /\ \/ /\ LET value23 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> value, midx |-> reqIdx[self], msource |-> self, mdest |-> server[self]] IN
                                                     /\ ((network)[server[self]]).enabled
                                                     /\ (Len(((network)[server[self]]).queue)) < (BufferSize)
                                                     /\ network' = [network EXCEPT ![server[self]] = [queue |-> Append(((network)[server[self]]).queue, value23), enabled |-> ((network)[server[self]]).enabled]]
                                                     /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                             \/ /\ LET yielded_fd4 == (fd)[server[self]] IN
                                                     /\ yielded_fd4
                                                     /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                /\ UNCHANGED network
                           /\ UNCHANGED server
                /\ UNCHANGED << fd, rsm, allReqs, reqCh, respCh, acctSrvId, 
                                srvId, m, sm, smDomain, srvId0, req, reqIdx, 
                                resp, timeout >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 573, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg10 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network00 == readMsg10 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network00]
                                 /\ IF Debug
                                       THEN /\ PrintT(<<"ClientRcvResp", self, server[self], reqIdx[self], resp'[self]>>)
                                            /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 581, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED respCh
                                                  ELSE /\ Assert(((((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse)))) /\ ((((resp'[self]).mresponse).idx) = (reqIdx[self]))) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                 "Failure of assertion at line 585, column 17.")
                                                       /\ respCh' = resp'[self]
                                                       /\ IF Debug
                                                             THEN /\ PrintT(<<"ClientRcvChDone", self, server[self], reqIdx[self], resp'[self]>>)
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                       ELSE /\ Assert(((resp'[self]).mdest) = (self), 
                                                      "Failure of assertion at line 595, column 15.")
                                            /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                       /\ UNCHANGED respCh
                                                  ELSE /\ Assert(((((((req[self]).type) = (Get)) => (((resp'[self]).mtype) = (ClientGetResponse))) /\ ((((req[self]).type) = (Put)) => (((resp'[self]).mtype) = (ClientPutResponse)))) /\ ((((resp'[self]).mresponse).idx) = (reqIdx[self]))) /\ ((((resp'[self]).mresponse).key) = ((req[self]).key)), 
                                                                 "Failure of assertion at line 599, column 17.")
                                                       /\ respCh' = resp'[self]
                                                       /\ IF Debug
                                                             THEN /\ PrintT(<<"ClientRcvChDone", self, server[self], reqIdx[self], resp'[self]>>)
                                                                  /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                       /\ UNCHANGED server
                    \/ /\ LET yielded_fd00 == (fd)[server[self]] IN
                            LET yielded_network10 == Len(((network)[self]).queue) IN
                              /\ ((yielded_fd00) /\ ((yielded_network10) = (0))) \/ (timeout[self])
                              /\ IF Debug
                                    THEN /\ PrintT(<<"ClientTimeout", self, server[self], reqIdx[self]>>)
                                         /\ server' = [server EXCEPT ![self] = Nil]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                                    ELSE /\ server' = [server EXCEPT ![self] = Nil]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                       /\ UNCHANGED <<network, respCh, resp>>
                 /\ UNCHANGED << fd, rsm, allReqs, reqCh, acctSrvId, srvId, m, 
                                 sm, smDomain, srvId0, req, reqIdx, timeout >>

client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerPropSet: s0(self))
           \/ (\E self \in ServerAcctSet: s1(self))
           \/ (\E self \in ClientSet: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerPropSet : WF_vars(s0(self))
        /\ \A self \in ServerAcctSet : WF_vars(s1(self))
        /\ \A self \in ClientSet : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
