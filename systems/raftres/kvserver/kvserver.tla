-------------------------------- MODULE kvserver --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT Debug

CONSTANT NumServers
CONSTANT NumClients

CONSTANT BufferSize

\* This is only used for model checking / simulation
CONSTANT NumRequests

(********************

--mpcal kvserver {

    define {
        Nil == 0

        ProposeMessage == "pm"
        AcceptMessage  == "am"

        PutRequest  == "pq"
        PutResponse == "pp"
        GetRequest  == "gq"
        GetResponse == "gp"

        Put == "p"
        Get == "g"

        ServerPropSet == 1..NumServers
        ServerAcctSet == (NumServers+1)..(2*NumServers)

        ServerSet == ServerPropSet
        ClientSet == (2*NumServers+1)..(2*NumServers+NumClients)
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
            with (res = Head($variable)) {
                assert res.mtype = ProposeMessage;

                $variable := Tail($variable);
                yield [
                    mtype |-> AcceptMessage,
                    mcmd  |-> res.mcmd
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

    archetype AServerProp(ref srvId, ref net[_], ref propCh) {
    serverPropLoop:
        while (TRUE) {
            with (msg = net[srvId]) {
                assert msg.mdest = srvId;

                propCh := [
                    mtype |-> ProposeMessage,
                    mcmd  |-> msg
                ];
            };
        };
    }

    archetype AServerAcct(ref srvId, ref net[_], ref acctCh[_])
    variables m, sm = [k \in KeySet |-> Nil], smDomain = KeySet;
    {
    serverAccLoop:
        while (TRUE) {
            m := acctCh[srvId];
            assert m.mtype = AcceptMessage;

            with (cmd = m.mcmd) {
                if (cmd.mtype = PutRequest) {
                    sm       := sm @@ (cmd.mkey :> cmd.mvalue);
                    smDomain := smDomain \cup {cmd.mkey};
                };

                with (
                    i = srvId,
                    j = cmd.msource,
                    respType = IF cmd.mtype = PutRequest
                               THEN PutResponse
                               ELSE GetResponse,
                    respOk   = cmd.mkey \in smDomain,
                    value    = IF respOk
                               THEN sm[cmd.mkey]
                               ELSE Nil 
                ) {
                    net[j] := [
                        mtype     |-> respType,
                        mresponse |-> [
                            idx   |-> cmd.midx,
                            key   |-> cmd.mkey,
                            value |-> value,
                            ok    |-> respOk
                        ],
                        msource   |-> i,
                        mdest     |-> j
                    ];
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
                mtype = IF req.type = Put
                        THEN PutRequest
                        ELSE GetRequest
            ) {
                Send(net, server, fd, [
                    mtype   |-> mtype,
                    mkey    |-> req.key,
                    mvalue  |-> req.value,
                    midx    |-> reqIdx,
                    msource |-> self,
                    mdest   |-> server
                ]);
            };
        
        rcvResp:
            either {
                resp := net[self];
                assert resp.mdest = self;

                if (resp.mresponse.idx /= reqIdx) {
                    goto rcvResp;
                } else {
                    respCh := resp;
                };
            } or {
                await \/ /\ fd[server]
                         /\ netLen[self] = 0
                      \/ timeout;
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
--algorithm kvserver {
  variables network = [i \in NodeSet |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [i \in ServerSet |-> FALSE]; rsm = [i \in ServerSet |-> <<>>]; allReqs = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key2], [type |-> Get, key |-> Key1]>>; reqCh = SubSeq(allReqs, 1, NumRequests); respCh; acctSrvId = [i \in ServerAcctSet |-> (i) - (NumServers)];
  define{
    Nil == 0
    ProposeMessage == "pm"
    AcceptMessage == "am"
    PutRequest == "pq"
    PutResponse == "pp"
    GetRequest == "gq"
    GetResponse == "gp"
    Put == "p"
    Get == "g"
    ServerPropSet == (1) .. (NumServers)
    ServerAcctSet == ((NumServers) + (1)) .. ((2) * (NumServers))
    ServerSet == ServerPropSet
    ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
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
            assert ((msg).mdest) = (srvId);
            with (value00 = [mtype |-> ProposeMessage, mcmd |-> msg]) {
              rsm := [i \in ServerSet |-> Append((rsm)[i], value00)];
              goto serverPropLoop;
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
        with (res00 = Head((rsm)[srvId0])) {
          assert ((res00).mtype) = (ProposeMessage);
          rsm := [rsm EXCEPT ![srvId0] = Tail((rsm)[srvId0])];
          with (yielded_rsm0 = [mtype |-> AcceptMessage, mcmd |-> (res00).mcmd]) {
            m := yielded_rsm0;
            assert ((m).mtype) = (AcceptMessage);
            with (cmd = (m).mcmd) {
              if (((cmd).mtype) = (PutRequest)) {
                sm := (sm) @@ (((cmd).mkey) :> ((cmd).mvalue));
                smDomain := (smDomain) \union ({(cmd).mkey});
                with (
                  i = srvId0, 
                  j = (cmd).msource, 
                  respType = IF ((cmd).mtype) = (PutRequest) THEN PutResponse ELSE GetResponse, 
                  respOk = ((cmd).mkey) \in (smDomain), 
                  value = IF respOk THEN (sm)[(cmd).mkey] ELSE Nil, 
                  value10 = [mtype |-> respType, mresponse |-> [idx |-> (cmd).midx, key |-> (cmd).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                ) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]];
                  goto serverAccLoop;
                };
              } else {
                with (
                  i = srvId0, 
                  j = (cmd).msource, 
                  respType = IF ((cmd).mtype) = (PutRequest) THEN PutResponse ELSE GetResponse, 
                  respOk = ((cmd).mkey) \in (smDomain), 
                  value = IF respOk THEN (sm)[(cmd).mkey] ELSE Nil, 
                  value11 = [mtype |-> respType, mresponse |-> [idx |-> (cmd).midx, key |-> (cmd).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j]
                ) {
                  await ((network)[j]).enabled;
                  await (Len(((network)[j]).queue)) < (BufferSize);
                  network := [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]];
                  goto serverAccLoop;
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
        with (res10 = Head(reqCh)) {
          reqCh := Tail(reqCh);
          with (yielded_reqCh0 = res10) {
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
          with (mtype = IF ((req).type) = (Put) THEN PutRequest ELSE GetRequest) {
            either {
              with (value20 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> (req).value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
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
          };
        };
      } else {
        with (mtype = IF ((req).type) = (Put) THEN PutRequest ELSE GetRequest) {
          either {
            with (value21 = [mtype |-> mtype, mkey |-> (req).key, mvalue |-> (req).value, midx |-> reqIdx, msource |-> self, mdest |-> server]) {
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
    rcvResp:
      either {
        assert ((network)[self]).enabled;
        await (Len(((network)[self]).queue)) > (0);
        with (readMsg10 = Head(((network)[self]).queue)) {
          network := [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]];
          with (yielded_network00 = readMsg10) {
            resp := yielded_network00;
            assert ((resp).mdest) = (self);
            if ((((resp).mresponse).idx) # (reqIdx)) {
              goto rcvResp;
            } else {
              respCh := resp;
              goto clientLoop;
            };
          };
        };
      } or {
        with (
          yielded_fd00 = (fd)[server], 
          yielded_network10 = Len(((network)[self]).queue)
        ) {
          await ((yielded_fd00) /\ ((yielded_network10) = (0))) \/ (timeout);
          server := Nil;
          goto sndReq;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "7ba819a9" /\ chksum(tla) = "229ef363")
CONSTANT defaultInitValue
VARIABLES network, fd, rsm, allReqs, reqCh, respCh, acctSrvId, pc

(* define statement *)
Nil == 0
ProposeMessage == "pm"
AcceptMessage == "am"
PutRequest == "pq"
PutResponse == "pp"
GetRequest == "gq"
GetResponse == "gp"
Put == "p"
Get == "g"
ServerPropSet == (1) .. (NumServers)
ServerAcctSet == ((NumServers) + (1)) .. ((2) * (NumServers))
ServerSet == ServerPropSet
ClientSet == (((2) * (NumServers)) + (1)) .. (((2) * (NumServers)) + (NumClients))
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
                                             "Failure of assertion at line 311, column 9.")
                                   /\ (Len(((network)[srvId[self]]).queue)) > (0)
                                   /\ LET readMsg0 == Head(((network)[srvId[self]]).queue) IN
                                        /\ network' = [network EXCEPT ![srvId[self]] = [queue |-> Tail(((network)[srvId[self]]).queue), enabled |-> ((network)[srvId[self]]).enabled]]
                                        /\ LET yielded_network == readMsg0 IN
                                             LET msg == yielded_network IN
                                               /\ Assert(((msg).mdest) = (srvId[self]), 
                                                         "Failure of assertion at line 319, column 13.")
                                               /\ LET value00 == [mtype |-> ProposeMessage, mcmd |-> msg] IN
                                                    /\ rsm' = [i \in ServerSet |-> Append((rsm)[i], value00)]
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
                                  /\ LET res00 == Head((rsm)[srvId0[self]]) IN
                                       /\ Assert(((res00).mtype) = (ProposeMessage), 
                                                 "Failure of assertion at line 338, column 11.")
                                       /\ rsm' = [rsm EXCEPT ![srvId0[self]] = Tail((rsm)[srvId0[self]])]
                                       /\ LET yielded_rsm0 == [mtype |-> AcceptMessage, mcmd |-> (res00).mcmd] IN
                                            /\ m' = [m EXCEPT ![self] = yielded_rsm0]
                                            /\ Assert(((m'[self]).mtype) = (AcceptMessage), 
                                                      "Failure of assertion at line 342, column 13.")
                                            /\ LET cmd == (m'[self]).mcmd IN
                                                 IF ((cmd).mtype) = (PutRequest)
                                                    THEN /\ sm' = [sm EXCEPT ![self] = (sm[self]) @@ (((cmd).mkey) :> ((cmd).mvalue))]
                                                         /\ smDomain' = [smDomain EXCEPT ![self] = (smDomain[self]) \union ({(cmd).mkey})]
                                                         /\ LET i == srvId0[self] IN
                                                              LET j == (cmd).msource IN
                                                                LET respType == IF ((cmd).mtype) = (PutRequest) THEN PutResponse ELSE GetResponse IN
                                                                  LET respOk == ((cmd).mkey) \in (smDomain'[self]) IN
                                                                    LET value == IF respOk THEN (sm'[self])[(cmd).mkey] ELSE Nil IN
                                                                      LET value10 == [mtype |-> respType, mresponse |-> [idx |-> (cmd).midx, key |-> (cmd).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                        /\ ((network)[j]).enabled
                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value10), enabled |-> ((network)[j]).enabled]]
                                                                        /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
                                                    ELSE /\ LET i == srvId0[self] IN
                                                              LET j == (cmd).msource IN
                                                                LET respType == IF ((cmd).mtype) = (PutRequest) THEN PutResponse ELSE GetResponse IN
                                                                  LET respOk == ((cmd).mkey) \in (smDomain[self]) IN
                                                                    LET value == IF respOk THEN (sm[self])[(cmd).mkey] ELSE Nil IN
                                                                      LET value11 == [mtype |-> respType, mresponse |-> [idx |-> (cmd).midx, key |-> (cmd).mkey, value |-> value, ok |-> respOk], msource |-> i, mdest |-> j] IN
                                                                        /\ ((network)[j]).enabled
                                                                        /\ (Len(((network)[j]).queue)) < (BufferSize)
                                                                        /\ network' = [network EXCEPT ![j] = [queue |-> Append(((network)[j]).queue, value11), enabled |-> ((network)[j]).enabled]]
                                                                        /\ pc' = [pc EXCEPT ![self] = "serverAccLoop"]
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
                               /\ LET res10 == Head(reqCh) IN
                                    /\ reqCh' = Tail(reqCh)
                                    /\ LET yielded_reqCh0 == res10 IN
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
                                /\ LET mtype == IF ((req[self]).type) = (Put) THEN PutRequest ELSE GetRequest IN
                                     \/ /\ LET value20 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> (req[self]).value, midx |-> reqIdx[self], msource |-> self, mdest |-> server'[self]] IN
                                             /\ ((network)[server'[self]]).enabled
                                             /\ (Len(((network)[server'[self]]).queue)) < (BufferSize)
                                             /\ network' = [network EXCEPT ![server'[self]] = [queue |-> Append(((network)[server'[self]]).queue, value20), enabled |-> ((network)[server'[self]]).enabled]]
                                             /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                     \/ /\ LET yielded_fd1 == (fd)[server'[self]] IN
                                             /\ yielded_fd1
                                             /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                        /\ UNCHANGED network
                      ELSE /\ LET mtype == IF ((req[self]).type) = (Put) THEN PutRequest ELSE GetRequest IN
                                \/ /\ LET value21 == [mtype |-> mtype, mkey |-> (req[self]).key, mvalue |-> (req[self]).value, midx |-> reqIdx[self], msource |-> self, mdest |-> server[self]] IN
                                        /\ ((network)[server[self]]).enabled
                                        /\ (Len(((network)[server[self]]).queue)) < (BufferSize)
                                        /\ network' = [network EXCEPT ![server[self]] = [queue |-> Append(((network)[server[self]]).queue, value21), enabled |-> ((network)[server[self]]).enabled]]
                                        /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                \/ /\ LET yielded_fd2 == (fd)[server[self]] IN
                                        /\ yielded_fd2
                                        /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                   /\ UNCHANGED network
                           /\ UNCHANGED server
                /\ UNCHANGED << fd, rsm, allReqs, reqCh, respCh, acctSrvId, 
                                srvId, m, sm, smDomain, srvId0, req, reqIdx, 
                                resp, timeout >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ \/ /\ Assert(((network)[self]).enabled, 
                                 "Failure of assertion at line 439, column 9.")
                       /\ (Len(((network)[self]).queue)) > (0)
                       /\ LET readMsg10 == Head(((network)[self]).queue) IN
                            /\ network' = [network EXCEPT ![self] = [queue |-> Tail(((network)[self]).queue), enabled |-> ((network)[self]).enabled]]
                            /\ LET yielded_network00 == readMsg10 IN
                                 /\ resp' = [resp EXCEPT ![self] = yielded_network00]
                                 /\ Assert(((resp'[self]).mdest) = (self), 
                                           "Failure of assertion at line 445, column 13.")
                                 /\ IF (((resp'[self]).mresponse).idx) # (reqIdx[self])
                                       THEN /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                            /\ UNCHANGED respCh
                                       ELSE /\ respCh' = resp'[self]
                                            /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                       /\ UNCHANGED server
                    \/ /\ LET yielded_fd00 == (fd)[server[self]] IN
                            LET yielded_network10 == Len(((network)[self]).queue) IN
                              /\ ((yielded_fd00) /\ ((yielded_network10) = (0))) \/ (timeout[self])
                              /\ server' = [server EXCEPT ![self] = Nil]
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
