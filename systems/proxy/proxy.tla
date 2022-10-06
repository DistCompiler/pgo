------------------------------- MODULE proxy -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_SERVERS
CONSTANT NUM_CLIENTS
CONSTANT EXPLORE_FAIL
CONSTANT CLIENT_RUN

ASSUME NUM_SERVERS > 0 /\ NUM_CLIENTS > 0

(********************

--mpcal proxy {
    define {
        FAIL == 100
        NUM_NODES == NUM_SERVERS + NUM_CLIENTS + 1

        ProxyID == NUM_NODES

        REQ_MSG_TYP == 1
        RESP_MSG_TYP == 2
        PROXY_REQ_MSG_TYP == 3
        PROXY_RESP_MSG_TYP == 4

        NODE_SET == 1..NUM_NODES
        SERVER_SET == 1..NUM_SERVERS
        CLIENT_SET == (NUM_SERVERS+1)..(NUM_SERVERS+NUM_CLIENTS)

        MSG_TYP_SET == {REQ_MSG_TYP, RESP_MSG_TYP, PROXY_REQ_MSG_TYP, PROXY_RESP_MSG_TYP}

        MSG_ID_BOUND == 2
    }

    macro mayFail(selfID, netEnabled) {
        if (EXPLORE_FAIL) {
            either { skip; } or {
                netEnabled[selfID, PROXY_REQ_MSG_TYP] := FALSE;
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

    mapping macro Requests {
        read {
            with(value = $variable) {
                $variable := $variable + 1;
                yield value;
            }
        }
        write { assert(FALSE); yield $value; }
    }

    archetype AProxy(ref net[_], ref fd[_])
    variables
        msg, proxyMsg, idx, resp, proxyResp;
    {
    proxyLoop:
        while(TRUE) {
            msg := net[<<ProxyID, REQ_MSG_TYP>>];
            assert(msg.to = ProxyID /\ msg.typ = REQ_MSG_TYP);
            proxyResp := [from |-> ProxyID, to |-> msg.from, body |-> FAIL, 
                          id |-> msg.id, typ |-> PROXY_RESP_MSG_TYP];
            idx := 1;

            serversLoop:
                while (idx <= NUM_SERVERS) {
                    either {
                        proxyMsg := [from |-> ProxyID, to |-> idx, body |-> msg.body, 
                                     id |-> msg.id, typ |-> PROXY_REQ_MSG_TYP];
                        net[<<proxyMsg.to, PROXY_REQ_MSG_TYP>>] := proxyMsg;
                    } or {
                        await fd[idx];
                        idx := idx + 1;
                        goto serversLoop;
                    };
            
                proxyRcvMsg:
                    either {
                        with (tmp = net[<<ProxyID, PROXY_RESP_MSG_TYP>>]) {
                            if (tmp.from # idx \/ tmp.id # msg.id) {
                                goto proxyRcvMsg;
                            } else {
                                proxyResp := tmp;
                                assert(
                                    /\ proxyResp.to = ProxyID
                                    /\ proxyResp.from = idx
                                    /\ proxyResp.id = msg.id
                                    /\ proxyResp.typ = PROXY_RESP_MSG_TYP
                                );
                                goto sendMsgToClient;
                            };
                        };
                    } or {
                        await fd[idx];
                        idx := idx + 1;
                    };
                };
        
        sendMsgToClient:
            resp := [from |-> ProxyID, to |-> msg.from, body |-> proxyResp.body, 
                     id |-> msg.id, typ |-> RESP_MSG_TYP];
            net[<<resp.to, resp.typ>>] := resp;
        };
    }

    archetype AServer(ref net[_], ref netEnabled[_], ref fd[_])
    variables
        msg, resp;
    {
    serverLoop:
        while (TRUE) {
            mayFail(self, netEnabled);

        serverRcvMsg:
            msg := net[<<self, PROXY_REQ_MSG_TYP>>];
            assert(
                /\ msg.to = self
                /\ msg.from = ProxyID
                /\ msg.typ = PROXY_REQ_MSG_TYP
            );
            mayFail(self, netEnabled);

        serverSendMsg:
            resp := [from |-> self, to |-> msg.from, body |-> self, 
                     id |-> msg.id, typ |-> PROXY_RESP_MSG_TYP];
            net[<<resp.to, resp.typ>>] := resp;
            mayFail(self, netEnabled);
        };

    failLabel:
        fd[self] := TRUE;
    }

    archetype AClient(ref net[_], ref input, ref output)
    variables
        req, resp, reqId = 0;
    {
    clientLoop:
        while (CLIENT_RUN) {
            req := [from |-> self, to |-> ProxyID, body |-> input, 
                    id |-> reqId, typ |-> REQ_MSG_TYP];
            net[<<req.to, req.typ>>] := req;
            \* print <<"CLIENT START", req>>;

        clientRcvResp:
            resp := net[<<self, RESP_MSG_TYP>>];
            assert(
                /\ resp.to = self
                /\ resp.id = reqId
                /\ resp.from = ProxyID
                /\ resp.typ = RESP_MSG_TYP
            );
            \* print <<"CLIENT RESP", resp>>;
            reqId := (reqId + 1) % MSG_ID_BOUND;
            output := resp;
        }
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> [queue |-> <<>>, enabled |-> TRUE]];
        fd = [id \in NODE_SET |-> FALSE];
        output = <<>>;
    
    fair process (Proxy = ProxyID) == instance AProxy(ref network[_], ref fd[_])
        mapping network[_] via ReliableFIFOLink
        mapping fd[_] via PracticalFD; \* PerfectFD

    fair process (Server \in SERVER_SET) == instance AServer(ref network[_], ref network[_], ref fd[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via NetworkToggle
        mapping @3[_] via PracticalFD; \* PerfectFD

    fair process (Client \in CLIENT_SET) == instance AClient(ref network[_], 0, ref output) \* Client -> 0
        mapping network[_] via ReliableFIFOLink
        mapping @2 via Requests; \* added for TraceCheck
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm proxy {
  variables network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [id \in NODE_SET |-> FALSE]; output = <<>>;
  define{
    FAIL == 100
    NUM_NODES == ((NUM_SERVERS) + (NUM_CLIENTS)) + (1)
    ProxyID == NUM_NODES
    REQ_MSG_TYP == 1
    RESP_MSG_TYP == 2
    PROXY_REQ_MSG_TYP == 3
    PROXY_RESP_MSG_TYP == 4
    NODE_SET == (1) .. (NUM_NODES)
    SERVER_SET == (1) .. (NUM_SERVERS)
    CLIENT_SET == ((NUM_SERVERS) + (1)) .. ((NUM_SERVERS) + (NUM_CLIENTS))
    MSG_TYP_SET == {REQ_MSG_TYP, RESP_MSG_TYP, PROXY_REQ_MSG_TYP, PROXY_RESP_MSG_TYP}
    MSG_ID_BOUND == 2
  }
  
  fair process (Proxy = ProxyID)
    variables msg; proxyMsg; idx; resp; proxyResp;
  {
    proxyLoop:
      if (TRUE) {
        assert ((network)[<<ProxyID, REQ_MSG_TYP>>]).enabled;
        await (Len(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)) > (0);
        with (readMsg00 = Head(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)) {
          network := [network EXCEPT ![<<ProxyID, REQ_MSG_TYP>>] = [queue |-> Tail(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue), enabled |-> ((network)[<<ProxyID, REQ_MSG_TYP>>]).enabled]];
          with (yielded_network3 = readMsg00) {
            msg := yielded_network3;
            assert (((msg).to) = (ProxyID)) /\ (((msg).typ) = (REQ_MSG_TYP));
            proxyResp := [from |-> ProxyID, to |-> (msg).from, body |-> FAIL, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
            idx := 1;
            goto serversLoop;
          };
        };
      } else {
        goto Done;
      };
    serversLoop:
      if ((idx) <= (NUM_SERVERS)) {
        either {
          proxyMsg := [from |-> ProxyID, to |-> idx, body |-> (msg).body, id |-> (msg).id, typ |-> PROXY_REQ_MSG_TYP];
          with (value00 = proxyMsg) {
            await ((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).enabled;
            network := [network EXCEPT ![<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>] = [queue |-> Append(((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).queue, value00), enabled |-> ((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).enabled]];
            goto proxyRcvMsg;
          };
        } or {
          if (((fd)[idx]) = (FALSE)) {
            either {
              with (yielded_fd5 = TRUE) {
                await yielded_fd5;
                idx := (idx) + (1);
                goto serversLoop;
              };
            } or {
              with (yielded_fd00 = FALSE) {
                await yielded_fd00;
                idx := (idx) + (1);
                goto serversLoop;
              };
            };
          } else {
            with (yielded_fd10 = (fd)[idx]) {
              await yielded_fd10;
              idx := (idx) + (1);
              goto serversLoop;
            };
          };
        };
      } else {
        goto sendMsgToClient;
      };
    proxyRcvMsg:
      either {
        assert ((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).enabled;
        await (Len(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)) > (0);
        with (readMsg1 = Head(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)) {
          network := [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = [queue |-> Tail(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue), enabled |-> ((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).enabled]];
          with (
            yielded_network0 = readMsg1, 
            tmp = yielded_network0
          ) {
            if ((((tmp).from) # (idx)) \/ (((tmp).id) # ((msg).id))) {
              goto proxyRcvMsg;
            } else {
              proxyResp := tmp;
              assert (((((proxyResp).to) = (ProxyID)) /\ (((proxyResp).from) = (idx))) /\ (((proxyResp).id) = ((msg).id))) /\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP));
              goto sendMsgToClient;
            };
          };
        };
      } or {
        if (((fd)[idx]) = (FALSE)) {
          either {
            with (yielded_fd20 = TRUE) {
              await yielded_fd20;
              idx := (idx) + (1);
              goto serversLoop;
            };
          } or {
            with (yielded_fd30 = FALSE) {
              await yielded_fd30;
              idx := (idx) + (1);
              goto serversLoop;
            };
          };
        } else {
          with (yielded_fd40 = (fd)[idx]) {
            await yielded_fd40;
            idx := (idx) + (1);
            goto serversLoop;
          };
        };
      };
    sendMsgToClient:
      resp := [from |-> ProxyID, to |-> (msg).from, body |-> (proxyResp).body, id |-> (msg).id, typ |-> RESP_MSG_TYP];
      with (value10 = resp) {
        await ((network)[<<(resp).to, (resp).typ>>]).enabled;
        network := [network EXCEPT ![<<(resp).to, (resp).typ>>] = [queue |-> Append(((network)[<<(resp).to, (resp).typ>>]).queue, value10), enabled |-> ((network)[<<(resp).to, (resp).typ>>]).enabled]];
        goto proxyLoop;
      };
  }
  
  fair process (Server \in SERVER_SET)
    variables msg0; resp0;
  {
    serverLoop:
      if (TRUE) {
        if (EXPLORE_FAIL) {
          either {
            skip;
            goto serverRcvMsg;
          } or {
            with (value20 = FALSE) {
              network := [network EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value20]];
              goto failLabel;
            };
          };
        } else {
          goto serverRcvMsg;
        };
      } else {
        goto failLabel;
      };
    serverRcvMsg:
      assert ((network)[<<self, PROXY_REQ_MSG_TYP>>]).enabled;
      await (Len(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue)) > (0);
      with (
        readMsg20 = Head(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue), 
        network0 = [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = [queue |-> Tail(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue), enabled |-> ((network)[<<self, PROXY_REQ_MSG_TYP>>]).enabled]], 
        yielded_network10 = readMsg20
      ) {
        msg0 := yielded_network10;
        assert ((((msg0).to) = (self)) /\ (((msg0).from) = (ProxyID))) /\ (((msg0).typ) = (PROXY_REQ_MSG_TYP));
        if (EXPLORE_FAIL) {
          either {
            skip;
            network := network0;
            goto serverSendMsg;
          } or {
            with (value30 = FALSE) {
              network := [network0 EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network0)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value30]];
              goto failLabel;
            };
          };
        } else {
          network := network0;
          goto serverSendMsg;
        };
      };
    serverSendMsg:
      resp0 := [from |-> self, to |-> (msg0).from, body |-> self, id |-> (msg0).id, typ |-> PROXY_RESP_MSG_TYP];
      with (value40 = resp0) {
        await ((network)[<<(resp0).to, (resp0).typ>>]).enabled;
        with (network1 = [network EXCEPT ![<<(resp0).to, (resp0).typ>>] = [queue |-> Append(((network)[<<(resp0).to, (resp0).typ>>]).queue, value40), enabled |-> ((network)[<<(resp0).to, (resp0).typ>>]).enabled]]) {
          if (EXPLORE_FAIL) {
            either {
              skip;
              network := network1;
              goto serverLoop;
            } or {
              with (value50 = FALSE) {
                network := [network1 EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network1)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value50]];
                goto failLabel;
              };
            };
          } else {
            network := network1;
            goto serverLoop;
          };
        };
      };
    failLabel:
      with (value60 = TRUE) {
        fd := [fd EXCEPT ![self] = value60];
        goto Done;
      };
  }
  
  fair process (Client \in CLIENT_SET)
    variables req; resp1; reqId = 0; input = 0;
  {
    clientLoop:
      if (CLIENT_RUN) {
        with (value70 = input) {
          input := (input) + (1);
          with (yielded_input0 = value70) {
            req := [from |-> self, to |-> ProxyID, body |-> yielded_input0, id |-> reqId, typ |-> REQ_MSG_TYP];
            with (value80 = req) {
              await ((network)[<<(req).to, (req).typ>>]).enabled;
              network := [network EXCEPT ![<<(req).to, (req).typ>>] = [queue |-> Append(((network)[<<(req).to, (req).typ>>]).queue, value80), enabled |-> ((network)[<<(req).to, (req).typ>>]).enabled]];
              goto clientRcvResp;
            };
          };
        };
      } else {
        goto Done;
      };
    clientRcvResp:
      assert ((network)[<<self, RESP_MSG_TYP>>]).enabled;
      await (Len(((network)[<<self, RESP_MSG_TYP>>]).queue)) > (0);
      with (readMsg30 = Head(((network)[<<self, RESP_MSG_TYP>>]).queue)) {
        network := [network EXCEPT ![<<self, RESP_MSG_TYP>>] = [queue |-> Tail(((network)[<<self, RESP_MSG_TYP>>]).queue), enabled |-> ((network)[<<self, RESP_MSG_TYP>>]).enabled]];
        with (yielded_network20 = readMsg30) {
          resp1 := yielded_network20;
          assert (((((resp1).to) = (self)) /\ (((resp1).id) = (reqId))) /\ (((resp1).from) = (ProxyID))) /\ (((resp1).typ) = (RESP_MSG_TYP));
          reqId := ((reqId) + (1)) % (MSG_ID_BOUND);
          output := resp1;
          goto clientLoop;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION


********************)

\* BEGIN TRANSLATION (chksum(pcal) = "36aae2fc" /\ chksum(tla) = "fde48588")
CONSTANT defaultInitValue
VARIABLES network, fd, output, pc

(* define statement *)
FAIL == 100
NUM_NODES == ((NUM_SERVERS) + (NUM_CLIENTS)) + (1)
ProxyID == NUM_NODES
REQ_MSG_TYP == 1
RESP_MSG_TYP == 2
PROXY_REQ_MSG_TYP == 3
PROXY_RESP_MSG_TYP == 4
NODE_SET == (1) .. (NUM_NODES)
SERVER_SET == (1) .. (NUM_SERVERS)
CLIENT_SET == ((NUM_SERVERS) + (1)) .. ((NUM_SERVERS) + (NUM_CLIENTS))
MSG_TYP_SET == {REQ_MSG_TYP, RESP_MSG_TYP, PROXY_REQ_MSG_TYP, PROXY_RESP_MSG_TYP}
MSG_ID_BOUND == 2

VARIABLES msg, proxyMsg, idx, resp, proxyResp, msg0, resp0, req, resp1, reqId, 
          input

vars == << network, fd, output, pc, msg, proxyMsg, idx, resp, proxyResp, msg0, 
           resp0, req, resp1, reqId, input >>

ProcSet == {ProxyID} \cup (SERVER_SET) \cup (CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> [queue |-> <<>>, enabled |-> TRUE]]
        /\ fd = [id \in NODE_SET |-> FALSE]
        /\ output = <<>>
        (* Process Proxy *)
        /\ msg = defaultInitValue
        /\ proxyMsg = defaultInitValue
        /\ idx = defaultInitValue
        /\ resp = defaultInitValue
        /\ proxyResp = defaultInitValue
        (* Process Server *)
        /\ msg0 = [self \in SERVER_SET |-> defaultInitValue]
        /\ resp0 = [self \in SERVER_SET |-> defaultInitValue]
        (* Process Client *)
        /\ req = [self \in CLIENT_SET |-> defaultInitValue]
        /\ resp1 = [self \in CLIENT_SET |-> defaultInitValue]
        /\ reqId = [self \in CLIENT_SET |-> 0]
        /\ input = [self \in CLIENT_SET |-> self]
        /\ pc = [self \in ProcSet |-> CASE self = ProxyID -> "proxyLoop"
                                        [] self \in SERVER_SET -> "serverLoop"
                                        [] self \in CLIENT_SET -> "clientLoop"]

proxyLoop == /\ pc[ProxyID] = "proxyLoop"
             /\ IF TRUE
                   THEN /\ Assert(((network)[<<ProxyID, REQ_MSG_TYP>>]).enabled, 
                                  "Failure of assertion at line 235, column 9.")
                        /\ (Len(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)) > (0)
                        /\ LET readMsg00 == Head(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue) IN
                             /\ network' = [network EXCEPT ![<<ProxyID, REQ_MSG_TYP>>] = [queue |-> Tail(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue), enabled |-> ((network)[<<ProxyID, REQ_MSG_TYP>>]).enabled]]
                             /\ LET yielded_network3 == readMsg00 IN
                                  /\ msg' = yielded_network3
                                  /\ Assert((((msg').to) = (ProxyID)) /\ (((msg').typ) = (REQ_MSG_TYP)), 
                                            "Failure of assertion at line 241, column 13.")
                                  /\ proxyResp' = [from |-> ProxyID, to |-> (msg').from, body |-> FAIL, id |-> (msg').id, typ |-> PROXY_RESP_MSG_TYP]
                                  /\ idx' = 1
                                  /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                   ELSE /\ pc' = [pc EXCEPT ![ProxyID] = "Done"]
                        /\ UNCHANGED << network, msg, idx, proxyResp >>
             /\ UNCHANGED << fd, output, proxyMsg, resp, msg0, resp0, req, 
                             resp1, reqId, input >>

serversLoop == /\ pc[ProxyID] = "serversLoop"
               /\ IF (idx) <= (NUM_SERVERS)
                     THEN /\ \/ /\ proxyMsg' = [from |-> ProxyID, to |-> idx, body |-> (msg).body, id |-> (msg).id, typ |-> PROXY_REQ_MSG_TYP]
                                /\ LET value7 == proxyMsg' IN
                                     /\ ((network)[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>]).enabled
                                     /\ network' = [network EXCEPT ![<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>] = [queue |-> Append(((network)[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>]).queue, value7), enabled |-> ((network)[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>]).enabled]]
                                     /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsg"]
                                /\ idx' = idx
                             \/ /\ LET yielded_fd1 == (fd)[idx] IN
                                     /\ yielded_fd1
                                     /\ idx' = (idx) + (1)
                                     /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                                /\ UNCHANGED <<network, proxyMsg>>
                     ELSE /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
                          /\ UNCHANGED << network, proxyMsg, idx >>
               /\ UNCHANGED << fd, output, msg, resp, proxyResp, msg0, resp0, 
                               req, resp1, reqId, input >>

proxyRcvMsg == /\ pc[ProxyID] = "proxyRcvMsg"
               /\ \/ /\ Assert(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).enabled, 
                               "Failure of assertion at line 271, column 9.")
                     /\ (Len(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)) > (0)
                     /\ LET readMsg1 == Head(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue) IN
                          /\ network' = [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = [queue |-> Tail(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue), enabled |-> ((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).enabled]]
                          /\ LET yielded_network0 == readMsg1 IN
                               LET tmp == yielded_network0 IN
                                 IF (((tmp).from) # (idx)) \/ (((tmp).id) # ((msg).id))
                                    THEN /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsg"]
                                         /\ UNCHANGED proxyResp
                                    ELSE /\ proxyResp' = tmp
                                         /\ Assert((((((proxyResp').to) = (ProxyID)) /\ (((proxyResp').from) = (idx))) /\ (((proxyResp').id) = ((msg).id))) /\ (((proxyResp').typ) = (PROXY_RESP_MSG_TYP)), 
                                                   "Failure of assertion at line 281, column 17.")
                                         /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
                     /\ idx' = idx
                  \/ /\ LET yielded_fd00 == (fd)[idx] IN
                          /\ yielded_fd00
                          /\ idx' = (idx) + (1)
                          /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                     /\ UNCHANGED <<network, proxyResp>>
               /\ UNCHANGED << fd, output, msg, proxyMsg, resp, msg0, resp0, 
                               req, resp1, reqId, input >>

sendMsgToClient == /\ pc[ProxyID] = "sendMsgToClient"
                   /\ resp' = [from |-> ProxyID, to |-> (msg).from, body |-> (proxyResp).body, id |-> (msg).id, typ |-> RESP_MSG_TYP]
                   /\ LET value00 == resp' IN
                        /\ ((network)[<<(resp').to, (resp').typ>>]).enabled
                        /\ network' = [network EXCEPT ![<<(resp').to, (resp').typ>>] = [queue |-> Append(((network)[<<(resp').to, (resp').typ>>]).queue, value00), enabled |-> ((network)[<<(resp').to, (resp').typ>>]).enabled]]
                        /\ pc' = [pc EXCEPT ![ProxyID] = "proxyLoop"]
                   /\ UNCHANGED << fd, output, msg, proxyMsg, idx, proxyResp, 
                                   msg0, resp0, req, resp1, reqId, input >>

Proxy == proxyLoop \/ serversLoop \/ proxyRcvMsg \/ sendMsgToClient

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ IF EXPLORE_FAIL
                                     THEN /\ \/ /\ TRUE
                                                /\ pc' = [pc EXCEPT ![self] = "serverRcvMsg"]
                                                /\ UNCHANGED network
                                             \/ /\ LET value10 == FALSE IN
                                                     /\ network' = [network EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value10]]
                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverRcvMsg"]
                                          /\ UNCHANGED network
                          ELSE /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                               /\ UNCHANGED network
                    /\ UNCHANGED << fd, output, msg, proxyMsg, idx, resp, 
                                    proxyResp, msg0, resp0, req, resp1, reqId, 
                                    input >>

serverRcvMsg(self) == /\ pc[self] = "serverRcvMsg"
                      /\ Assert(((network)[<<self, PROXY_REQ_MSG_TYP>>]).enabled, 
                                "Failure of assertion at line 325, column 7.")
                      /\ (Len(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue)) > (0)
                      /\ LET readMsg20 == Head(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue) IN
                           LET network0 == [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = [queue |-> Tail(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue), enabled |-> ((network)[<<self, PROXY_REQ_MSG_TYP>>]).enabled]] IN
                             LET yielded_network10 == readMsg20 IN
                               /\ msg0' = [msg0 EXCEPT ![self] = yielded_network10]
                               /\ Assert(((((msg0'[self]).to) = (self)) /\ (((msg0'[self]).from) = (ProxyID))) /\ (((msg0'[self]).typ) = (PROXY_REQ_MSG_TYP)), 
                                         "Failure of assertion at line 331, column 13.")
                               /\ IF EXPLORE_FAIL
                                     THEN /\ \/ /\ TRUE
                                                /\ network' = network0
                                                /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                                             \/ /\ LET value20 == FALSE IN
                                                     /\ network' = [network0 EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network0)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value20]]
                                                     /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                     ELSE /\ network' = network0
                                          /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                      /\ UNCHANGED << fd, output, msg, proxyMsg, idx, resp, 
                                      proxyResp, resp0, req, resp1, reqId, 
                                      input >>

serverSendMsg(self) == /\ pc[self] = "serverSendMsg"
                       /\ resp0' = [resp0 EXCEPT ![self] = [from |-> self, to |-> (msg0[self]).from, body |-> self, id |-> (msg0[self]).id, typ |-> PROXY_RESP_MSG_TYP]]
                       /\ LET value30 == resp0'[self] IN
                            /\ ((network)[<<(resp0'[self]).to, (resp0'[self]).typ>>]).enabled
                            /\ LET network1 == [network EXCEPT ![<<(resp0'[self]).to, (resp0'[self]).typ>>] = [queue |-> Append(((network)[<<(resp0'[self]).to, (resp0'[self]).typ>>]).queue, value30), enabled |-> ((network)[<<(resp0'[self]).to, (resp0'[self]).typ>>]).enabled]] IN
                                 IF EXPLORE_FAIL
                                    THEN /\ \/ /\ TRUE
                                               /\ network' = network1
                                               /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                            \/ /\ LET value40 == FALSE IN
                                                    /\ network' = [network1 EXCEPT ![self, PROXY_REQ_MSG_TYP] = [queue |-> ((network1)[self, PROXY_REQ_MSG_TYP]).queue, enabled |-> value40]]
                                                    /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                    ELSE /\ network' = network1
                                         /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                       /\ UNCHANGED << fd, output, msg, proxyMsg, idx, resp, 
                                       proxyResp, msg0, req, resp1, reqId, 
                                       input >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ LET value50 == TRUE IN
                        /\ fd' = [fd EXCEPT ![self] = value50]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, output, msg, proxyMsg, idx, resp, 
                                   proxyResp, msg0, resp0, req, resp1, reqId, 
                                   input >>

Server(self) == serverLoop(self) \/ serverRcvMsg(self)
                   \/ serverSendMsg(self) \/ failLabel(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF CLIENT_RUN
                          THEN /\ req' = [req EXCEPT ![self] = [from |-> self, to |-> ProxyID, body |-> input[self], id |-> reqId[self], typ |-> REQ_MSG_TYP]]
                               /\ LET value60 == req'[self] IN
                                    /\ ((network)[<<(req'[self]).to, (req'[self]).typ>>]).enabled
                                    /\ network' = [network EXCEPT ![<<(req'[self]).to, (req'[self]).typ>>] = [queue |-> Append(((network)[<<(req'[self]).to, (req'[self]).typ>>]).queue, value60), enabled |-> ((network)[<<(req'[self]).to, (req'[self]).typ>>]).enabled]]
                                    /\ pc' = [pc EXCEPT ![self] = "clientRcvResp"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, req >>
                    /\ UNCHANGED << fd, output, msg, proxyMsg, idx, resp, 
                                    proxyResp, msg0, resp0, resp1, reqId, 
                                    input >>

clientRcvResp(self) == /\ pc[self] = "clientRcvResp"
                       /\ Assert(((network)[<<self, RESP_MSG_TYP>>]).enabled, 
                                 "Failure of assertion at line 394, column 7.")
                       /\ (Len(((network)[<<self, RESP_MSG_TYP>>]).queue)) > (0)
                       /\ LET readMsg30 == Head(((network)[<<self, RESP_MSG_TYP>>]).queue) IN
                            /\ network' = [network EXCEPT ![<<self, RESP_MSG_TYP>>] = [queue |-> Tail(((network)[<<self, RESP_MSG_TYP>>]).queue), enabled |-> ((network)[<<self, RESP_MSG_TYP>>]).enabled]]
                            /\ LET yielded_network20 == readMsg30 IN
                                 /\ resp1' = [resp1 EXCEPT ![self] = yielded_network20]
                                 /\ Assert((((((resp1'[self]).to) = (self)) /\ (((resp1'[self]).id) = (reqId[self]))) /\ (((resp1'[self]).from) = (ProxyID))) /\ (((resp1'[self]).typ) = (RESP_MSG_TYP)), 
                                           "Failure of assertion at line 400, column 11.")
                                 /\ reqId' = [reqId EXCEPT ![self] = ((reqId[self]) + (1)) % (MSG_ID_BOUND)]
                                 /\ output' = resp1'[self]
                                 /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                       /\ UNCHANGED << fd, msg, proxyMsg, idx, resp, proxyResp, 
                                       msg0, resp0, req, input >>

Client(self) == clientLoop(self) \/ clientRcvResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Proxy
           \/ (\E self \in SERVER_SET: Server(self))
           \/ (\E self \in CLIENT_SET: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proxy)
        /\ \A self \in SERVER_SET : WF_vars(Server(self))
        /\ \A self \in CLIENT_SET : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants

\* Only holds if PerfectFD is used
ProxyOK == (pc[ProxyID] = "sendMsgToClient" /\ proxyResp.body = FAIL) 
                => (\A server \in SERVER_SET : pc[server] = "failLabel" \/ pc[server] = "Done")

\* Properties

ReceiveResp(client) == pc[client] = "clientSendReq" ~> pc[client] = "clientRcvResp"
ClientsOK == \A client \in CLIENT_SET : ReceiveResp(client)

=============================================================================
\* Modification History
\* Last modified Thu Oct 21 00:59:02 PDT 2021 by shayan
\* Created Wed Jun 30 19:19:46 PDT 2021 by shayan
