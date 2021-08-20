------------------------------- MODULE proxy -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_SERVERS
CONSTANT NUM_CLIENTS
CONSTANT EXPLORE_FAIL
CONSTANT F

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
    }

    mapping macro ReliableFIFOLink {
        read {
            assert $variable.enabled;
            await Len($variable.queue) > 0;
            with (msg = Head($variable.queue)) {
                $variable.queue := Tail($variable.queue);
                yield msg;
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

    archetype AProxy(ref net[_], ref fd[_])
    variables
        msg, proxyMsg, idx, resp, proxyResp;
    {
    proxyLoop:
        while(TRUE) {
        rcvMsgFromClient:
            msg := net[<<ProxyID, REQ_MSG_TYP>>];

        proxyMsg:
            assert(msg.to = ProxyID /\ msg.typ = REQ_MSG_TYP);
            proxyResp := [from |-> ProxyID, to |-> msg.from, body |-> FAIL,
                          id |-> msg.id, typ |-> PROXY_RESP_MSG_TYP];
            idx := 1;
            serversLoop:
                while (idx <= NUM_SERVERS) {
                proxySendMsg:
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
                        proxyResp := net[<<ProxyID, PROXY_RESP_MSG_TYP>>];
                        assert(
                            /\ proxyResp.to = ProxyID
                            /\ proxyResp.from = idx
                            /\ proxyResp.id = msg.id
                            /\ proxyResp.typ = PROXY_RESP_MSG_TYP
                        );
                        goto sendMsgToClient;
                    } or {
                        await fd[idx];
                        idx := idx + 1;
                    };
                };

        sendMsgToClient:
            resp := [from |-> ProxyID, to |-> msg.from, body |-> proxyResp.body,
                     id |-> proxyResp.id, typ |-> RESP_MSG_TYP];
            net[<<resp.to, resp.typ>>] := resp;
        };
    }

    archetype AServer(ref net[_], ref netEnabled[_], ref fd[_])
    variables
        msg, resp;
    {
    serverLoop:
        while (TRUE) {
            if (EXPLORE_FAIL) {
                either { skip; } or {
                    netEnabled[self] := FALSE;
                    goto failLabel;
                };
            };

        serverRcvMsg:
            msg := net[<<self, PROXY_REQ_MSG_TYP>>];
            assert(
                /\ msg.to = self
                /\ msg.from = ProxyID
                /\ msg.typ = PROXY_REQ_MSG_TYP
            );
            if (EXPLORE_FAIL) {
                either { skip; } or {
                    netEnabled[self] := FALSE;
                    goto failLabel;
                };
            };

        serverSendMsg:
            resp := [from |-> self, to |-> msg.from, body |-> self,
                     id |-> msg.id, typ |-> PROXY_RESP_MSG_TYP];
            net[<<resp.to, resp.typ>>] := resp;
            if (EXPLORE_FAIL) {
                either { skip; } or {
                    netEnabled[self] := FALSE;
                    goto failLabel;
                };
            };
        };

    failLabel:
        fd[self] := TRUE;
    }

    archetype AClient(ref net[_])
    variables
        req, resp;
    {
    clientLoop:
        while (TRUE) {
        clientSendReq:
            req := [from |-> self, to |-> ProxyID, body |-> self,
                    id |-> 0, typ |-> REQ_MSG_TYP];
            net[<<req.to, req.typ>>] := req;
            print <<"CLIENT START", req>>;

        clientRcvResp:
            resp := net[<<self, RESP_MSG_TYP>>];
            assert(
                /\ resp.to = self
                /\ resp.id = 0
                /\ resp.typ = RESP_MSG_TYP
            );
            print <<"CLIENT RESP", resp>>;
        }
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> [queue |-> <<>>, enabled |-> TRUE]];
        fd = [id \in NODE_SET |-> FALSE];

    fair process (Proxy = ProxyID) == instance AProxy(ref network[_], ref fd[_])
        mapping network[_] via ReliableFIFOLink
        mapping fd[_] via PerfectFD;

    fair process (Server \in SERVER_SET) == instance AServer(ref network[_], ref network[_], ref fd[_])
        mapping @1[_] via ReliableFIFOLink
        mapping @2[_] via NetworkToggle
        mapping @3[_] via PerfectFD;

    fair process (Client \in CLIENT_SET) == instance AClient(ref network[_])
        mapping network[_] via ReliableFIFOLink;
}







\* BEGIN PLUSCAL TRANSLATION
--algorithm proxy {
  variables network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> [queue |-> <<>>, enabled |-> TRUE]]; fd = [id \in NODE_SET |-> FALSE];
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
  }

  fair process (Proxy = ProxyID)
    variables msg; proxyMsg; idx; resp; proxyResp;
  {
    proxyLoop:
      if(TRUE) {
        goto rcvMsgFromClient;
      } else {
        goto Done;
      };
    rcvMsgFromClient:
      assert ((network)[<<ProxyID, REQ_MSG_TYP>>]).enabled;
      await (Len(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)) > (0);
      with (msg0 = Head(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)) {
        network := [network EXCEPT !["queue"][<<ProxyID, REQ_MSG_TYP>>] = Tail(((network)[<<ProxyID, REQ_MSG_TYP>>]).queue)];
        with (yielded_net3 = msg0) {
          msg := yielded_net3;
          goto proxyMsg;
        };
      };
    proxyMsg:
      assert (((msg).to) = (ProxyID)) /\ (((msg).typ) = (REQ_MSG_TYP));
      proxyResp := [from |-> ProxyID, to |-> (msg).from, body |-> FAIL, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
      idx := 1;
      goto serversLoop;
    serversLoop:
      if((idx) <= (NUM_SERVERS)) {
        goto proxySendMsg;
      } else {
        goto sendMsgToClient;
      };
    proxySendMsg:
      either {
        proxyMsg := [from |-> ProxyID, to |-> idx, body |-> (msg).body, id |-> (msg).id, typ |-> PROXY_REQ_MSG_TYP];
        with (value7 = proxyMsg) {
          await ((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).enabled;
          network := [network EXCEPT ![<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>] = [queue |-> Append(((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).queue, value7), enabled |-> ((network)[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>]).enabled]];
          goto proxyRcvMsg;
        };
      } or {
        with (yielded_fd1 = (fd)[idx]) {
          await yielded_fd1;
          idx := (idx) + (1);
          goto serversLoop;
        };
      };
    proxyRcvMsg:
      either {
        assert ((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).enabled;
        await (Len(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)) > (0);
        with (msg1 = Head(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)) {
          network := [network EXCEPT !["queue"][<<ProxyID, PROXY_RESP_MSG_TYP>>] = Tail(((network)[<<ProxyID, PROXY_RESP_MSG_TYP>>]).queue)];
          with (yielded_net00 = msg1) {
            proxyResp := yielded_net00;
            assert (((((proxyResp).to) = (ProxyID)) /\ (((proxyResp).from) = (idx))) /\ (((proxyResp).id) = ((msg).id))) /\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP));
            goto sendMsgToClient;
          };
        };
      } or {
        with (yielded_fd00 = (fd)[idx]) {
          await yielded_fd00;
          idx := (idx) + (1);
          goto serversLoop;
        };
      };
    sendMsgToClient:
      resp := [from |-> ProxyID, to |-> (msg).from, body |-> (proxyResp).body, id |-> (proxyResp).id, typ |-> RESP_MSG_TYP];
      with (value00 = resp) {
        await ((network)[<<(resp).to, (resp).typ>>]).enabled;
        network := [network EXCEPT ![<<(resp).to, (resp).typ>>] = [queue |-> Append(((network)[<<(resp).to, (resp).typ>>]).queue, value00), enabled |-> ((network)[<<(resp).to, (resp).typ>>]).enabled]];
        goto proxyLoop;
      };
  }

  fair process (Server \in SERVER_SET)
    variables msg; resp;
  {
    serverLoop:
      if(TRUE) {
        if(EXPLORE_FAIL) {
          either {
            skip;
            goto serverRcvMsg;
          } or {
            with (value10 = FALSE) {
              network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value10]];
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
      with (msg2 = Head(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue)) {
        network := [network EXCEPT !["queue"][<<self, PROXY_REQ_MSG_TYP>>] = Tail(((network)[<<self, PROXY_REQ_MSG_TYP>>]).queue)];
        with (yielded_net10 = msg2) {
          msg := yielded_net10;
          assert ((((msg).to) = (self)) /\ (((msg).from) = (ProxyID))) /\ (((msg).typ) = (PROXY_REQ_MSG_TYP));
          if(EXPLORE_FAIL) {
            either {
              skip;
              goto serverSendMsg;
            } or {
              with (value20 = FALSE) {
                network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value20]];
                goto failLabel;
              };
            };
          } else {
            goto serverSendMsg;
          };
        };
      };
    serverSendMsg:
      resp := [from |-> self, to |-> (msg).from, body |-> self, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
      with (value30 = resp) {
        await ((network)[<<(resp).to, (resp).typ>>]).enabled;
        network := [network EXCEPT ![<<(resp).to, (resp).typ>>] = [queue |-> Append(((network)[<<(resp).to, (resp).typ>>]).queue, value30), enabled |-> ((network)[<<(resp).to, (resp).typ>>]).enabled]];
        if(EXPLORE_FAIL) {
          either {
            skip;
            goto serverLoop;
          } or {
            with (value40 = FALSE) {
              network := [network EXCEPT ![self] = [queue |-> ((network)[self]).queue, enabled |-> value40]];
              goto failLabel;
            };
          };
        } else {
          goto serverLoop;
        };
      };
    failLabel:
      with (value50 = TRUE) {
        fd := [fd EXCEPT ![self] = value50];
        goto Done;
      };
  }

  fair process (Client \in CLIENT_SET)
    variables req; resp;
  {
    clientLoop:
      if(TRUE) {
        goto clientSendReq;
      } else {
        goto Done;
      };
    clientSendReq:
      req := [from |-> self, to |-> ProxyID, body |-> self, id |-> 0, typ |-> REQ_MSG_TYP];
      with (value60 = req) {
        await ((network)[<<(req).to, (req).typ>>]).enabled;
        network := [network EXCEPT ![<<(req).to, (req).typ>>] = [queue |-> Append(((network)[<<(req).to, (req).typ>>]).queue, value60), enabled |-> ((network)[<<(req).to, (req).typ>>]).enabled]];
        print <<"CLIENT START", req>>;
        goto clientRcvResp;
      };
    clientRcvResp:
      assert ((network)[<<self, RESP_MSG_TYP>>]).enabled;
      await (Len(((network)[<<self, RESP_MSG_TYP>>]).queue)) > (0);
      with (msg3 = Head(((network)[<<self, RESP_MSG_TYP>>]).queue)) {
        network := [network EXCEPT !["queue"][<<self, RESP_MSG_TYP>>] = Tail(((network)[<<self, RESP_MSG_TYP>>]).queue)];
        with (yielded_net20 = msg3) {
          resp := yielded_net20;
          assert ((((resp).to) = (self)) /\ (((resp).id) = (0))) /\ (((resp).typ) = (RESP_MSG_TYP));
          print <<"CLIENT RESP", resp>>;
          goto clientLoop;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION


********************)

\* BEGIN TRANSLATION

\* END TRANSLATION

\* Invariants

\* Properties

\* ReceiveResp(client) == pc[client] = "clientSendReq" ~> pc[client] = "clientRcvResp"
\* ClientsOK == \A client \in CLIENT_SET : ReceiveResp(client)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:47:39 PDT 2021 by shayan
\* Created Wed Jun 30 19:19:46 PDT 2021 by shayan