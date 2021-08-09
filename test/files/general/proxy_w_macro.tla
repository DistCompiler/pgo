------------------------------- MODULE proxy_w_macro -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

\* CONSTANT BUFFER_SIZE
CONSTANT NUM_SERVERS
CONSTANT NUM_CLIENTS
CONSTANT EXPLORE_FAIL
CONSTANT F

ASSUME NUM_SERVERS > 0 /\ NUM_CLIENTS > 0

(********************

--mpcal proxy_w_macro {
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

    macro mayFail(selfID, netEnabled) {
        if (EXPLORE_FAIL) {
            either { skip; } or {
                netEnabled[selfID] := FALSE;
                goto failLabel;
            };
        };
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

--algorithm Proxy1 {
    variables network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> <<>>], fd = [id \in NODE_SET |-> TRUE], netRead, netWrite, netWrite0, netWrite1, netWrite2, netWrite3, netRead0, netWrite4, netWrite5, netWrite6, netRead1;
    define {
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
    variables msg, proxyMsg, idx, resp, proxyResp;
    {
        proxyLoop:
            if (TRUE) {
                rcvMsgFromClient:
                    await (Len(network[<<ProxyID, REQ_MSG_TYP>>])) > (0);
                    with (msg0 = Head(network[<<ProxyID, REQ_MSG_TYP>>])) {
                        netWrite := [network EXCEPT ![<<ProxyID, REQ_MSG_TYP>>] = Tail(network[<<ProxyID, REQ_MSG_TYP>>])];
                        netRead := msg0;
                    };
                    msg := netRead;
                    network := netWrite;

                proxyMsg:
                    assert (((msg).to) = (ProxyID)) /\ (((msg).typ) = (REQ_MSG_TYP));
                    proxyResp := [from |-> ProxyID, to |-> (msg).from, body |-> FAIL, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
                    idx := 1;

                serversLoop:
                    if ((idx) <= (NUM_SERVERS)) {
                        proxySendMsg:
                            either {
                                proxyMsg := [from |-> ProxyID, to |-> idx, body |-> (msg).body, id |-> (msg).id, typ |-> PROXY_REQ_MSG_TYP];
                                await (Len(network[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>])) < (BUFFER_SIZE);
                                netWrite := [network EXCEPT ![<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>] = Append(network[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>], proxyMsg)];
                                netWrite0 := netWrite;
                                network := netWrite0;
                            } or {
                                idx := (idx) + (1);
                                netWrite0 := network;
                                network := netWrite0;
                                goto serversLoop;
                            };

                        proxyRcvMsg:
                            either {
                                await (Len(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) > (0);
                                with (msg1 = Head(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) {
                                    netWrite := [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = Tail(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])];
                                    netRead := msg1;
                                };
                                proxyResp := netRead;
                                await ((proxyResp).from) = (idx);
                                assert (((((proxyResp).to) = (ProxyID)) /\ (((proxyResp).from) = (idx))) /\ (((proxyResp).id) = ((msg).id))) /\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP));
                                netWrite1 := netWrite;
                                network := netWrite1;
                                goto sendMsgToClient;
                            } or {
                                idx := (idx) + (1);
                                netWrite1 := network;
                                network := netWrite1;
                                goto serversLoop;
                            };

                    } else {
                        netWrite2 := network;
                        network := netWrite2;
                    };

                sendMsgToClient:
                    resp := [from |-> ProxyID, to |-> (msg).from, body |-> (proxyResp).body, id |-> (proxyResp).id, typ |-> RESP_MSG_TYP];
                    await (Len(network[<<(resp).to, (resp).typ>>])) < (BUFFER_SIZE);
                    netWrite := [network EXCEPT ![<<(resp).to, (resp).typ>>] = Append(network[<<(resp).to, (resp).typ>>], resp)];
                    network := netWrite;
                    goto proxyLoop;

            } else {
                netWrite3 := network;
                network := netWrite3;
            };

    }
    fair process (Server \in SERVER_SET)
    variables msg, resp;
    {
        serverLoop:
            if (TRUE) {
                if (EXPLORE_FAIL) {
                    either {
                        skip;
                    } or {
                        goto failLabel;
                    };
                };
                serverRcvMsg:
                    await (Len(network[<<self, PROXY_REQ_MSG_TYP>>])) > (0);
                    with (msg2 = Head(network[<<self, PROXY_REQ_MSG_TYP>>])) {
                        netWrite4 := [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = Tail(network[<<self, PROXY_REQ_MSG_TYP>>])];
                        netRead0 := msg2;
                    };
                    msg := netRead0;
                    assert ((((msg).to) = (self)) /\ (((msg).from) = (ProxyID))) /\ (((msg).typ) = (PROXY_REQ_MSG_TYP));
                    if (EXPLORE_FAIL) {
                        either {
                            network := netWrite4;
                        } or {
                            network := netWrite4;
                            goto failLabel;
                        };
                    } else {
                        network := netWrite4;
                    };

                serverSendMsg:
                    resp := [from |-> self, to |-> (msg).from, body |-> self, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
                    await (Len(network[<<(resp).to, (resp).typ>>])) < (BUFFER_SIZE);
                    netWrite4 := [network EXCEPT ![<<(resp).to, (resp).typ>>] = Append(network[<<(resp).to, (resp).typ>>], resp)];
                    if (EXPLORE_FAIL) {
                        either {
                            network := netWrite4;
                            goto serverLoop;
                        } or {
                            network := netWrite4;
                            goto failLabel;
                        };
                    } else {
                        network := netWrite4;
                        goto serverLoop;
                    };

            } else {
                netWrite5 := network;
                network := netWrite5;
            };
        failLabel:
            skip;

    }
    fair process (Client \in CLIENT_SET)
    variables req, resp;
    {
        clientSendReq:
            req := [from |-> self, to |-> ProxyID, body |-> self, id |-> 0, typ |-> REQ_MSG_TYP];
            await (Len(network[<<(req).to, (req).typ>>])) < (BUFFER_SIZE);
            netWrite6 := [network EXCEPT ![<<(req).to, (req).typ>>] = Append(network[<<(req).to, (req).typ>>], req)];
            network := netWrite6;
        clientRcvResp:
            await (Len(network[<<self, RESP_MSG_TYP>>])) > (0);
            with (msg3 = Head(network[<<self, RESP_MSG_TYP>>])) {
                netWrite6 := [network EXCEPT ![<<self, RESP_MSG_TYP>>] = Tail(network[<<self, RESP_MSG_TYP>>])];
                netRead1 := msg3;
            };
            resp := netRead1;
            assert ((((resp).to) = (self)) /\ (((resp).id) = (0))) /\ (((resp).typ) = (RESP_MSG_TYP));
            network := netWrite6;

    }
}
\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "ba6cf426" /\ chksum(tla) = "3fa8c3b5")
\* Label proxyMsg of process Proxy at line 199 col 21 changed to proxyMsg_
\* Process variable msg of process Proxy at line 185 col 15 changed to msg_
\* Process variable resp of process Proxy at line 185 col 35 changed to resp_
\* Process variable resp of process Server at line 258 col 20 changed to resp_S
CONSTANT defaultInitValue
VARIABLES network, fd, netRead, netWrite, netWrite0, netWrite1, netWrite2,
          netWrite3, netRead0, netWrite4, netWrite5, netWrite6, netRead1, pc

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

VARIABLES msg_, proxyMsg, idx, resp_, proxyResp, msg, resp_S, req, resp

vars == << network, fd, netRead, netWrite, netWrite0, netWrite1, netWrite2,
           netWrite3, netRead0, netWrite4, netWrite5, netWrite6, netRead1, pc,
           msg_, proxyMsg, idx, resp_, proxyResp, msg, resp_S, req, resp >>

ProcSet == {ProxyID} \cup (SERVER_SET) \cup (CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> <<>>]
        /\ fd = [id \in NODE_SET |-> TRUE]
        /\ netRead = defaultInitValue
        /\ netWrite = defaultInitValue
        /\ netWrite0 = defaultInitValue
        /\ netWrite1 = defaultInitValue
        /\ netWrite2 = defaultInitValue
        /\ netWrite3 = defaultInitValue
        /\ netRead0 = defaultInitValue
        /\ netWrite4 = defaultInitValue
        /\ netWrite5 = defaultInitValue
        /\ netWrite6 = defaultInitValue
        /\ netRead1 = defaultInitValue
        (* Process Proxy *)
        /\ msg_ = defaultInitValue
        /\ proxyMsg = defaultInitValue
        /\ idx = defaultInitValue
        /\ resp_ = defaultInitValue
        /\ proxyResp = defaultInitValue
        (* Process Server *)
        /\ msg = [self \in SERVER_SET |-> defaultInitValue]
        /\ resp_S = [self \in SERVER_SET |-> defaultInitValue]
        (* Process Client *)
        /\ req = [self \in CLIENT_SET |-> defaultInitValue]
        /\ resp = [self \in CLIENT_SET |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = ProxyID -> "proxyLoop"
                                        [] self \in SERVER_SET -> "serverLoop"
                                        [] self \in CLIENT_SET -> "clientSendReq"]

proxyLoop == /\ pc[ProxyID] = "proxyLoop"
             /\ IF TRUE
                   THEN /\ pc' = [pc EXCEPT ![ProxyID] = "rcvMsgFromClient"]
                        /\ UNCHANGED << network, netWrite3 >>
                   ELSE /\ netWrite3' = network
                        /\ network' = netWrite3'
                        /\ pc' = [pc EXCEPT ![ProxyID] = "Done"]
             /\ UNCHANGED << fd, netRead, netWrite, netWrite0, netWrite1,
                             netWrite2, netRead0, netWrite4, netWrite5,
                             netWrite6, netRead1, msg_, proxyMsg, idx, resp_,
                             proxyResp, msg, resp_S, req, resp >>

rcvMsgFromClient == /\ pc[ProxyID] = "rcvMsgFromClient"
                    /\ (Len(network[<<ProxyID, REQ_MSG_TYP>>])) > (0)
                    /\ LET msg0 == Head(network[<<ProxyID, REQ_MSG_TYP>>]) IN
                         /\ netWrite' = [network EXCEPT ![<<ProxyID, REQ_MSG_TYP>>] = Tail(network[<<ProxyID, REQ_MSG_TYP>>])]
                         /\ netRead' = msg0
                    /\ msg_' = netRead'
                    /\ network' = netWrite'
                    /\ pc' = [pc EXCEPT ![ProxyID] = "proxyMsg_"]
                    /\ UNCHANGED << fd, netWrite0, netWrite1, netWrite2,
                                    netWrite3, netRead0, netWrite4, netWrite5,
                                    netWrite6, netRead1, proxyMsg, idx, resp_,
                                    proxyResp, msg, resp_S, req, resp >>

proxyMsg_ == /\ pc[ProxyID] = "proxyMsg_"
             /\ Assert((((msg_).to) = (ProxyID)) /\ (((msg_).typ) = (REQ_MSG_TYP)),
                       "Failure of assertion at line 199, column 21.")
             /\ proxyResp' = [from |-> ProxyID, to |-> (msg_).from, body |-> FAIL, id |-> (msg_).id, typ |-> PROXY_RESP_MSG_TYP]
             /\ idx' = 1
             /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
             /\ UNCHANGED << network, fd, netRead, netWrite, netWrite0,
                             netWrite1, netWrite2, netWrite3, netRead0,
                             netWrite4, netWrite5, netWrite6, netRead1, msg_,
                             proxyMsg, resp_, msg, resp_S, req, resp >>

serversLoop == /\ pc[ProxyID] = "serversLoop"
               /\ IF (idx) <= (NUM_SERVERS)
                     THEN /\ pc' = [pc EXCEPT ![ProxyID] = "proxySendMsg"]
                          /\ UNCHANGED << network, netWrite2 >>
                     ELSE /\ netWrite2' = network
                          /\ network' = netWrite2'
                          /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
               /\ UNCHANGED << fd, netRead, netWrite, netWrite0, netWrite1,
                               netWrite3, netRead0, netWrite4, netWrite5,
                               netWrite6, netRead1, msg_, proxyMsg, idx, resp_,
                               proxyResp, msg, resp_S, req, resp >>

proxySendMsg == /\ pc[ProxyID] = "proxySendMsg"
                /\ \/ /\ proxyMsg' = [from |-> ProxyID, to |-> idx, body |-> (msg_).body, id |-> (msg_).id, typ |-> PROXY_REQ_MSG_TYP]
                      /\ (Len(network[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>])) < (BUFFER_SIZE)
                      /\ netWrite' = [network EXCEPT ![<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>] = Append(network[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>], proxyMsg')]
                      /\ netWrite0' = netWrite'
                      /\ network' = netWrite0'
                      /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsg"]
                      /\ idx' = idx
                   \/ /\ idx' = (idx) + (1)
                      /\ netWrite0' = network
                      /\ network' = netWrite0'
                      /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                      /\ UNCHANGED <<netWrite, proxyMsg>>
                /\ UNCHANGED << fd, netRead, netWrite1, netWrite2, netWrite3,
                                netRead0, netWrite4, netWrite5, netWrite6,
                                netRead1, msg_, resp_, proxyResp, msg, resp_S,
                                req, resp >>

proxyRcvMsg == /\ pc[ProxyID] = "proxyRcvMsg"
               /\ \/ /\ (Len(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) > (0)
                     /\ LET msg1 == Head(network[<<ProxyID, PROXY_RESP_MSG_TYP>>]) IN
                          /\ netWrite' = [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = Tail(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])]
                          /\ netRead' = msg1
                     /\ proxyResp' = netRead'
                     /\ ((proxyResp').from) = (idx)
                     /\ Assert((((((proxyResp').to) = (ProxyID)) /\ (((proxyResp').from) = (idx))) /\ (((proxyResp').id) = ((msg_).id))) /\ (((proxyResp').typ) = (PROXY_RESP_MSG_TYP)),
                               "Failure of assertion at line 228, column 33.")
                     /\ netWrite1' = netWrite'
                     /\ network' = netWrite1'
                     /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
                     /\ idx' = idx
                  \/ /\ idx' = (idx) + (1)
                     /\ netWrite1' = network
                     /\ network' = netWrite1'
                     /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                     /\ UNCHANGED <<netRead, netWrite, proxyResp>>
               /\ UNCHANGED << fd, netWrite0, netWrite2, netWrite3, netRead0,
                               netWrite4, netWrite5, netWrite6, netRead1, msg_,
                               proxyMsg, resp_, msg, resp_S, req, resp >>

sendMsgToClient == /\ pc[ProxyID] = "sendMsgToClient"
                   /\ resp_' = [from |-> ProxyID, to |-> (msg_).from, body |-> (proxyResp).body, id |-> (proxyResp).id, typ |-> RESP_MSG_TYP]
                   /\ (Len(network[<<(resp_').to, (resp_').typ>>])) < (BUFFER_SIZE)
                   /\ netWrite' = [network EXCEPT ![<<(resp_').to, (resp_').typ>>] = Append(network[<<(resp_').to, (resp_').typ>>], resp_')]
                   /\ network' = netWrite'
                   /\ pc' = [pc EXCEPT ![ProxyID] = "proxyLoop"]
                   /\ UNCHANGED << fd, netRead, netWrite0, netWrite1,
                                   netWrite2, netWrite3, netRead0, netWrite4,
                                   netWrite5, netWrite6, netRead1, msg_,
                                   proxyMsg, idx, proxyResp, msg, resp_S, req,
                                   resp >>

Proxy == proxyLoop \/ rcvMsgFromClient \/ proxyMsg_ \/ serversLoop
            \/ proxySendMsg \/ proxyRcvMsg \/ sendMsgToClient

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ IF EXPLORE_FAIL
                                     THEN /\ \/ /\ TRUE
                                                /\ pc' = [pc EXCEPT ![self] = "serverRcvMsg"]
                                             \/ /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverRcvMsg"]
                               /\ UNCHANGED << network, netWrite5 >>
                          ELSE /\ netWrite5' = network
                               /\ network' = netWrite5'
                               /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                    /\ UNCHANGED << fd, netRead, netWrite, netWrite0,
                                    netWrite1, netWrite2, netWrite3, netRead0,
                                    netWrite4, netWrite6, netRead1, msg_,
                                    proxyMsg, idx, resp_, proxyResp, msg,
                                    resp_S, req, resp >>

serverRcvMsg(self) == /\ pc[self] = "serverRcvMsg"
                      /\ (Len(network[<<self, PROXY_REQ_MSG_TYP>>])) > (0)
                      /\ LET msg2 == Head(network[<<self, PROXY_REQ_MSG_TYP>>]) IN
                           /\ netWrite4' = [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = Tail(network[<<self, PROXY_REQ_MSG_TYP>>])]
                           /\ netRead0' = msg2
                      /\ msg' = [msg EXCEPT ![self] = netRead0']
                      /\ Assert(((((msg'[self]).to) = (self)) /\ (((msg'[self]).from) = (ProxyID))) /\ (((msg'[self]).typ) = (PROXY_REQ_MSG_TYP)),
                                "Failure of assertion at line 276, column 21.")
                      /\ IF EXPLORE_FAIL
                            THEN /\ \/ /\ network' = netWrite4'
                                       /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                                    \/ /\ network' = netWrite4'
                                       /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                            ELSE /\ network' = netWrite4'
                                 /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                      /\ UNCHANGED << fd, netRead, netWrite, netWrite0,
                                      netWrite1, netWrite2, netWrite3,
                                      netWrite5, netWrite6, netRead1, msg_,
                                      proxyMsg, idx, resp_, proxyResp, resp_S,
                                      req, resp >>

serverSendMsg(self) == /\ pc[self] = "serverSendMsg"
                       /\ resp_S' = [resp_S EXCEPT ![self] = [from |-> self, to |-> (msg[self]).from, body |-> self, id |-> (msg[self]).id, typ |-> PROXY_RESP_MSG_TYP]]
                       /\ (Len(network[<<(resp_S'[self]).to, (resp_S'[self]).typ>>])) < (BUFFER_SIZE)
                       /\ netWrite4' = [network EXCEPT ![<<(resp_S'[self]).to, (resp_S'[self]).typ>>] = Append(network[<<(resp_S'[self]).to, (resp_S'[self]).typ>>], resp_S'[self])]
                       /\ IF EXPLORE_FAIL
                             THEN /\ \/ /\ network' = netWrite4'
                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                     \/ /\ network' = netWrite4'
                                        /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                             ELSE /\ network' = netWrite4'
                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                       /\ UNCHANGED << fd, netRead, netWrite, netWrite0,
                                       netWrite1, netWrite2, netWrite3,
                                       netRead0, netWrite5, netWrite6,
                                       netRead1, msg_, proxyMsg, idx, resp_,
                                       proxyResp, msg, req, resp >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << network, fd, netRead, netWrite, netWrite0,
                                   netWrite1, netWrite2, netWrite3, netRead0,
                                   netWrite4, netWrite5, netWrite6, netRead1,
                                   msg_, proxyMsg, idx, resp_, proxyResp, msg,
                                   resp_S, req, resp >>

Server(self) == serverLoop(self) \/ serverRcvMsg(self)
                   \/ serverSendMsg(self) \/ failLabel(self)

clientSendReq(self) == /\ pc[self] = "clientSendReq"
                       /\ req' = [req EXCEPT ![self] = [from |-> self, to |-> ProxyID, body |-> self, id |-> 0, typ |-> REQ_MSG_TYP]]
                       /\ (Len(network[<<(req'[self]).to, (req'[self]).typ>>])) < (BUFFER_SIZE)
                       /\ netWrite6' = [network EXCEPT ![<<(req'[self]).to, (req'[self]).typ>>] = Append(network[<<(req'[self]).to, (req'[self]).typ>>], req'[self])]
                       /\ network' = netWrite6'
                       /\ pc' = [pc EXCEPT ![self] = "clientRcvResp"]
                       /\ UNCHANGED << fd, netRead, netWrite, netWrite0,
                                       netWrite1, netWrite2, netWrite3,
                                       netRead0, netWrite4, netWrite5,
                                       netRead1, msg_, proxyMsg, idx, resp_,
                                       proxyResp, msg, resp_S, resp >>

clientRcvResp(self) == /\ pc[self] = "clientRcvResp"
                       /\ (Len(network[<<self, RESP_MSG_TYP>>])) > (0)
                       /\ LET msg3 == Head(network[<<self, RESP_MSG_TYP>>]) IN
                            /\ netWrite6' = [network EXCEPT ![<<self, RESP_MSG_TYP>>] = Tail(network[<<self, RESP_MSG_TYP>>])]
                            /\ netRead1' = msg3
                       /\ resp' = [resp EXCEPT ![self] = netRead1']
                       /\ Assert(((((resp'[self]).to) = (self)) /\ (((resp'[self]).id) = (0))) /\ (((resp'[self]).typ) = (RESP_MSG_TYP)),
                                 "Failure of assertion at line 328, column 13.")
                       /\ network' = netWrite6'
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << fd, netRead, netWrite, netWrite0,
                                       netWrite1, netWrite2, netWrite3,
                                       netRead0, netWrite4, netWrite5, msg_,
                                       proxyMsg, idx, resp_, proxyResp, msg,
                                       resp_S, req >>

Client(self) == clientSendReq(self) \/ clientRcvResp(self)

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

\* BufferOK(node, typ) == Len(network[node, typ]) >= 0 /\ Len(network[node, typ]) <= BUFFER_SIZE
\* BuffersOK == \A <<node, typ>> \in DOMAIN network : BufferOK(node, typ)

\* Properties

ReceiveResp(client) == pc[client] = "clientSendReq" ~> pc[client] = "clientRcvResp"
ClientsOK == \A client \in CLIENT_SET : ReceiveResp(client)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:29:38 PDT 2021 by shayan
\* Created Wed Jun 30 19:19:46 PDT 2021 by shayan