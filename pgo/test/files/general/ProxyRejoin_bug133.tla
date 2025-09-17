------------------------------ MODULE ProxyRejoin ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT BUFFER_SIZE
CONSTANT NUM_SERVERS
CONSTANT NUM_CLIENTS
CONSTANT EXPLORE_FAIL
CONSTANT EXPLORE_REJOIN
CONSTANT F

ASSUME NUM_SERVERS > 0 /\ NUM_CLIENTS > 0

(************************
--mpcal ProxyRejoin {

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

    macro mayFail(self, fd) {
        if (EXPLORE_FAIL = TRUE) {
            assert(fd[self] = TRUE);
            either {
                skip;
            } or {
                fd[self] := FALSE;
                goto fLabel;
            };
        };
    }

    macro mayRejoin(self, fd) {
        if (EXPLORE_REJOIN = TRUE) {
            assert(fd[self] = FALSE);
            either {
                skip;
            } or {
                fd[self] := TRUE;
                goto serverLoop;
            };
        };
    }

    mapping macro TCPChannel {
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

    archetype AProxy(ref net)
    variables
        msg, proxyResp, proxyMsg, idx, resp, tmp;
    {
        proxyLoop:
            while (TRUE) {
                rcvMsgFromClient:
                    msg := net[<<ProxyID, REQ_MSG_TYP>>];

                proxyMsg:
                    assert(msg.to = ProxyID);
                    assert(msg.typ = REQ_MSG_TYP);
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
                                    idx := idx + 1;
                                    goto serversLoop;
                                };

                            proxyRcvMsg:
                                either {
                                    tmp := net[<<ProxyID, PROXY_RESP_MSG_TYP>>];
                                    if (tmp.from # idx) {
                                        goto proxyRcvMsg;
                                    };
                                    proxyRcvMsgAsserts:
                                        proxyResp := tmp;
                                        assert(proxyResp.to = ProxyID);
                                        assert(proxyResp.from = idx);
                                        assert(proxyResp.id = msg.id);
                                        assert(proxyResp.typ = PROXY_RESP_MSG_TYP);
                                        goto sendMsgToClient;
                                } or {
                                    idx := idx + 1;
                                };
                        };

                sendMsgToClient:
                    resp := [from |-> ProxyID, to |-> msg.from, body |-> proxyResp.body,
                             id |-> proxyResp.id, typ |-> RESP_MSG_TYP];
                    net[<<resp.to, resp.typ>>] := resp;
            };
    }

    archetype AServer(ref net, ref fd)
    variables
        msg, resp;
    {
        serverLoop:
            while (TRUE) {
                mayFail(self, fd);

                serverRcvMsg:
                    msg := net[<<self, PROXY_REQ_MSG_TYP>>];
                    assert(msg.to = self);
                    assert(msg.from = ProxyID);
                    assert(msg.typ = PROXY_REQ_MSG_TYP);
                    mayFail(self, fd);

                serverSendMsg:
                    resp := [from |-> self, to |-> msg.from, body |-> self,
                             id |-> msg.id, typ |-> PROXY_RESP_MSG_TYP];
                    net[<<resp.to, resp.typ>>] := resp;
                    mayFail(self, fd);
            };

        failLabel:
            mayRejoin(self, fd);
    }

    archetype AClient(ref net)
    variables
        req, resp;
    {
        clientLoop:
            while (TRUE) {
                clientSendReq:
                    req := [from |-> self, to |-> ProxyID, body |-> self,
                            id |-> 0, typ |-> REQ_MSG_TYP];
                    print <<"CLIENT START", req>>;
                    net[<<req.to, req.typ>>] := req;

                clientRcvResp:
                    resp := net[<<self, RESP_MSG_TYP>>];
                    assert(resp.to = self);
                    assert(resp.id = 0);
                    assert(resp.typ = RESP_MSG_TYP);
                    print <<"CLIENT RESP", resp>>;
            }
    }

    variables
        network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> <<>>];
        fd = [id \in NODE_SET |-> TRUE];

    fair process (Proxy = ProxyID) == instance AProxy(ref network)
        mapping network[_] via TCPChannel
        mapping (*:: expectedError: MappingLookupError *) fd[_] via FailureDetector;

    fair process (Server \in SERVER_SET) == instance AServer(ref network, ref fd)
        mapping network[_] via TCPChannel
        mapping fd[_] via FailureDetector;

    fair process (Client \in CLIENT_SET) == instance AClient(ref network)
        mapping network[_] via TCPChannel;

}

\* BEGIN PLUSCAL TRANSLATION

--algorithm ProxyNewIdea {
    variables network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> <<>>], fd = [id \in NODE_SET |-> TRUE], netRead, netWrite, fdRead, netWrite0, netWrite1, netWrite2, netWrite3, netRead0, netWrite4, fdRead0, fdWrite, fdWrite0, fdWrite1, fdWrite2, fdWrite3, netWrite5, fdWrite4, fdWrite5, fdWrite6, netWrite6, netRead1, netWrite7;
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
    variables msg, proxyResp, proxyMsg, idx, resp, tmp;
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
                    assert ((msg).to) = (ProxyID);
                    assert ((msg).typ) = (REQ_MSG_TYP);
                    proxyResp := [from |-> ProxyID, to |-> (msg).from, body |-> FAIL, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
                    idx := 1;

                serversLoop:
                    if ((idx) <= (NUM_SERVERS)) {
                        proxySendMsg:
                            fdRead := fd[idx];
                            if ((fdRead) = (TRUE)) {
                                proxyMsg := [from |-> ProxyID, to |-> idx, body |-> (msg).body, id |-> (msg).id, typ |-> PROXY_REQ_MSG_TYP];
                                await (Len(network[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>])) < (BUFFER_SIZE);
                                netWrite := [network EXCEPT ![<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>] = Append(network[<<(proxyMsg).to, PROXY_REQ_MSG_TYP>>], proxyMsg)];
                                netWrite0 := netWrite;
                                network := netWrite0;
                            } else {
                                idx := (idx) + (1);
                                netWrite0 := network;
                                network := netWrite0;
                                goto serversLoop;
                            };

                        proxyRcvMsg:
                            fdRead := fd[idx];
                            if ((fdRead) = (TRUE)) {
                                await (Len(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) > (0);
                                with (msg1 = Head(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) {
                                    netWrite := [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = Tail(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])];
                                    netRead := msg1;
                                };
                                tmp := netRead;
                                if (((tmp).from) # (idx)) {
                                    network := netWrite;
                                    goto proxyRcvMsg;
                                } else {
                                    network := netWrite;
                                };
                                proxyRcvMsgAsserts:
                                    proxyResp := tmp;
                                    assert ((proxyResp).to) = (ProxyID);
                                    assert ((proxyResp).from) = (idx);
                                    assert ((proxyResp).id) = ((msg).id);
                                    assert ((proxyResp).typ) = (PROXY_RESP_MSG_TYP);
                                    goto sendMsgToClient;

                            } else {
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
                serverRcvMsg:
                    await (Len(network[<<self, PROXY_REQ_MSG_TYP>>])) > (0);
                    with (msg2 = Head(network[<<self, PROXY_REQ_MSG_TYP>>])) {
                        netWrite4 := [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = Tail(network[<<self, PROXY_REQ_MSG_TYP>>])];
                        netRead0 := msg2;
                    };
                    msg := netRead0;
                    assert ((msg).to) = (self);
                    assert ((msg).from) = (ProxyID);
                    assert ((msg).typ) = (PROXY_REQ_MSG_TYP);
                    fdRead0 := fd[self];
                    assert (fdRead0) = (TRUE);
                    if ((EXPLORE_FAIL) = (TRUE)) {
                        either {
                            fdWrite0 := fd;
                            fdWrite1 := fdWrite0;
                            network := netWrite4;
                            fd := fdWrite1;
                        } or {
                            fdWrite := [fd EXCEPT ![self] = FALSE];
                            fdWrite0 := fdWrite;
                            fdWrite1 := fdWrite0;
                            network := netWrite4;
                            fd := fdWrite1;
                            goto failLabel;
                        };
                    } else {
                        fdWrite1 := fd;
                        network := netWrite4;
                        fd := fdWrite1;
                    };

                serverSendMsg:
                    resp := [from |-> self, to |-> (msg).from, body |-> self, id |-> (msg).id, typ |-> PROXY_RESP_MSG_TYP];
                    await (Len(network[<<(resp).to, (resp).typ>>])) < (BUFFER_SIZE);
                    netWrite4 := [network EXCEPT ![<<(resp).to, (resp).typ>>] = Append(network[<<(resp).to, (resp).typ>>], resp)];
                    fdRead0 := fd[self];
                    assert (fdRead0) = (TRUE);
                    if ((EXPLORE_FAIL) = (TRUE)) {
                        either {
                            fdWrite2 := fd;
                            fdWrite3 := fdWrite2;
                            network := netWrite4;
                            fd := fdWrite3;
                            goto serverLoop;
                        } or {
                            fdWrite := [fd EXCEPT ![self] = FALSE];
                            fdWrite2 := fdWrite;
                            fdWrite3 := fdWrite2;
                            network := netWrite4;
                            fd := fdWrite3;
                            goto failLabel;
                        };
                    } else {
                        fdWrite3 := fd;
                        network := netWrite4;
                        fd := fdWrite3;
                        goto serverLoop;
                    };

            } else {
                netWrite5 := network;
                fdWrite4 := fd;
                network := netWrite5;
                fd := fdWrite4;
            };
        failLabel:
            fdRead0 := fd[self];
            assert (fdRead0) = (FALSE);
            if ((EXPLORE_REJOIN) = (TRUE)) {
                either {
                    fdWrite5 := fd;
                    fdWrite6 := fdWrite5;
                    fd := fdWrite6;
                } or {
                    fdWrite := [fd EXCEPT ![self] = TRUE];
                    fdWrite5 := fdWrite;
                    fdWrite6 := fdWrite5;
                    fd := fdWrite6;
                    goto serverLoop;
                };
            } else {
                fdWrite6 := fd;
                fd := fdWrite6;
            };

    }
    fair process (Client \in CLIENT_SET)
    variables req, resp;
    {
        clientLoop:
            if (TRUE) {
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
                    assert ((resp).to) = (self);
                    assert ((resp).id) = (0);
                    assert ((resp).typ) = (RESP_MSG_TYP);
                    network := netWrite6;
                    goto clientLoop;

            } else {
                netWrite7 := network;
                network := netWrite7;
            };

    }
}
\* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION* END PLUSCAL TRANSLATION




************************)
\* BEGIN TRANSLATION (chksum(pcal) = "acaa25b7" /\ chksum(tla) = "7a791c62")
\* Label proxyMsg of process Proxy at line 232 col 21 changed to proxyMsg_
\* Process variable msg of process Proxy at line 218 col 15 changed to msg_
\* Process variable resp of process Proxy at line 218 col 46 changed to resp_
\* Process variable resp of process Server at line 303 col 20 changed to resp_S
CONSTANT defaultInitValue
VARIABLES network, fd, netRead, netWrite, fdRead, netWrite0, netWrite1,
          netWrite2, netWrite3, netRead0, netWrite4, fdRead0, fdWrite,
          fdWrite0, fdWrite1, fdWrite2, fdWrite3, netWrite5, fdWrite4,
          fdWrite5, fdWrite6, netWrite6, netRead1, netWrite7, pc

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

VARIABLES msg_, proxyResp, proxyMsg, idx, resp_, tmp, msg, resp_S, req, resp

vars == << network, fd, netRead, netWrite, fdRead, netWrite0, netWrite1,
           netWrite2, netWrite3, netRead0, netWrite4, fdRead0, fdWrite,
           fdWrite0, fdWrite1, fdWrite2, fdWrite3, netWrite5, fdWrite4,
           fdWrite5, fdWrite6, netWrite6, netRead1, netWrite7, pc, msg_,
           proxyResp, proxyMsg, idx, resp_, tmp, msg, resp_S, req, resp >>

ProcSet == {ProxyID} \cup (SERVER_SET) \cup (CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET, typ \in MSG_TYP_SET |-> <<>>]
        /\ fd = [id \in NODE_SET |-> TRUE]
        /\ netRead = defaultInitValue
        /\ netWrite = defaultInitValue
        /\ fdRead = defaultInitValue
        /\ netWrite0 = defaultInitValue
        /\ netWrite1 = defaultInitValue
        /\ netWrite2 = defaultInitValue
        /\ netWrite3 = defaultInitValue
        /\ netRead0 = defaultInitValue
        /\ netWrite4 = defaultInitValue
        /\ fdRead0 = defaultInitValue
        /\ fdWrite = defaultInitValue
        /\ fdWrite0 = defaultInitValue
        /\ fdWrite1 = defaultInitValue
        /\ fdWrite2 = defaultInitValue
        /\ fdWrite3 = defaultInitValue
        /\ netWrite5 = defaultInitValue
        /\ fdWrite4 = defaultInitValue
        /\ fdWrite5 = defaultInitValue
        /\ fdWrite6 = defaultInitValue
        /\ netWrite6 = defaultInitValue
        /\ netRead1 = defaultInitValue
        /\ netWrite7 = defaultInitValue
        (* Process Proxy *)
        /\ msg_ = defaultInitValue
        /\ proxyResp = defaultInitValue
        /\ proxyMsg = defaultInitValue
        /\ idx = defaultInitValue
        /\ resp_ = defaultInitValue
        /\ tmp = defaultInitValue
        (* Process Server *)
        /\ msg = [self \in SERVER_SET |-> defaultInitValue]
        /\ resp_S = [self \in SERVER_SET |-> defaultInitValue]
        (* Process Client *)
        /\ req = [self \in CLIENT_SET |-> defaultInitValue]
        /\ resp = [self \in CLIENT_SET |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = ProxyID -> "proxyLoop"
                                        [] self \in SERVER_SET -> "serverLoop"
                                        [] self \in CLIENT_SET -> "clientLoop"]

proxyLoop == /\ pc[ProxyID] = "proxyLoop"
             /\ IF TRUE
                   THEN /\ pc' = [pc EXCEPT ![ProxyID] = "rcvMsgFromClient"]
                        /\ UNCHANGED << network, netWrite3 >>
                   ELSE /\ netWrite3' = network
                        /\ network' = netWrite3'
                        /\ pc' = [pc EXCEPT ![ProxyID] = "Done"]
             /\ UNCHANGED << fd, netRead, netWrite, fdRead, netWrite0,
                             netWrite1, netWrite2, netRead0, netWrite4,
                             fdRead0, fdWrite, fdWrite0, fdWrite1, fdWrite2,
                             fdWrite3, netWrite5, fdWrite4, fdWrite5, fdWrite6,
                             netWrite6, netRead1, netWrite7, msg_, proxyResp,
                             proxyMsg, idx, resp_, tmp, msg, resp_S, req, resp >>

rcvMsgFromClient == /\ pc[ProxyID] = "rcvMsgFromClient"
                    /\ (Len(network[<<ProxyID, REQ_MSG_TYP>>])) > (0)
                    /\ LET msg0 == Head(network[<<ProxyID, REQ_MSG_TYP>>]) IN
                         /\ netWrite' = [network EXCEPT ![<<ProxyID, REQ_MSG_TYP>>] = Tail(network[<<ProxyID, REQ_MSG_TYP>>])]
                         /\ netRead' = msg0
                    /\ msg_' = netRead'
                    /\ network' = netWrite'
                    /\ pc' = [pc EXCEPT ![ProxyID] = "proxyMsg_"]
                    /\ UNCHANGED << fd, fdRead, netWrite0, netWrite1,
                                    netWrite2, netWrite3, netRead0, netWrite4,
                                    fdRead0, fdWrite, fdWrite0, fdWrite1,
                                    fdWrite2, fdWrite3, netWrite5, fdWrite4,
                                    fdWrite5, fdWrite6, netWrite6, netRead1,
                                    netWrite7, proxyResp, proxyMsg, idx, resp_,
                                    tmp, msg, resp_S, req, resp >>

proxyMsg_ == /\ pc[ProxyID] = "proxyMsg_"
             /\ Assert(((msg_).to) = (ProxyID),
                       "Failure of assertion at line 232, column 21.")
             /\ Assert(((msg_).typ) = (REQ_MSG_TYP),
                       "Failure of assertion at line 233, column 21.")
             /\ proxyResp' = [from |-> ProxyID, to |-> (msg_).from, body |-> FAIL, id |-> (msg_).id, typ |-> PROXY_RESP_MSG_TYP]
             /\ idx' = 1
             /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
             /\ UNCHANGED << network, fd, netRead, netWrite, fdRead, netWrite0,
                             netWrite1, netWrite2, netWrite3, netRead0,
                             netWrite4, fdRead0, fdWrite, fdWrite0, fdWrite1,
                             fdWrite2, fdWrite3, netWrite5, fdWrite4, fdWrite5,
                             fdWrite6, netWrite6, netRead1, netWrite7, msg_,
                             proxyMsg, resp_, tmp, msg, resp_S, req, resp >>

serversLoop == /\ pc[ProxyID] = "serversLoop"
               /\ IF (idx) <= (NUM_SERVERS)
                     THEN /\ pc' = [pc EXCEPT ![ProxyID] = "proxySendMsg"]
                          /\ UNCHANGED << network, netWrite2 >>
                     ELSE /\ netWrite2' = network
                          /\ network' = netWrite2'
                          /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
               /\ UNCHANGED << fd, netRead, netWrite, fdRead, netWrite0,
                               netWrite1, netWrite3, netRead0, netWrite4,
                               fdRead0, fdWrite, fdWrite0, fdWrite1, fdWrite2,
                               fdWrite3, netWrite5, fdWrite4, fdWrite5,
                               fdWrite6, netWrite6, netRead1, netWrite7, msg_,
                               proxyResp, proxyMsg, idx, resp_, tmp, msg,
                               resp_S, req, resp >>

proxySendMsg == /\ pc[ProxyID] = "proxySendMsg"
                /\ fdRead' = fd[idx]
                /\ IF (fdRead') = (TRUE)
                      THEN /\ proxyMsg' = [from |-> ProxyID, to |-> idx, body |-> (msg_).body, id |-> (msg_).id, typ |-> PROXY_REQ_MSG_TYP]
                           /\ (Len(network[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>])) < (BUFFER_SIZE)
                           /\ netWrite' = [network EXCEPT ![<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>] = Append(network[<<(proxyMsg').to, PROXY_REQ_MSG_TYP>>], proxyMsg')]
                           /\ netWrite0' = netWrite'
                           /\ network' = netWrite0'
                           /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsg"]
                           /\ idx' = idx
                      ELSE /\ idx' = (idx) + (1)
                           /\ netWrite0' = network
                           /\ network' = netWrite0'
                           /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                           /\ UNCHANGED << netWrite, proxyMsg >>
                /\ UNCHANGED << fd, netRead, netWrite1, netWrite2, netWrite3,
                                netRead0, netWrite4, fdRead0, fdWrite,
                                fdWrite0, fdWrite1, fdWrite2, fdWrite3,
                                netWrite5, fdWrite4, fdWrite5, fdWrite6,
                                netWrite6, netRead1, netWrite7, msg_,
                                proxyResp, resp_, tmp, msg, resp_S, req, resp >>

proxyRcvMsg == /\ pc[ProxyID] = "proxyRcvMsg"
               /\ fdRead' = fd[idx]
               /\ IF (fdRead') = (TRUE)
                     THEN /\ (Len(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])) > (0)
                          /\ LET msg1 == Head(network[<<ProxyID, PROXY_RESP_MSG_TYP>>]) IN
                               /\ netWrite' = [network EXCEPT ![<<ProxyID, PROXY_RESP_MSG_TYP>>] = Tail(network[<<ProxyID, PROXY_RESP_MSG_TYP>>])]
                               /\ netRead' = msg1
                          /\ tmp' = netRead'
                          /\ IF ((tmp').from) # (idx)
                                THEN /\ network' = netWrite'
                                     /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsg"]
                                ELSE /\ network' = netWrite'
                                     /\ pc' = [pc EXCEPT ![ProxyID] = "proxyRcvMsgAsserts"]
                          /\ UNCHANGED << netWrite1, idx >>
                     ELSE /\ idx' = (idx) + (1)
                          /\ netWrite1' = network
                          /\ network' = netWrite1'
                          /\ pc' = [pc EXCEPT ![ProxyID] = "serversLoop"]
                          /\ UNCHANGED << netRead, netWrite, tmp >>
               /\ UNCHANGED << fd, netWrite0, netWrite2, netWrite3, netRead0,
                               netWrite4, fdRead0, fdWrite, fdWrite0, fdWrite1,
                               fdWrite2, fdWrite3, netWrite5, fdWrite4,
                               fdWrite5, fdWrite6, netWrite6, netRead1,
                               netWrite7, msg_, proxyResp, proxyMsg, resp_,
                               msg, resp_S, req, resp >>

proxyRcvMsgAsserts == /\ pc[ProxyID] = "proxyRcvMsgAsserts"
                      /\ proxyResp' = tmp
                      /\ Assert(((proxyResp').to) = (ProxyID),
                                "Failure of assertion at line 271, column 37.")
                      /\ Assert(((proxyResp').from) = (idx),
                                "Failure of assertion at line 272, column 37.")
                      /\ Assert(((proxyResp').id) = ((msg_).id),
                                "Failure of assertion at line 273, column 37.")
                      /\ Assert(((proxyResp').typ) = (PROXY_RESP_MSG_TYP),
                                "Failure of assertion at line 274, column 37.")
                      /\ pc' = [pc EXCEPT ![ProxyID] = "sendMsgToClient"]
                      /\ UNCHANGED << network, fd, netRead, netWrite, fdRead,
                                      netWrite0, netWrite1, netWrite2,
                                      netWrite3, netRead0, netWrite4, fdRead0,
                                      fdWrite, fdWrite0, fdWrite1, fdWrite2,
                                      fdWrite3, netWrite5, fdWrite4, fdWrite5,
                                      fdWrite6, netWrite6, netRead1, netWrite7,
                                      msg_, proxyMsg, idx, resp_, tmp, msg,
                                      resp_S, req, resp >>

sendMsgToClient == /\ pc[ProxyID] = "sendMsgToClient"
                   /\ resp_' = [from |-> ProxyID, to |-> (msg_).from, body |-> (proxyResp).body, id |-> (proxyResp).id, typ |-> RESP_MSG_TYP]
                   /\ (Len(network[<<(resp_').to, (resp_').typ>>])) < (BUFFER_SIZE)
                   /\ netWrite' = [network EXCEPT ![<<(resp_').to, (resp_').typ>>] = Append(network[<<(resp_').to, (resp_').typ>>], resp_')]
                   /\ network' = netWrite'
                   /\ pc' = [pc EXCEPT ![ProxyID] = "proxyLoop"]
                   /\ UNCHANGED << fd, netRead, fdRead, netWrite0, netWrite1,
                                   netWrite2, netWrite3, netRead0, netWrite4,
                                   fdRead0, fdWrite, fdWrite0, fdWrite1,
                                   fdWrite2, fdWrite3, netWrite5, fdWrite4,
                                   fdWrite5, fdWrite6, netWrite6, netRead1,
                                   netWrite7, msg_, proxyResp, proxyMsg, idx,
                                   tmp, msg, resp_S, req, resp >>

Proxy == proxyLoop \/ rcvMsgFromClient \/ proxyMsg_ \/ serversLoop
            \/ proxySendMsg \/ proxyRcvMsg \/ proxyRcvMsgAsserts
            \/ sendMsgToClient

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "serverRcvMsg"]
                               /\ UNCHANGED << network, fd, netWrite5,
                                               fdWrite4 >>
                          ELSE /\ netWrite5' = network
                               /\ fdWrite4' = fd
                               /\ network' = netWrite5'
                               /\ fd' = fdWrite4'
                               /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                    /\ UNCHANGED << netRead, netWrite, fdRead, netWrite0,
                                    netWrite1, netWrite2, netWrite3, netRead0,
                                    netWrite4, fdRead0, fdWrite, fdWrite0,
                                    fdWrite1, fdWrite2, fdWrite3, fdWrite5,
                                    fdWrite6, netWrite6, netRead1, netWrite7,
                                    msg_, proxyResp, proxyMsg, idx, resp_, tmp,
                                    msg, resp_S, req, resp >>

serverRcvMsg(self) == /\ pc[self] = "serverRcvMsg"
                      /\ (Len(network[<<self, PROXY_REQ_MSG_TYP>>])) > (0)
                      /\ LET msg2 == Head(network[<<self, PROXY_REQ_MSG_TYP>>]) IN
                           /\ netWrite4' = [network EXCEPT ![<<self, PROXY_REQ_MSG_TYP>>] = Tail(network[<<self, PROXY_REQ_MSG_TYP>>])]
                           /\ netRead0' = msg2
                      /\ msg' = [msg EXCEPT ![self] = netRead0']
                      /\ Assert(((msg'[self]).to) = (self),
                                "Failure of assertion at line 314, column 21.")
                      /\ Assert(((msg'[self]).from) = (ProxyID),
                                "Failure of assertion at line 315, column 21.")
                      /\ Assert(((msg'[self]).typ) = (PROXY_REQ_MSG_TYP),
                                "Failure of assertion at line 316, column 21.")
                      /\ fdRead0' = fd[self]
                      /\ Assert((fdRead0') = (TRUE),
                                "Failure of assertion at line 318, column 21.")
                      /\ IF (EXPLORE_FAIL) = (TRUE)
                            THEN /\ \/ /\ fdWrite0' = fd
                                       /\ fdWrite1' = fdWrite0'
                                       /\ network' = netWrite4'
                                       /\ fd' = fdWrite1'
                                       /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                                       /\ UNCHANGED fdWrite
                                    \/ /\ fdWrite' = [fd EXCEPT ![self] = FALSE]
                                       /\ fdWrite0' = fdWrite'
                                       /\ fdWrite1' = fdWrite0'
                                       /\ network' = netWrite4'
                                       /\ fd' = fdWrite1'
                                       /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                            ELSE /\ fdWrite1' = fd
                                 /\ network' = netWrite4'
                                 /\ fd' = fdWrite1'
                                 /\ pc' = [pc EXCEPT ![self] = "serverSendMsg"]
                                 /\ UNCHANGED << fdWrite, fdWrite0 >>
                      /\ UNCHANGED << netRead, netWrite, fdRead, netWrite0,
                                      netWrite1, netWrite2, netWrite3,
                                      fdWrite2, fdWrite3, netWrite5, fdWrite4,
                                      fdWrite5, fdWrite6, netWrite6, netRead1,
                                      netWrite7, msg_, proxyResp, proxyMsg,
                                      idx, resp_, tmp, resp_S, req, resp >>

serverSendMsg(self) == /\ pc[self] = "serverSendMsg"
                       /\ resp_S' = [resp_S EXCEPT ![self] = [from |-> self, to |-> (msg[self]).from, body |-> self, id |-> (msg[self]).id, typ |-> PROXY_RESP_MSG_TYP]]
                       /\ (Len(network[<<(resp_S'[self]).to, (resp_S'[self]).typ>>])) < (BUFFER_SIZE)
                       /\ netWrite4' = [network EXCEPT ![<<(resp_S'[self]).to, (resp_S'[self]).typ>>] = Append(network[<<(resp_S'[self]).to, (resp_S'[self]).typ>>], resp_S'[self])]
                       /\ fdRead0' = fd[self]
                       /\ Assert((fdRead0') = (TRUE),
                                 "Failure of assertion at line 344, column 21.")
                       /\ IF (EXPLORE_FAIL) = (TRUE)
                             THEN /\ \/ /\ fdWrite2' = fd
                                        /\ fdWrite3' = fdWrite2'
                                        /\ network' = netWrite4'
                                        /\ fd' = fdWrite3'
                                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                        /\ UNCHANGED fdWrite
                                     \/ /\ fdWrite' = [fd EXCEPT ![self] = FALSE]
                                        /\ fdWrite2' = fdWrite'
                                        /\ fdWrite3' = fdWrite2'
                                        /\ network' = netWrite4'
                                        /\ fd' = fdWrite3'
                                        /\ pc' = [pc EXCEPT ![self] = "failLabel"]
                             ELSE /\ fdWrite3' = fd
                                  /\ network' = netWrite4'
                                  /\ fd' = fdWrite3'
                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                  /\ UNCHANGED << fdWrite, fdWrite2 >>
                       /\ UNCHANGED << netRead, netWrite, fdRead, netWrite0,
                                       netWrite1, netWrite2, netWrite3,
                                       netRead0, fdWrite0, fdWrite1, netWrite5,
                                       fdWrite4, fdWrite5, fdWrite6, netWrite6,
                                       netRead1, netWrite7, msg_, proxyResp,
                                       proxyMsg, idx, resp_, tmp, msg, req,
                                       resp >>

failLabel(self) == /\ pc[self] = "failLabel"
                   /\ fdRead0' = fd[self]
                   /\ Assert((fdRead0') = (FALSE),
                             "Failure of assertion at line 375, column 13.")
                   /\ IF (EXPLORE_REJOIN) = (TRUE)
                         THEN /\ \/ /\ fdWrite5' = fd
                                    /\ fdWrite6' = fdWrite5'
                                    /\ fd' = fdWrite6'
                                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED fdWrite
                                 \/ /\ fdWrite' = [fd EXCEPT ![self] = TRUE]
                                    /\ fdWrite5' = fdWrite'
                                    /\ fdWrite6' = fdWrite5'
                                    /\ fd' = fdWrite6'
                                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                         ELSE /\ fdWrite6' = fd
                              /\ fd' = fdWrite6'
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << fdWrite, fdWrite5 >>
                   /\ UNCHANGED << network, netRead, netWrite, fdRead,
                                   netWrite0, netWrite1, netWrite2, netWrite3,
                                   netRead0, netWrite4, fdWrite0, fdWrite1,
                                   fdWrite2, fdWrite3, netWrite5, fdWrite4,
                                   netWrite6, netRead1, netWrite7, msg_,
                                   proxyResp, proxyMsg, idx, resp_, tmp, msg,
                                   resp_S, req, resp >>

Server(self) == serverLoop(self) \/ serverRcvMsg(self)
                   \/ serverSendMsg(self) \/ failLabel(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "clientSendReq"]
                               /\ UNCHANGED << network, netWrite7 >>
                          ELSE /\ netWrite7' = network
                               /\ network' = netWrite7'
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << fd, netRead, netWrite, fdRead, netWrite0,
                                    netWrite1, netWrite2, netWrite3, netRead0,
                                    netWrite4, fdRead0, fdWrite, fdWrite0,
                                    fdWrite1, fdWrite2, fdWrite3, netWrite5,
                                    fdWrite4, fdWrite5, fdWrite6, netWrite6,
                                    netRead1, msg_, proxyResp, proxyMsg, idx,
                                    resp_, tmp, msg, resp_S, req, resp >>

clientSendReq(self) == /\ pc[self] = "clientSendReq"
                       /\ req' = [req EXCEPT ![self] = [from |-> self, to |-> ProxyID, body |-> self, id |-> 0, typ |-> REQ_MSG_TYP]]
                       /\ (Len(network[<<(req'[self]).to, (req'[self]).typ>>])) < (BUFFER_SIZE)
                       /\ netWrite6' = [network EXCEPT ![<<(req'[self]).to, (req'[self]).typ>>] = Append(network[<<(req'[self]).to, (req'[self]).typ>>], req'[self])]
                       /\ network' = netWrite6'
                       /\ pc' = [pc EXCEPT ![self] = "clientRcvResp"]
                       /\ UNCHANGED << fd, netRead, netWrite, fdRead,
                                       netWrite0, netWrite1, netWrite2,
                                       netWrite3, netRead0, netWrite4, fdRead0,
                                       fdWrite, fdWrite0, fdWrite1, fdWrite2,
                                       fdWrite3, netWrite5, fdWrite4, fdWrite5,
                                       fdWrite6, netRead1, netWrite7, msg_,
                                       proxyResp, proxyMsg, idx, resp_, tmp,
                                       msg, resp_S, resp >>

clientRcvResp(self) == /\ pc[self] = "clientRcvResp"
                       /\ (Len(network[<<self, RESP_MSG_TYP>>])) > (0)
                       /\ LET msg3 == Head(network[<<self, RESP_MSG_TYP>>]) IN
                            /\ netWrite6' = [network EXCEPT ![<<self, RESP_MSG_TYP>>] = Tail(network[<<self, RESP_MSG_TYP>>])]
                            /\ netRead1' = msg3
                       /\ resp' = [resp EXCEPT ![self] = netRead1']
                       /\ Assert(((resp'[self]).to) = (self),
                                 "Failure of assertion at line 412, column 21.")
                       /\ Assert(((resp'[self]).id) = (0),
                                 "Failure of assertion at line 413, column 21.")
                       /\ Assert(((resp'[self]).typ) = (RESP_MSG_TYP),
                                 "Failure of assertion at line 414, column 21.")
                       /\ network' = netWrite6'
                       /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                       /\ UNCHANGED << fd, netRead, netWrite, fdRead,
                                       netWrite0, netWrite1, netWrite2,
                                       netWrite3, netRead0, netWrite4, fdRead0,
                                       fdWrite, fdWrite0, fdWrite1, fdWrite2,
                                       fdWrite3, netWrite5, fdWrite4, fdWrite5,
                                       fdWrite6, netWrite7, msg_, proxyResp,
                                       proxyMsg, idx, resp_, tmp, msg, resp_S,
                                       req >>

Client(self) == clientLoop(self) \/ clientSendReq(self)
                   \/ clientRcvResp(self)

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


\* Contraints

FailCntCnst == Cardinality({node \in DOMAIN fd : fd[node] = FALSE}) <= F

\* Invariants

ProxyAllFailOK == (pc[ProxyID] = "sendMsgToClient" /\ proxyResp.body = FAIL) =>
                  /\ \A node \in SERVER_SET : fd[node] = FALSE
                  /\ idx > NUM_SERVERS
ProxyAliveOK ==  (pc[ProxyID] = "sendMsgToClient" /\ proxyResp.body # FAIL) =>
                  /\ idx <= NUM_SERVERS
                  /\ proxyResp.from = idx

BufferOK(node, typ) == Len(network[node, typ]) >= 0 /\ Len(network[node, typ]) <= BUFFER_SIZE
BuffersOK == \A <<node, typ>> \in DOMAIN network : BufferOK(node, typ)

\* Properties

ReceiveResp(client) == pc[client] = "clientSendReq" ~> pc[client] = "clientRcvResp"
ClientsOK == \A client \in CLIENT_SET : ReceiveResp(client)

=============================================================================
\* Modification History
\* Last modified Fri May 21 20:17:32 PDT 2021 by shayan
\* Created Mon Mar 29 02:55:50 PDT 2021 by shayan
