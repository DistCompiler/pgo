------------------------------- MODULE kvs -------------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumServers

CONSTANT NumClients

(********************

--mpcal kvs {
    define {
        Nil == 0

        Key1 == "key1"
        Key2 == "key2"
        Key3 == "key3"
        Key4 == "key4"

        KeySet == {Key1, Key2, Key3, Key4}

        Value1 == "value1"
        Value2 == "value2"
        Value3 == "value3"
        Value4 == "value4"

        GetRequest  == 1
        GetResponse == 2
        PutRequest  == 3
        PutResponse == 4

        Get == 1
        Put == 2

        ServerSet == 1..NumServers
        ClientSet == (NumServers+1)..(NumServers+NumClients)
        
        NodeSet == ServerSet \cup ClientSet
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
            await Len($variable) > 0;
            with (readMsg = Head($variable)) {
                $variable := Tail($variable);
                yield readMsg;
            };
        }
        
        write {
            yield Append($variable, $value);
        }
    }

    mapping macro InputChannel {
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

    mapping macro PerfectFD {
        read {
            yield $variable;
        }

        write { yield $value; }
    }

    archetype AServer(ref net[_], ref kvs)
    variable req;
    {
    serverLoop:
        while (TRUE) {
            req := net[self];
            assert req.dest = self;

        handleReq:
            if (req.type = GetRequest) {
                with (
                    i = self, j = req.source,
                    found = req.key \in DOMAIN kvs,
                    value = IF found THEN kvs[req.key] ELSE Nil
                ) {
                    net[j] := [
                        type   |-> GetResponse,
                        found  |-> found,
                        key    |-> req.key,
                        value  |-> value,
                        idx    |-> req.idx,
                        source |-> i,
                        dest   |-> j
                    ];
                };
            } else if (req.type = PutRequest) {
                if (req.key \notin DOMAIN kvs) {
                    kvs := kvs @@ (req.key :> req.value);
                } else {
                    kvs := [kvs EXCEPT ![req.key] = req.value];
                };

                with (i = self, j = req.source) {
                    net[j] := [
                        type   |-> PutResponse,
                        key    |-> req.key,
                        value  |-> req.value,
                        idx    |-> req.idx,
                        source |-> i,
                        dest   |-> j
                    ];
                };
            };
        };
    }

    archetype AClient(ref net[_], ref in, ref out, ref fd[_])
    variable req, reqIdx = 0, srv = 1, resp;
    {
    clientLoop:
        while (TRUE) {
            req := in;
            reqIdx := reqIdx + 1;

        selectServer:
            while (srv <= NumServers) {
                if (\lnot fd[srv]) {
                    goto sndReq;
                } else {
                    srv := srv + 1;
                    if (srv > NumServers) {
                        srv := 1;
                    };
                };
            };
        
        sndReq:
            if (req.type = Put) {
                Send(net, srv, fd, [
                    type   |-> PutRequest,
                    idx    |-> reqIdx,
                    key    |-> req.key,
                    value  |-> req.value,
                    source |-> self,
                    dest   |-> srv
                ]);
            } else if (req.type = Get) {
                Send(net, srv, fd, [
                    type   |-> GetRequest,
                    idx    |-> reqIdx,
                    key    |-> req.key,
                    source |-> self,
                    dest   |-> srv
                ]);
            };
        
        rcvResp:
            resp := net[self];
            assert resp.idx = reqIdx;
            out := resp;
        };
    }

    variables 
        network = [id \in NodeSet |-> <<>>];
        fd = [id \in NodeSet |-> FALSE];
        kvs = [key \in KeySet |-> ""];
        in = <<
            [type |-> Put, key |-> Key1, value |-> Value1],
            [type |-> Get, key |-> Key1]
        >>;
        out;

    fair process (Server \in ServerSet) == instance AServer(ref network[_], ref kvs)
        mapping network[_] via ReliableFIFOLink;

    fair process (Client \in ClientSet) == instance AClient(ref network[_], ref in, ref out, ref fd[_])
        mapping network[_] via ReliableFIFOLink
        mapping in via InputChannel
        mapping fd[_] via PerfectFD;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm kvs {
  variables network = [id \in NodeSet |-> <<>>]; fd = [id \in NodeSet |-> FALSE]; kvs = [key \in KeySet |-> ""]; in = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key1]>>; out;
  define{
    Nil == 0
    Key1 == "key1"
    Key2 == "key2"
    Key3 == "key3"
    Key4 == "key4"
    KeySet == {Key1, Key2, Key3, Key4}
    Value1 == "value1"
    Value2 == "value2"
    Value3 == "value3"
    Value4 == "value4"
    GetRequest == 1
    GetResponse == 2
    PutRequest == 3
    PutResponse == 4
    Get == 1
    Put == 2
    ServerSet == (1) .. (NumServers)
    ClientSet == ((NumServers) + (1)) .. ((NumServers) + (NumClients))
    NodeSet == (ServerSet) \union (ClientSet)
  }
  
  fair process (Server \in ServerSet)
    variables req;
  {
    serverLoop:
      if (TRUE) {
        await (Len((network)[self])) > (0);
        with (readMsg00 = Head((network)[self])) {
          network := [network EXCEPT ![self] = Tail((network)[self])];
          with (yielded_network1 = readMsg00) {
            req := yielded_network1;
            assert ((req).dest) = (self);
            goto handleReq;
          };
        };
      } else {
        goto Done;
      };
    handleReq:
      if (((req).type) = (GetRequest)) {
        with (
          i = self, 
          j = (req).source, 
          found = ((req).key) \in (DOMAIN (kvs)), 
          value = IF found THEN (kvs)[(req).key] ELSE Nil, 
          value00 = [type |-> GetResponse, found |-> found, key |-> (req).key, value |-> value, idx |-> (req).idx, source |-> i, dest |-> j]
        ) {
          network := [network EXCEPT ![j] = Append((network)[j], value00)];
          goto serverLoop;
        };
      } else {
        if (((req).type) = (PutRequest)) {
          if (((req).key) \notin (DOMAIN (kvs))) {
            kvs := (kvs) @@ (((req).key) :> ((req).value));
            with (
              i = self, 
              j = (req).source, 
              value10 = [type |-> PutResponse, key |-> (req).key, value |-> (req).value, idx |-> (req).idx, source |-> i, dest |-> j]
            ) {
              network := [network EXCEPT ![j] = Append((network)[j], value10)];
              goto serverLoop;
            };
          } else {
            kvs := [kvs EXCEPT ![(req).key] = (req).value];
            with (
              i = self, 
              j = (req).source, 
              value11 = [type |-> PutResponse, key |-> (req).key, value |-> (req).value, idx |-> (req).idx, source |-> i, dest |-> j]
            ) {
              network := [network EXCEPT ![j] = Append((network)[j], value11)];
              goto serverLoop;
            };
          };
        } else {
          goto serverLoop;
        };
      };
  }
  
  fair process (Client \in ClientSet)
    variables req0; reqIdx = 0; srv = 1; resp;
  {
    clientLoop:
      if (TRUE) {
        await (Len(in)) > (0);
        with (res00 = Head(in)) {
          in := Tail(in);
          with (yielded_in0 = res00) {
            req0 := yielded_in0;
            reqIdx := (reqIdx) + (1);
            goto selectServer;
          };
        };
      } else {
        goto Done;
      };
    selectServer:
      if ((srv) <= (NumServers)) {
        with (yielded_fd = (fd)[srv]) {
          if (~ (yielded_fd)) {
            goto sndReq;
          } else {
            with (srv1 = (srv) + (1)) {
              if ((srv1) > (NumServers)) {
                srv := 1;
                goto selectServer;
              } else {
                srv := srv1;
                goto selectServer;
              };
            };
          };
        };
      } else {
        goto sndReq;
      };
    sndReq:
      if (((req0).type) = (Put)) {
        with (value20 = [type |-> PutRequest, idx |-> reqIdx, key |-> (req0).key, value |-> (req0).value, source |-> self, dest |-> srv]) {
          network := [network EXCEPT ![srv] = Append((network)[srv], value20)];
          goto rcvResp;
        };
      } else {
        if (((req0).type) = (Get)) {
          with (value30 = [type |-> GetRequest, idx |-> reqIdx, key |-> (req0).key, source |-> self, dest |-> srv]) {
            network := [network EXCEPT ![srv] = Append((network)[srv], value30)];
            goto rcvResp;
          };
        } else {
          goto rcvResp;
        };
      };
    rcvResp:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = readMsg10) {
          resp := yielded_network00;
          assert ((resp).idx) = (reqIdx);
          out := resp;
          goto clientLoop;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "8d949109" /\ chksum(tla) = "106bde4e")
CONSTANT defaultInitValue
VARIABLES network, kvs, in, out, pc

(* define statement *)
Nil == 0
Key1 == "key1"
Key2 == "key2"
Key3 == "key3"
Key4 == "key4"
KeySet == {Key1, Key2, Key3, Key4}
Value1 == "value1"
Value2 == "value2"
Value3 == "value3"
Value4 == "value4"
GetRequest == 1
GetResponse == 2
PutRequest == 3
PutResponse == 4
Get == 1
Put == 2
ServerSet == (1) .. (NumServers)
ClientSet == ((NumServers) + (1)) .. ((NumServers) + (NumClients))
NodeSet == (ServerSet) \union (ClientSet)

VARIABLES req, req0, reqIdx, srv, resp

vars == << network, kvs, in, out, pc, req, req0, reqIdx, srv, resp >>

ProcSet == (ServerSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [id \in NodeSet |-> <<>>]
        /\ kvs = [key \in KeySet |-> ""]
        /\ in = <<[type |-> Put, key |-> Key1, value |-> Value1], [type |-> Get, key |-> Key1]>>
        /\ out = defaultInitValue
        (* Process Server *)
        /\ req = [self \in ServerSet |-> defaultInitValue]
        (* Process Client *)
        /\ req0 = [self \in ClientSet |-> defaultInitValue]
        /\ reqIdx = [self \in ClientSet |-> 0]
        /\ srv = [self \in ClientSet |-> Nil]
        /\ resp = [self \in ClientSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ClientSet -> "clientLoop"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ (Len((network)[self])) > (0)
                               /\ LET readMsg00 == Head((network)[self]) IN
                                    /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                                    /\ LET yielded_network1 == readMsg00 IN
                                         /\ req' = [req EXCEPT ![self] = yielded_network1]
                                         /\ Assert(((req'[self]).dest) = (self), 
                                                   "Failure of assertion at line 206, column 13.")
                                         /\ pc' = [pc EXCEPT ![self] = "handleReq"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << network, req >>
                    /\ UNCHANGED << kvs, in, out, req0, reqIdx, srv, resp >>

handleReq(self) == /\ pc[self] = "handleReq"
                   /\ IF ((req[self]).type) = (GetRequest)
                         THEN /\ LET i == self IN
                                   LET j == (req[self]).source IN
                                     LET found == ((req[self]).key) \in (DOMAIN (kvs)) IN
                                       LET value == IF found THEN (kvs)[(req[self]).key] ELSE Nil IN
                                         LET value00 == [type |-> GetResponse, found |-> found, key |-> (req[self]).key, value |-> value, idx |-> (req[self]).idx, source |-> i, dest |-> j] IN
                                           /\ network' = [network EXCEPT ![j] = Append((network)[j], value00)]
                                           /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                              /\ kvs' = kvs
                         ELSE /\ IF ((req[self]).type) = (PutRequest)
                                    THEN /\ IF ((req[self]).key) \notin (DOMAIN (kvs))
                                               THEN /\ kvs' = (kvs) @@ (((req[self]).key) :> ((req[self]).value))
                                                    /\ LET i == self IN
                                                         LET j == (req[self]).source IN
                                                           LET value10 == [type |-> PutResponse, key |-> (req[self]).key, value |-> (req[self]).value, idx |-> (req[self]).idx, source |-> i, dest |-> j] IN
                                                             /\ network' = [network EXCEPT ![j] = Append((network)[j], value10)]
                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                               ELSE /\ kvs' = [kvs EXCEPT ![(req[self]).key] = (req[self]).value]
                                                    /\ LET i == self IN
                                                         LET j == (req[self]).source IN
                                                           LET value11 == [type |-> PutResponse, key |-> (req[self]).key, value |-> (req[self]).value, idx |-> (req[self]).idx, source |-> i, dest |-> j] IN
                                                             /\ network' = [network EXCEPT ![j] = Append((network)[j], value11)]
                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                         /\ UNCHANGED << network, kvs >>
                   /\ UNCHANGED << in, out, req, req0, reqIdx, srv, resp >>

Server(self) == serverLoop(self) \/ handleReq(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ (Len(in)) > (0)
                               /\ LET res00 == Head(in) IN
                                    /\ in' = Tail(in)
                                    /\ LET yielded_in0 == res00 IN
                                         /\ req0' = [req0 EXCEPT ![self] = yielded_in0]
                                         /\ reqIdx' = [reqIdx EXCEPT ![self] = (reqIdx[self]) + (1)]
                                         /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << in, req0, reqIdx >>
                    /\ UNCHANGED << network, kvs, out, req, srv, resp >>

sndReq(self) == /\ pc[self] = "sndReq"
                /\ IF (srv[self]) = (Nil)
                      THEN /\ \E tmp1 \in ServerSet:
                                /\ srv' = [srv EXCEPT ![self] = tmp1]
                                /\ IF ((req0[self]).type) = (Put)
                                      THEN /\ LET value20 == [type |-> PutRequest, idx |-> reqIdx[self], key |-> (req0[self]).key, value |-> (req0[self]).value, source |-> self, dest |-> srv'[self]] IN
                                                /\ network' = [network EXCEPT ![srv'[self]] = Append((network)[srv'[self]], value20)]
                                                /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                      ELSE /\ IF ((req0[self]).type) = (Get)
                                                 THEN /\ LET value30 == [type |-> GetRequest, idx |-> reqIdx[self], key |-> (req0[self]).key, source |-> self, dest |-> srv'[self]] IN
                                                           /\ network' = [network EXCEPT ![srv'[self]] = Append((network)[srv'[self]], value30)]
                                                           /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                      /\ UNCHANGED network
                      ELSE /\ IF ((req0[self]).type) = (Put)
                                 THEN /\ LET value21 == [type |-> PutRequest, idx |-> reqIdx[self], key |-> (req0[self]).key, value |-> (req0[self]).value, source |-> self, dest |-> srv[self]] IN
                                           /\ network' = [network EXCEPT ![srv[self]] = Append((network)[srv[self]], value21)]
                                           /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                 ELSE /\ IF ((req0[self]).type) = (Get)
                                            THEN /\ LET value31 == [type |-> GetRequest, idx |-> reqIdx[self], key |-> (req0[self]).key, source |-> self, dest |-> srv[self]] IN
                                                      /\ network' = [network EXCEPT ![srv[self]] = Append((network)[srv[self]], value31)]
                                                      /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                                                 /\ UNCHANGED network
                           /\ srv' = srv
                /\ UNCHANGED << kvs, in, out, req, req0, reqIdx, resp >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ (Len((network)[self])) > (0)
                 /\ LET readMsg10 == Head((network)[self]) IN
                      /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                      /\ LET yielded_network00 == readMsg10 IN
                           /\ resp' = [resp EXCEPT ![self] = yielded_network00]
                           /\ Assert(((resp'[self]).idx) = (reqIdx[self]), 
                                     "Failure of assertion at line 314, column 11.")
                           /\ out' = resp'[self]
                           /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                 /\ UNCHANGED << kvs, in, req, req0, reqIdx, srv >>

Client(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: Server(self))
           \/ (\E self \in ClientSet: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(Server(self))
        /\ \A self \in ClientSet : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
