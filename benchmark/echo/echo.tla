------------------------------- MODULE echo -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(********************

--mpcal echo {
    define {
        ServerID == 1
        ClientID == 2

        NODE_SET == {ServerID, ClientID}
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

    archetype AServer(ref net[_])
    variable req;
    {
    serverLoop:
        while (TRUE) {
        serverRcv:
            req := net[self];
        serverSnd:
            net[req.from] := [from |-> self, body |-> req.body];
        };
    }

    archetype AClient(ref net[_], ref in, ref out)
    variable req, resp;
    {
    clientLoop:
        while (TRUE) {
        clientSnd:
            req := [from |-> self, body |-> in];
            net[ServerID] := req;
        clientRcv:
            resp := net[self];
            assert resp.body = req.body;
            out := resp.body;
        };
    }

    variables
        network = [id \in NODE_SET |-> <<>>];
        in = 1, out;

    fair process (Server \in {ServerID}) == instance AServer(ref network[_])
        mapping network[_] via ReliableFIFOLink;
    
    fair process (Client \in {ClientID}) == instance AClient(ref network[_], ref in, ref out)
        mapping network[_] via ReliableFIFOLink;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm echo {
  variables network = [id \in NODE_SET |-> <<>>]; in = 1; out;
  define{
    ServerID == 1
    ClientID == 2
    NODE_SET == {ServerID, ClientID}
  }
  
  fair process (Server \in {ServerID})
    variables req;
  {
    serverLoop:
      if(TRUE) {
        goto serverRcv;
      } else {
        goto Done;
      };
    serverRcv:
      await (Len((network)[self])) > (0);
      with (readMsg00 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network1 = readMsg00) {
          req := yielded_network1;
          goto serverSnd;
        };
      };
    serverSnd:
      with (value1 = [from |-> self, body |-> (req).body]) {
        network := [network EXCEPT ![(req).from] = Append((network)[(req).from], value1)];
        goto serverLoop;
      };
  }
  
  fair process (Client \in {ClientID})
    variables req0; resp;
  {
    clientLoop:
      if(TRUE) {
        goto clientSnd;
      } else {
        goto Done;
      };
    clientSnd:
      req0 := [from |-> self, body |-> in];
      with (value00 = req0) {
        network := [network EXCEPT ![ServerID] = Append((network)[ServerID], value00)];
        goto clientRcv;
      };
    clientRcv:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = readMsg10) {
          resp := yielded_network00;
          assert ((resp).body) = ((req0).body);
          out := (resp).body;
          goto clientLoop;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "67b149e" /\ chksum(tla) = "fead2658")
CONSTANT defaultInitValue
VARIABLES network, in, out, pc

(* define statement *)
ServerID == 1
ClientID == 2
NODE_SET == {ServerID, ClientID}

VARIABLES req, req0, resp

vars == << network, in, out, pc, req, req0, resp >>

ProcSet == ({ServerID}) \cup ({ClientID})

Init == (* Global variables *)
        /\ network = [id \in NODE_SET |-> <<>>]
        /\ in = 1
        /\ out = defaultInitValue
        (* Process Server *)
        /\ req = [self \in {ServerID} |-> defaultInitValue]
        (* Process Client *)
        /\ req0 = [self \in {ClientID} |-> defaultInitValue]
        /\ resp = [self \in {ClientID} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in {ServerID} -> "serverLoop"
                                        [] self \in {ClientID} -> "clientLoop"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "serverRcv"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << network, in, out, req, req0, resp >>

serverRcv(self) == /\ pc[self] = "serverRcv"
                   /\ (Len((network)[self])) > (0)
                   /\ LET readMsg00 == Head((network)[self]) IN
                        /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                        /\ LET yielded_network1 == readMsg00 IN
                             /\ req' = [req EXCEPT ![self] = yielded_network1]
                             /\ pc' = [pc EXCEPT ![self] = "serverSnd"]
                   /\ UNCHANGED << in, out, req0, resp >>

serverSnd(self) == /\ pc[self] = "serverSnd"
                   /\ LET value1 == [from |-> self, body |-> (req[self]).body] IN
                        /\ network' = [network EXCEPT ![(req[self]).from] = Append((network)[(req[self]).from], value1)]
                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                   /\ UNCHANGED << in, out, req, req0, resp >>

Server(self) == serverLoop(self) \/ serverRcv(self) \/ serverSnd(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "clientSnd"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << network, in, out, req, req0, resp >>

clientSnd(self) == /\ pc[self] = "clientSnd"
                   /\ req0' = [req0 EXCEPT ![self] = [from |-> self, body |-> in]]
                   /\ LET value00 == req0'[self] IN
                        /\ network' = [network EXCEPT ![ServerID] = Append((network)[ServerID], value00)]
                        /\ pc' = [pc EXCEPT ![self] = "clientRcv"]
                   /\ UNCHANGED << in, out, req, resp >>

clientRcv(self) == /\ pc[self] = "clientRcv"
                   /\ (Len((network)[self])) > (0)
                   /\ LET readMsg10 == Head((network)[self]) IN
                        /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                        /\ LET yielded_network00 == readMsg10 IN
                             /\ resp' = [resp EXCEPT ![self] = yielded_network00]
                             /\ Assert(((resp'[self]).body) = ((req0[self]).body), 
                                       "Failure of assertion at line 122, column 11.")
                             /\ out' = (resp'[self]).body
                             /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                   /\ UNCHANGED << in, req, req0 >>

Client(self) == clientLoop(self) \/ clientSnd(self) \/ clientRcv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {ServerID}: Server(self))
           \/ (\E self \in {ClientID}: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {ServerID} : WF_vars(Server(self))
        /\ \A self \in {ClientID} : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Properties

ProgressOK == (pc[ClientID] = "clientSnd") ~> (pc[ClientID] = "clientRcv")

=============================================================================
