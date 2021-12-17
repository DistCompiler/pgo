------------------------------- MODULE evallock -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumClients

(********************

--mpcal evallock {
    define {
        ServerID  == 0
        ServerSet == {ServerID}

        ClientSet == 1..NumClients

        NodeSet == ServerSet \cup ClientSet

        LockMsg   == 1
        UnlockMsg == 2
        GrantMsg  == 3
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

    archetype AServer(ref network[_])
    variables msg, q = <<>>;
    {
    serverLoop:
        while (TRUE) {
        serverReceive:
            msg := network[self];

        serverRespond:
            if (msg.type = LockMsg) {
                if (q = <<>>) {
                    network[msg.from] := GrantMsg;
                };
                q := Append(q, msg.from);
            } else if (msg.type = UnlockMsg) {
                q := Tail(q);
                if (q # <<>>) {
                    network[Head(q)] := GrantMsg;
                };
            };
        };
    }

    archetype AClient(ref network[_])
    variable hasLock = FALSE;
    {
    acquireLock:
        network[ServerID] := [from |-> self, type |-> LockMsg];
    criticalSection:
        with (resp = network[self]) {
            assert resp = GrantMsg;
        };
        hasLock := TRUE;
        \* print <<"in critical section: ", self>>;
    unlock:
        network[ServerID] := [from |-> self, type |-> UnlockMsg];
        hasLock := FALSE;
    }

    variables network = [id \in NodeSet |-> <<>>];

    fair process (Server \in ServerSet) == instance AServer(ref network[_])
        mapping network[_] via ReliableFIFOLink;


    fair process (client \in ClientSet) == instance AClient(ref network[_])
        mapping network[_] via ReliableFIFOLink;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm evallock {
  variables network = [id \in NodeSet |-> <<>>];
  define{
    ServerID == 0
    ServerSet == {ServerID}
    ClientSet == (1) .. (NumClients)
    NodeSet == (ServerSet) \union (ClientSet)
    LockMsg == 1
    UnlockMsg == 2
    GrantMsg == 3
  }
  
  fair process (Server \in ServerSet)
    variables msg; q = <<>>;
  {
    serverLoop:
      if (TRUE) {
        goto serverReceive;
      } else {
        goto Done;
      };
    serverReceive:
      await (Len((network)[self])) > (0);
      with (readMsg00 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network1 = readMsg00) {
          msg := yielded_network1;
          goto serverRespond;
        };
      };
    serverRespond:
      if (((msg).type) = (LockMsg)) {
        if ((q) = (<<>>)) {
          with (value3 = GrantMsg) {
            network := [network EXCEPT ![(msg).from] = Append((network)[(msg).from], value3)];
            q := Append(q, (msg).from);
            goto serverLoop;
          };
        } else {
          q := Append(q, (msg).from);
          goto serverLoop;
        };
      } else {
        if (((msg).type) = (UnlockMsg)) {
          q := Tail(q);
          if ((q) # (<<>>)) {
            with (value00 = GrantMsg) {
              network := [network EXCEPT ![Head(q)] = Append((network)[Head(q)], value00)];
              goto serverLoop;
            };
          } else {
            goto serverLoop;
          };
        } else {
          goto serverLoop;
        };
      };
  }
  
  fair process (client \in ClientSet)
    variables hasLock = FALSE;
  {
    acquireLock:
      with (value10 = [from |-> self, type |-> LockMsg]) {
        network := [network EXCEPT ![ServerID] = Append((network)[ServerID], value10)];
        goto criticalSection;
      };
    criticalSection:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (
          yielded_network00 = readMsg10, 
          resp1 = yielded_network00
        ) {
          assert (resp1) = (GrantMsg);
          hasLock := TRUE;
          goto unlock;
        };
      };
    unlock:
      with (value20 = [from |-> self, type |-> UnlockMsg]) {
        network := [network EXCEPT ![ServerID] = Append((network)[ServerID], value20)];
        hasLock := FALSE;
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "f9c427cd" /\ chksum(tla) = "98748790")
CONSTANT defaultInitValue
VARIABLES network, pc

(* define statement *)
ServerID == 0
ServerSet == {ServerID}
ClientSet == (1) .. (NumClients)
NodeSet == (ServerSet) \union (ClientSet)
LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

VARIABLES msg, q, hasLock

vars == << network, pc, msg, q, hasLock >>

ProcSet == (ServerSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ network = [id \in NodeSet |-> <<>>]
        (* Process Server *)
        /\ msg = [self \in ServerSet |-> defaultInitValue]
        /\ q = [self \in ServerSet |-> <<>>]
        (* Process client *)
        /\ hasLock = [self \in ClientSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ClientSet -> "acquireLock"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "serverReceive"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << network, msg, q, hasLock >>

serverReceive(self) == /\ pc[self] = "serverReceive"
                       /\ (Len((network)[self])) > (0)
                       /\ LET readMsg00 == Head((network)[self]) IN
                            /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                            /\ LET yielded_network1 == readMsg00 IN
                                 /\ msg' = [msg EXCEPT ![self] = yielded_network1]
                                 /\ pc' = [pc EXCEPT ![self] = "serverRespond"]
                       /\ UNCHANGED << q, hasLock >>

serverRespond(self) == /\ pc[self] = "serverRespond"
                       /\ IF ((msg[self]).type) = (LockMsg)
                             THEN /\ IF (q[self]) = (<<>>)
                                        THEN /\ LET value3 == GrantMsg IN
                                                  /\ network' = [network EXCEPT ![(msg[self]).from] = Append((network)[(msg[self]).from], value3)]
                                                  /\ q' = [q EXCEPT ![self] = Append(q[self], (msg[self]).from)]
                                                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                        ELSE /\ q' = [q EXCEPT ![self] = Append(q[self], (msg[self]).from)]
                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                             /\ UNCHANGED network
                             ELSE /\ IF ((msg[self]).type) = (UnlockMsg)
                                        THEN /\ q' = [q EXCEPT ![self] = Tail(q[self])]
                                             /\ IF (q'[self]) # (<<>>)
                                                   THEN /\ LET value00 == GrantMsg IN
                                                             /\ network' = [network EXCEPT ![Head(q'[self])] = Append((network)[Head(q'[self])], value00)]
                                                             /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                        /\ UNCHANGED network
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                             /\ UNCHANGED << network, q >>
                       /\ UNCHANGED << msg, hasLock >>

Server(self) == serverLoop(self) \/ serverReceive(self)
                   \/ serverRespond(self)

acquireLock(self) == /\ pc[self] = "acquireLock"
                     /\ LET value10 == [from |-> self, type |-> LockMsg] IN
                          /\ network' = [network EXCEPT ![ServerID] = Append((network)[ServerID], value10)]
                          /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                     /\ UNCHANGED << msg, q, hasLock >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ (Len((network)[self])) > (0)
                         /\ LET readMsg10 == Head((network)[self]) IN
                              /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                              /\ LET yielded_network00 == readMsg10 IN
                                   LET resp1 == yielded_network00 IN
                                     /\ Assert((resp1) = (GrantMsg), 
                                               "Failure of assertion at line 162, column 11.")
                                     /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
                                     /\ pc' = [pc EXCEPT ![self] = "unlock"]
                         /\ UNCHANGED << msg, q >>

unlock(self) == /\ pc[self] = "unlock"
                /\ LET value20 == [from |-> self, type |-> UnlockMsg] IN
                     /\ network' = [network EXCEPT ![ServerID] = Append((network)[ServerID], value20)]
                     /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msg, q >>

client(self) == acquireLock(self) \/ criticalSection(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: Server(self))
           \/ (\E self \in ClientSet: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(Server(self))
        /\ \A self \in ClientSet : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Invariants

Safety == \lnot (\A i, j \in ClientSet:
                            /\ i /= j
                            /\ hasLock[i] 
                            /\ hasLock[j])

\* Properties

ProgressOK(i) == pc[i] = "acquireLock" ~> pc[i] = "criticalSection"
Liveness == \A i \in NodeSet: ProgressOK(i)

=============================================================================
