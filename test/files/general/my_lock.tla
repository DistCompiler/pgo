------------------------------- MODULE my_lock -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets
CONSTANT NODE_SET

serverID == 1
LockMsg == "Lock!"
UnlockMsg == "Unlock!"
GrantMsg == "Has Lock!"

(********************

--mpcal my_lock {

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
    variables msg, q = <<>> ; 
    {
    serverLoop:
        while(TRUE) {
        serverReceive:
            msg := network[self];
            print(msg);
        serverRespond:
            if (msg.type = LockMsg) {
                print("Receive LockMsg");
                if (q = <<>>) {
                    network[msg.from] := GrantMsg;
                };
                q := Append(q, msg.from);
            } else if (msg.type = UnlockMsg) {
                print("Receive UnlockMsg");
                q := Tail(q);
                if (q # <<>>) {
                    network[Head(q)] := GrantMsg;
                };
            };
        };
    }

    archetype AClient(ref network[_])
    variable msg;
    {
    requestLock:
        network[serverID] := [
            type |-> LockMsg,
            from |-> self
        ];
        print(LockMsg);
    receiveLock:
        msg := network[self];
        print(msg);
        assert(msg = GrantMsg);
    sendUnlock:
        network[serverID] := [type |-> UnlockMsg, from |-> self];
        print(UnlockMsg);
    }
    
    variables network = [id \in NODE_SET |-> <<>>];

    fair process (Server \in {serverID}) == 
        instance AServer(ref network[_])
        mapping network[_] via ReliableFIFOLink;

    fair process (Client \in {2, 0}) == 
        instance AClient(ref network[_])
        mapping network[_] via ReliableFIFOLink;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm my_lock {
  variables network = [id \in NODE_SET |-> <<>>];
  
  fair process (Server \in {serverID})
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
  
  fair process (Client \in {2, 0})
    variables msg0;
  {
    requestLock:
      with (value10 = [type |-> LockMsg, from |-> self]) {
        network := [network EXCEPT ![serverID] = Append((network)[serverID], value10)];
        goto receiveLock;
      };
    receiveLock:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = readMsg10) {
          msg0 := yielded_network00;
          assert (msg0) = (GrantMsg);
          goto sendUnlock;
        };
      };
    sendUnlock:
      with (value20 = [type |-> UnlockMsg, from |-> self]) {
        network := [network EXCEPT ![serverID] = Append((network)[serverID], value20)];
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "eebde993" /\ chksum(tla) = "552c833a")
CONSTANT defaultInitValue
VARIABLES network, pc, msg, q, msg0

vars == << network, pc, msg, q, msg0 >>

ProcSet == ({serverID}) \cup ({2, 0})

Init == (* Global variables *)
        /\ network = [id \in NODE_SET |-> <<>>]
        (* Process Server *)
        /\ msg = [self \in {serverID} |-> defaultInitValue]
        /\ q = [self \in {serverID} |-> <<>>]
        (* Process Client *)
        /\ msg0 = [self \in {2, 0} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in {serverID} -> "serverLoop"
                                        [] self \in {2, 0} -> "requestLock"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "serverReceive"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << network, msg, q, msg0 >>

serverReceive(self) == /\ pc[self] = "serverReceive"
                       /\ (Len((network)[self])) > (0)
                       /\ LET readMsg00 == Head((network)[self]) IN
                            /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                            /\ LET yielded_network1 == readMsg00 IN
                                 /\ msg' = [msg EXCEPT ![self] = yielded_network1]
                                 /\ pc' = [pc EXCEPT ![self] = "serverRespond"]
                       /\ UNCHANGED << q, msg0 >>

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
                       /\ UNCHANGED << msg, msg0 >>

Server(self) == serverLoop(self) \/ serverReceive(self)
                   \/ serverRespond(self)

requestLock(self) == /\ pc[self] = "requestLock"
                     /\ LET value10 == [type |-> LockMsg, from |-> self] IN
                          /\ network' = [network EXCEPT ![serverID] = Append((network)[serverID], value10)]
                          /\ pc' = [pc EXCEPT ![self] = "receiveLock"]
                     /\ UNCHANGED << msg, q, msg0 >>

receiveLock(self) == /\ pc[self] = "receiveLock"
                     /\ (Len((network)[self])) > (0)
                     /\ LET readMsg10 == Head((network)[self]) IN
                          /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                          /\ LET yielded_network00 == readMsg10 IN
                               /\ msg0' = [msg0 EXCEPT ![self] = yielded_network00]
                               /\ Assert((msg0'[self]) = (GrantMsg), 
                                         "Failure of assertion at line 141, column 11.")
                               /\ pc' = [pc EXCEPT ![self] = "sendUnlock"]
                     /\ UNCHANGED << msg, q >>

sendUnlock(self) == /\ pc[self] = "sendUnlock"
                    /\ LET value20 == [type |-> UnlockMsg, from |-> self] IN
                         /\ network' = [network EXCEPT ![serverID] = Append((network)[serverID], value20)]
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << msg, q, msg0 >>

Client(self) == requestLock(self) \/ receiveLock(self) \/ sendUnlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {serverID}: Server(self))
           \/ (\E self \in {2, 0}: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {serverID} : WF_vars(Server(self))
        /\ \A self \in {2, 0} : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
HasLock(self) == pc[self] = "sendUnlock"
Exclusivity == \A i,j \in (ProcSet \ {serverID}): (pc[i] = "sendUnlock" /\ pc[j] = "sendUnlock") => i = j

ClientSet == ProcSet \ {serverID}
Exclusivity2 == \A i \in ClientSet : HasLock(i) => \lnot \E j \in ClientSet : i # j /\ HasLock(j)

ClientTermination == <>(\A self \in ClientSet: pc[self] = "Done")
=============================================================================
