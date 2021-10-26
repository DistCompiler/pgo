------------------------------ MODULE keylock ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NUM_CLIENTS

ASSUME NUM_CLIENTS > 0

(* --mpcal keylock {

    define {
        GrantMsgType == 1
        UnlockMsgType == 2
        LockMsgType == 3

        LOCK_SERVER_ID == 1
        LOCK_SERVER_SET == {LOCK_SERVER_ID}
        CLIENT_SET == 2..(NUM_CLIENTS+1)

        NODE_SET == 1..(NUM_CLIENTS+1)
    }

    \* Mapping macros handles logic for the network
    mapping macro ReliableFIFOLink {
        \* When you receive data 
        read {
            \* Wait till you get data (buffer > 0)
            await Len($variable) > 0;
            with (readMsg = Head($variable)) {
                $variable := Tail($variable);
                yield readMsg;
            };
        }
        \* When you want to send data
        write {
            \* Add the data to the end of the buffer
            yield Append($variable, $value);
        }
    }

    \* Archetypes handles logic for the processes  
    archetype AServer(ref network[_])
    \* When do these variables get instantiated?
    variables msg, s = <<>>, reply;
    {
    l1: 
        \* message is whatever we have received from the network
        msg := network[self];
        print("Server: receive msg");
        print(msg);
    
    l2:
        \* Check if message is asking for the lock
        if (msg.type = LockMsgType) {
            \* If no one else was waiting for the lock
            if (s = <<>>) {
                \*  Directly send the grant to where the message came from
                reply := [from |-> self, type |-> GrantMsgType];
                print("Server: send grant reply (immediately)");
                print(reply);
                network[msg.from] := reply;
            };
            \* Add the new client to our list of clients
            s := Append(s, msg.from);
        \* Check if message is trying to give lock back to server
        } else if (msg.type = UnlockMsgType) {
            \* Move the head of the list to the next client
            s := Tail(s);
            print("new head of set");
            print(s);
            \* If the list of clients is not empty then grant the lock to the next client
            if (s # <<>>) {
                reply := [from |-> self, type |-> GrantMsgType];
                print("Server: send grant reply (on new head)");
                print(reply);
                network[Head(s)] := reply;
            };
        };
    }

    archetype AClient(ref network[_])
    variables request, msg;
    {

    l1:
        \* Send a request to get the lock
        request := [from |-> self, type |-> LockMsgType];
        print(request);
        network[LOCK_SERVER_ID] := request;
    
    l2:
        \* Wait for the response to come back from the server
        msg := network[self];
        print(msg);
        assert msg.type = GrantMsgType;

    l3:
        \* Return the lock back to the server
        request := [from |-> self, type |-> UnlockMsgType];
        print(request);
        network[LOCK_SERVER_ID] := request;
    }

    variables 
        \* Give everyone (server + clients) in the network an id
        network = [id \in NODE_SET |-> <<>>];

    \* Start the server and client processes based off the archetype and mapping of the mapping macro
    fair process (LockServer \in LOCK_SERVER_SET) == instance AServer(ref network[_])
        mapping network[_] via ReliableFIFOLink;
    fair process (Client \in CLIENT_SET) == instance AClient(ref network[_])
        mapping network[_] via ReliableFIFOLink;
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm keylock {
  variables network = [id \in NODE_SET |-> <<>>];
  define{
    GrantMsgType == 1
    UnlockMsgType == 2
    LockMsgType == 3
    LOCK_SERVER_ID == 1
    LOCK_SERVER_SET == {LOCK_SERVER_ID}
    CLIENT_SET == (2) .. ((NUM_CLIENTS) + (1))
    NODE_SET == (1) .. ((NUM_CLIENTS) + (1))
  }
  
  fair process (LockServer \in LOCK_SERVER_SET)
    variables msg; s = <<>>; reply;
  {
    l1:
      await (Len((network)[self])) > (0);
      with (readMsg00 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network1 = readMsg00) {
          msg := yielded_network1;
          print "Server: receive msg";
          print msg;
          goto l2;
        };
      };
    l2:
      if(((msg).type) = (LockMsgType)) {
        if((s) = (<<>>)) {
          reply := [from |-> self, type |-> GrantMsgType];
          print "Server: send grant reply \(immediately\)";
          print reply;
          with (value3 = reply) {
            network := [network EXCEPT ![(msg).from] = Append((network)[(msg).from], value3)];
            s := Append(s, (msg).from);
            goto Done;
          };
        } else {
          s := Append(s, (msg).from);
          goto Done;
        };
      } else {
        if(((msg).type) = (UnlockMsgType)) {
          s := Tail(s);
          print "new head of set";
          print s;
          if((s) # (<<>>)) {
            reply := [from |-> self, type |-> GrantMsgType];
            print "Server: send grant reply (on new head\)";
            print reply;
            with (value00 = reply) {
              network := [network EXCEPT ![Head(s)] = Append((network)[Head(s)], value00)];
              goto Done;
            };
          } else {
            goto Done;
          };
        } else {
          goto Done;
        };
      };
  }
  
  fair process (Client \in CLIENT_SET)
    variables request; msg0;
  {
    l1:
      request := [from |-> self, type |-> LockMsgType];
      print request;
      with (value10 = request) {
        network := [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value10)];
        goto l2;
      };
    l2:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = readMsg10) {
          msg0 := yielded_network00;
          print msg0;
          assert ((msg0).type) = (GrantMsgType);
          goto l3;
        };
      };
    l3:
      request := [from |-> self, type |-> UnlockMsgType];
      print request;
      with (value20 = request) {
        network := [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value20)];
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION
\* Label l1 of process LockServer at line 129 col 7 changed to l1_
\* Label l2 of process LockServer at line 140 col 7 changed to l2_
CONSTANT defaultInitValue
VARIABLES network, pc

(* define statement *)
GrantMsgType == 1
UnlockMsgType == 2
LockMsgType == 3
LOCK_SERVER_ID == 1
LOCK_SERVER_SET == {LOCK_SERVER_ID}
CLIENT_SET == (2) .. ((NUM_CLIENTS) + (1))
NODE_SET == (1) .. ((NUM_CLIENTS) + (1))

VARIABLES msg, s, reply, request, msg0

vars == << network, pc, msg, s, reply, request, msg0 >>

ProcSet == (LOCK_SERVER_SET) \cup (CLIENT_SET)

Init == (* Global variables *)
        /\ network = [id \in NODE_SET |-> <<>>]
        (* Process LockServer *)
        /\ msg = [self \in LOCK_SERVER_SET |-> defaultInitValue]
        /\ s = [self \in LOCK_SERVER_SET |-> <<>>]
        /\ reply = [self \in LOCK_SERVER_SET |-> defaultInitValue]
        (* Process Client *)
        /\ request = [self \in CLIENT_SET |-> defaultInitValue]
        /\ msg0 = [self \in CLIENT_SET |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in LOCK_SERVER_SET -> "l1_"
                                        [] self \in CLIENT_SET -> "l1"]

l1_(self) == /\ pc[self] = "l1_"
             /\ (Len((network)[self])) > (0)
             /\ LET readMsg00 == Head((network)[self]) IN
                  /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                  /\ LET yielded_network1 == readMsg00 IN
                       /\ msg' = [msg EXCEPT ![self] = yielded_network1]
                       /\ PrintT("Server: receive:")
                       /\ PrintT(msg'[self])
                       /\ pc' = [pc EXCEPT ![self] = "l2_"]
             /\ UNCHANGED << s, reply, request, msg0 >>

l2_(self) == /\ pc[self] = "l2_"
             /\ IF ((msg[self]).type) = (LockMsgType)
                   THEN /\ IF (s[self]) = (<<>>)
                              THEN /\ reply' = [reply EXCEPT ![self] = [from |-> self, type |-> GrantMsgType]]
                                   /\ PrintT(reply'[self])
                                   /\ LET value3 == reply'[self] IN
                                        /\ network' = [network EXCEPT ![(msg[self]).from] = Append((network)[(msg[self]).from], value3)]
                                        /\ s' = [s EXCEPT ![self] = Append(s[self], (msg[self]).from)]
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                              ELSE /\ s' = [s EXCEPT ![self] = Append(s[self], (msg[self]).from)]
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << network, reply >>
                   ELSE /\ IF ((msg[self]).type) = (UnlockMsgType)
                              THEN /\ s' = [s EXCEPT ![self] = Tail(s[self])]
                                   /\ PrintT(s'[self])
                                   /\ IF (s'[self]) # (<<>>)
                                         THEN /\ reply' = [reply EXCEPT ![self] = [from |-> self, type |-> GrantMsgType]]
                                              /\ PrintT(reply'[self])
                                              /\ LET value00 == reply'[self] IN
                                                   /\ network' = [network EXCEPT ![Head(s'[self])] = Append((network)[Head(s'[self])], value00)]
                                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                              /\ UNCHANGED << network, reply >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << network, s, reply >>
             /\ UNCHANGED << msg, request, msg0 >>

LockServer(self) == l1_(self) \/ l2_(self)

l1(self) == /\ pc[self] = "l1"
            /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> LockMsgType]]
            /\ PrintT(request'[self])
            /\ LET value10 == request'[self] IN
                 /\ network' = [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value10)]
                 /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << msg, s, reply, msg0 >>

l2(self) == /\ pc[self] = "l2"
            /\ (Len((network)[self])) > (0)
            /\ LET readMsg10 == Head((network)[self]) IN
                 /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                 /\ LET yielded_network00 == readMsg10 IN
                      /\ msg0' = [msg0 EXCEPT ![self] = yielded_network00]
                      /\ PrintT(msg0'[self])
                      /\ Assert(((msg0'[self]).type) = (GrantMsgType), 
                                "Failure of assertion at line 190, column 11.")
                      /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << msg, s, reply, request >>

l3(self) == /\ pc[self] = "l3"
            /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> UnlockMsgType]]
            /\ PrintT(request'[self])
            /\ LET value20 == request'[self] IN
                 /\ network' = [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value20)]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << msg, s, reply, msg0 >>

Client(self) == l1(self) \/ l2(self) \/ l3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in LOCK_SERVER_SET: LockServer(self))
           \/ (\E self \in CLIENT_SET: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in LOCK_SERVER_SET : WF_vars(LockServer(self))
        /\ \A self \in CLIENT_SET : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Fri Oct 22 11:50:33 PDT 2021 by ruchitpalrecha
\* Created Tue Oct 12 23:33:39 PDT 2021 by ruchitpalrecha
