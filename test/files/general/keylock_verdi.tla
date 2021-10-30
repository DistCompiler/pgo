------------------------------ MODULE keylock_verdi ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NUM_CLIENTS

ASSUME NUM_CLIENTS > 0

(* --mpcal keylock_verdi {

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
    server_l1: 
        \* message is whatever we have received from the network
        msg := network[self];
        \* print <<"Server: receive msg ", msg>>;
    
    server_l2:
        \* Check if message is asking for the lock
        if (msg.type = LockMsgType) {
            \* If no one else was waiting for the lock
            if (s = <<>>) {
                \*  Directly send the grant to where the message came from
                reply := [from |-> self, type |-> GrantMsgType];
                \* print <<"Server: send grant reply (immediately) ", reply>>;
                network[msg.from] := reply;
            };
            \* Add the new client to our list of clients
            s := Append(s, msg.from);
        \* Check if message is trying to give lock back to server
        } else if (msg.type = UnlockMsgType) {
            \* Move the head of the list to the next client
            s := Tail(s);
            \* print <<"new head of set ", s>>;
            \* If the list of clients is not empty then grant the lock to the next client
            if (s # <<>>) {
                reply := [from |-> self, type |-> GrantMsgType];
                \* print <<"Server: send grant reply (on new head) ", reply>>;
                network[Head(s)] := reply;
            };
        };

        goto server_l1;
    }

    archetype AClient(ref network[_])
    variables request, msg;
    {

    client_l1:
        \* Send a request to get the lock
        request := [from |-> self, type |-> LockMsgType];
        \* print <<"Client: acquire lock request ", request>>;
        network[LOCK_SERVER_ID] := request;
    
    client_l2:
        \* Wait for the response to come back from the server
        msg := network[self];
        \* print <<"Client: receive msg ", msg>>;
        assert msg.type = GrantMsgType;

    client_l3:
        \* Return the lock back to the server
        request := [from |-> self, type |-> UnlockMsgType];
        \* print <<"Client: return lock request ", request>>;
        network[LOCK_SERVER_ID] := request;

        goto client_l1;
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
--algorithm keylock_verdi {
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
    server_l1:
      await (Len((network)[self])) > (0);
      with (readMsg00 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network1 = readMsg00) {
          msg := yielded_network1;
          goto server_l2;
        };
      };
    server_l2:
      if(((msg).type) = (LockMsgType)) {
        if((s) = (<<>>)) {
          reply := [from |-> self, type |-> GrantMsgType];
          with (value3 = reply) {
            network := [network EXCEPT ![(msg).from] = Append((network)[(msg).from], value3)];
            s := Append(s, (msg).from);
            goto server_l1;
          };
        } else {
          s := Append(s, (msg).from);
          goto server_l1;
        };
      } else {
        if(((msg).type) = (UnlockMsgType)) {
          s := Tail(s);
          if((s) # (<<>>)) {
            reply := [from |-> self, type |-> GrantMsgType];
            with (value00 = reply) {
              network := [network EXCEPT ![Head(s)] = Append((network)[Head(s)], value00)];
              goto server_l1;
            };
          } else {
            goto server_l1;
          };
        } else {
          goto server_l1;
        };
      };
  }
  
  fair process (Client \in CLIENT_SET)
    variables request; msg0;
  {
    client_l1:
      request := [from |-> self, type |-> LockMsgType];
      with (value10 = request) {
        network := [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value10)];
        goto client_l2;
      };
    client_l2:
      await (Len((network)[self])) > (0);
      with (readMsg10 = Head((network)[self])) {
        network := [network EXCEPT ![self] = Tail((network)[self])];
        with (yielded_network00 = readMsg10) {
          msg0 := yielded_network00;
          assert ((msg0).type) = (GrantMsgType);
          goto client_l3;
        };
      };
    client_l3:
      request := [from |-> self, type |-> UnlockMsgType];
      with (value20 = request) {
        network := [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value20)];
        goto client_l1;
      };
  }
}

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION (chksum(pcal) = "b2f67e3" /\ chksum(tla) = "c3771088")
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
        /\ pc = [self \in ProcSet |-> CASE self \in LOCK_SERVER_SET -> "server_l1"
                                        [] self \in CLIENT_SET -> "client_l1"]

server_l1(self) == /\ pc[self] = "server_l1"
                   /\ (Len((network)[self])) > (0)
                   /\ LET readMsg00 == Head((network)[self]) IN
                        /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                        /\ LET yielded_network1 == readMsg00 IN
                             /\ msg' = [msg EXCEPT ![self] = yielded_network1]
                             /\ pc' = [pc EXCEPT ![self] = "server_l2"]
                   /\ UNCHANGED << s, reply, request, msg0 >>

server_l2(self) == /\ pc[self] = "server_l2"
                   /\ IF ((msg[self]).type) = (LockMsgType)
                         THEN /\ IF (s[self]) = (<<>>)
                                    THEN /\ reply' = [reply EXCEPT ![self] = [from |-> self, type |-> GrantMsgType]]
                                         /\ LET value3 == reply'[self] IN
                                              /\ network' = [network EXCEPT ![(msg[self]).from] = Append((network)[(msg[self]).from], value3)]
                                              /\ s' = [s EXCEPT ![self] = Append(s[self], (msg[self]).from)]
                                              /\ pc' = [pc EXCEPT ![self] = "server_l1"]
                                    ELSE /\ s' = [s EXCEPT ![self] = Append(s[self], (msg[self]).from)]
                                         /\ pc' = [pc EXCEPT ![self] = "server_l1"]
                                         /\ UNCHANGED << network, reply >>
                         ELSE /\ IF ((msg[self]).type) = (UnlockMsgType)
                                    THEN /\ s' = [s EXCEPT ![self] = Tail(s[self])]
                                         /\ IF (s'[self]) # (<<>>)
                                               THEN /\ reply' = [reply EXCEPT ![self] = [from |-> self, type |-> GrantMsgType]]
                                                    /\ LET value00 == reply'[self] IN
                                                         /\ network' = [network EXCEPT ![Head(s'[self])] = Append((network)[Head(s'[self])], value00)]
                                                         /\ pc' = [pc EXCEPT ![self] = "server_l1"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "server_l1"]
                                                    /\ UNCHANGED << network, 
                                                                    reply >>
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "server_l1"]
                                         /\ UNCHANGED << network, s, reply >>
                   /\ UNCHANGED << msg, request, msg0 >>

LockServer(self) == server_l1(self) \/ server_l2(self)

client_l1(self) == /\ pc[self] = "client_l1"
                   /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> LockMsgType]]
                   /\ LET value10 == request'[self] IN
                        /\ network' = [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value10)]
                        /\ pc' = [pc EXCEPT ![self] = "client_l2"]
                   /\ UNCHANGED << msg, s, reply, msg0 >>

client_l2(self) == /\ pc[self] = "client_l2"
                   /\ (Len((network)[self])) > (0)
                   /\ LET readMsg10 == Head((network)[self]) IN
                        /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                        /\ LET yielded_network00 == readMsg10 IN
                             /\ msg0' = [msg0 EXCEPT ![self] = yielded_network00]
                             /\ Assert(((msg0'[self]).type) = (GrantMsgType), 
                                       "Failure of assertion at line 186, column 11.")
                             /\ pc' = [pc EXCEPT ![self] = "client_l3"]
                   /\ UNCHANGED << msg, s, reply, request >>

client_l3(self) == /\ pc[self] = "client_l3"
                   /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> UnlockMsgType]]
                   /\ LET value20 == request'[self] IN
                        /\ network' = [network EXCEPT ![LOCK_SERVER_ID] = Append((network)[LOCK_SERVER_ID], value20)]
                        /\ pc' = [pc EXCEPT ![self] = "client_l1"]
                   /\ UNCHANGED << msg, s, reply, msg0 >>

Client(self) == client_l1(self) \/ client_l2(self) \/ client_l3(self)

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
\* Last modified Fri Oct 29 18:58:20 PDT 2021 by ruchitpalrecha
\* Created Tue Oct 12 23:33:39 PDT 2021 by ruchitpalrecha
