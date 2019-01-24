----------------------------- MODULE load_balancer -----------------------------
(***************************************************************************)
(* Load balancer example in Modular PlusCal.                               *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC
CONSTANT BUFFER_SIZE, SERVER_CAPACITY

LoadBalancerId == 0
CONSTANTS NUM_SERVERS, NUM_CLIENTS

CONSTANTS GET_PAGE, WEB_PAGE

(* total nodes in the system: number of clients + number of  servers + the load balancer *)
NUM_NODES == NUM_CLIENTS + NUM_SERVERS + 1

(***************************************************************************
--mpcal LoadBalancer {
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

  mapping macro WebPages {
     read {
         yield WEB_PAGE
     }
     
     write {
         yield FALSE
     }
  }

  archetype ALoadBalancer(ref mailboxes)
  variables msg, next = 0; {
      main: while (TRUE) {
              rcvMsg: msg := mailboxes[LoadBalancerId];
                      assert(msg[1] = GET_PAGE);
                      
              sendServer: next := (next % NUM_SERVERS) + 1;
                          mailboxes[next] := << next, msg[2] >>;
                          
      }
  }

  archetype AServer(ref mailboxes, page_stream)
  variable msg; {
      p: while (TRUE) {
          rcvReq: msg := mailboxes[self];
          
          sendPage: mailboxes[msg[2]] := page_stream;
      }
  }
  
  variables network = [id \in 0..NUM_NODES |-> <<>>],
            processor = 0,
            stream = 0;

  fair process (LoadBalancer = LoadBalancerId) == instance ALoadBalancer(ref network)
      mapping network[_] via TCPChannel;
  fair process (Servers \in 1..NUM_SERVERS) == instance AServer(ref network, ref stream)
      mapping network[_] via TCPChannel
      mapping stream via WebPages;
      
  fair process (Browser \in (NUM_SERVERS+1)..(NUM_SERVERS+1+NUM_CLIENTS))
  variable msg; {
      main: while (TRUE) {
                req: msg := << GET_PAGE, self >>;
                     await Len(network[LoadBalancerId]) < BUFFER_SIZE;
                     network[LoadBalancerId] := Append(network[LoadBalancerId], msg);
                     
                     
                rcv: await Len(network[self]) > 0;
                     with (m = Head(network[self])) {
                         network[self] := Tail(network[self]);
                         assert(m = WEB_PAGE);
                     };
            }
  }
}

--algorithm LoadBalancer {
    variables network = [id \in (0)..(NUM_NODES) |-> <<>>], processor = 0, stream = 0;
    fair process (LoadBalancer = LoadBalancerId)
    variables msg, next = 0, mailboxesRead, mailboxesWrite, mailboxesWrite0;
    {
        main:
            if (TRUE) {
                rcvMsg:
                    await (Len(network[LoadBalancerId]))>(0);
                    with (msg0 = Head(network[LoadBalancerId])) {
                        mailboxesWrite := [network EXCEPT ![LoadBalancerId] = Tail(network[LoadBalancerId])];
                        mailboxesRead := msg0;
                    };
                    msg := mailboxesRead;
                    assert (msg[1])=(GET_PAGE);
                    network := mailboxesWrite;
                
                sendServer:
                    next := ((next)%(NUM_SERVERS))+(1);
                    await (Len(network[next]))<(BUFFER_SIZE);
                    mailboxesWrite := [network EXCEPT ![next] = Append(network[next], <<next, msg[2]>>)];
                    network := mailboxesWrite;
                    goto main;
            
            } else {
                mailboxesWrite0 := network;
                network := mailboxesWrite0;
            }
    
    }
    fair process (Servers \in (1)..(NUM_SERVERS))
    variables msg, mailboxesRead0, mailboxesWrite1, page_streamRead, mailboxesWrite2;
    {
        p:
            if (TRUE) {
                rcvReq:
                    await (Len(network[self]))>(0);
                    with (msg1 = Head(network[self])) {
                        mailboxesWrite1 := [network EXCEPT ![self] = Tail(network[self])];
                        mailboxesRead0 := msg1;
                    };
                    msg := mailboxesRead0;
                    network := mailboxesWrite1;
                
                sendPage:
                    page_streamRead := WEB_PAGE;
                    await (Len(network[msg[2]]))<(BUFFER_SIZE);
                    mailboxesWrite1 := [network EXCEPT ![msg[2]] = Append(network[msg[2]], page_streamRead)];
                    network := mailboxesWrite1;
                    goto p;
            
            } else {
                mailboxesWrite2 := network;
                network := mailboxesWrite2;
            }
    
    }
    fair process (Browser \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)))
    variables msg;
    {
        main:
            while (TRUE) {
                req:
                    msg := <<GET_PAGE, self>>;
                    await (Len(network[LoadBalancerId]))<(BUFFER_SIZE);
                    network[LoadBalancerId] := Append(network[LoadBalancerId], msg);
                
                rcv:
                    await (Len(network[self]))>(0);
                    with (m = Head(network[self])) {
                        network[self] := Tail(network[self]);
                        assert (m)=(WEB_PAGE);
                    };
            
            };
    
    }
}




***************************************************************************)
\* BEGIN TRANSLATION
\* Label main of process LoadBalancer at line 98 col 13 changed to main_
\* Process variable msg of process LoadBalancer at line 95 col 15 changed to msg_
\* Process variable msg of process Servers at line 123 col 15 changed to msg_S
CONSTANT defaultInitValue
VARIABLES network, processor, stream, pc, msg_, next, mailboxesRead, 
          mailboxesWrite, mailboxesWrite0, msg_S, mailboxesRead0, 
          mailboxesWrite1, page_streamRead, mailboxesWrite2, msg

vars == << network, processor, stream, pc, msg_, next, mailboxesRead, 
           mailboxesWrite, mailboxesWrite0, msg_S, mailboxesRead0, 
           mailboxesWrite1, page_streamRead, mailboxesWrite2, msg >>

ProcSet == {LoadBalancerId} \cup ((1)..(NUM_SERVERS)) \cup (((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)))

Init == (* Global variables *)
        /\ network = [id \in (0)..(NUM_NODES) |-> <<>>]
        /\ processor = 0
        /\ stream = 0
        (* Process LoadBalancer *)
        /\ msg_ = defaultInitValue
        /\ next = 0
        /\ mailboxesRead = defaultInitValue
        /\ mailboxesWrite = defaultInitValue
        /\ mailboxesWrite0 = defaultInitValue
        (* Process Servers *)
        /\ msg_S = [self \in (1)..(NUM_SERVERS) |-> defaultInitValue]
        /\ mailboxesRead0 = [self \in (1)..(NUM_SERVERS) |-> defaultInitValue]
        /\ mailboxesWrite1 = [self \in (1)..(NUM_SERVERS) |-> defaultInitValue]
        /\ page_streamRead = [self \in (1)..(NUM_SERVERS) |-> defaultInitValue]
        /\ mailboxesWrite2 = [self \in (1)..(NUM_SERVERS) |-> defaultInitValue]
        (* Process Browser *)
        /\ msg = [self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = LoadBalancerId -> "main_"
                                        [] self \in (1)..(NUM_SERVERS) -> "p"
                                        [] self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)) -> "main"]

main_ == /\ pc[LoadBalancerId] = "main_"
         /\ IF TRUE
               THEN /\ pc' = [pc EXCEPT ![LoadBalancerId] = "rcvMsg"]
                    /\ UNCHANGED << network, mailboxesWrite0 >>
               ELSE /\ mailboxesWrite0' = network
                    /\ network' = mailboxesWrite0'
                    /\ pc' = [pc EXCEPT ![LoadBalancerId] = "Done"]
         /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                         mailboxesWrite, msg_S, mailboxesRead0, 
                         mailboxesWrite1, page_streamRead, mailboxesWrite2, 
                         msg >>

rcvMsg == /\ pc[LoadBalancerId] = "rcvMsg"
          /\ (Len(network[LoadBalancerId]))>(0)
          /\ LET msg0 == Head(network[LoadBalancerId]) IN
               /\ mailboxesWrite' = [network EXCEPT ![LoadBalancerId] = Tail(network[LoadBalancerId])]
               /\ mailboxesRead' = msg0
          /\ msg_' = mailboxesRead'
          /\ Assert((msg_'[1])=(GET_PAGE), 
                    "Failure of assertion at line 106, column 21.")
          /\ network' = mailboxesWrite'
          /\ pc' = [pc EXCEPT ![LoadBalancerId] = "sendServer"]
          /\ UNCHANGED << processor, stream, next, mailboxesWrite0, msg_S, 
                          mailboxesRead0, mailboxesWrite1, page_streamRead, 
                          mailboxesWrite2, msg >>

sendServer == /\ pc[LoadBalancerId] = "sendServer"
              /\ next' = ((next)%(NUM_SERVERS))+(1)
              /\ (Len(network[next']))<(BUFFER_SIZE)
              /\ mailboxesWrite' = [network EXCEPT ![next'] = Append(network[next'], <<next', msg_[2]>>)]
              /\ network' = mailboxesWrite'
              /\ pc' = [pc EXCEPT ![LoadBalancerId] = "main_"]
              /\ UNCHANGED << processor, stream, msg_, mailboxesRead, 
                              mailboxesWrite0, msg_S, mailboxesRead0, 
                              mailboxesWrite1, page_streamRead, 
                              mailboxesWrite2, msg >>

LoadBalancer == main_ \/ rcvMsg \/ sendServer

p(self) == /\ pc[self] = "p"
           /\ IF TRUE
                 THEN /\ pc' = [pc EXCEPT ![self] = "rcvReq"]
                      /\ UNCHANGED << network, mailboxesWrite2 >>
                 ELSE /\ mailboxesWrite2' = [mailboxesWrite2 EXCEPT ![self] = network]
                      /\ network' = mailboxesWrite2'[self]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                           mailboxesWrite, mailboxesWrite0, msg_S, 
                           mailboxesRead0, mailboxesWrite1, page_streamRead, 
                           msg >>

rcvReq(self) == /\ pc[self] = "rcvReq"
                /\ (Len(network[self]))>(0)
                /\ LET msg1 == Head(network[self]) IN
                     /\ mailboxesWrite1' = [mailboxesWrite1 EXCEPT ![self] = [network EXCEPT ![self] = Tail(network[self])]]
                     /\ mailboxesRead0' = [mailboxesRead0 EXCEPT ![self] = msg1]
                /\ msg_S' = [msg_S EXCEPT ![self] = mailboxesRead0'[self]]
                /\ network' = mailboxesWrite1'[self]
                /\ pc' = [pc EXCEPT ![self] = "sendPage"]
                /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                                mailboxesWrite, mailboxesWrite0, 
                                page_streamRead, mailboxesWrite2, msg >>

sendPage(self) == /\ pc[self] = "sendPage"
                  /\ page_streamRead' = [page_streamRead EXCEPT ![self] = WEB_PAGE]
                  /\ (Len(network[msg_S[self][2]]))<(BUFFER_SIZE)
                  /\ mailboxesWrite1' = [mailboxesWrite1 EXCEPT ![self] = [network EXCEPT ![msg_S[self][2]] = Append(network[msg_S[self][2]], page_streamRead'[self])]]
                  /\ network' = mailboxesWrite1'[self]
                  /\ pc' = [pc EXCEPT ![self] = "p"]
                  /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                                  mailboxesWrite, mailboxesWrite0, msg_S, 
                                  mailboxesRead0, mailboxesWrite2, msg >>

Servers(self) == p(self) \/ rcvReq(self) \/ sendPage(self)

main(self) == /\ pc[self] = "main"
              /\ pc' = [pc EXCEPT ![self] = "req"]
              /\ UNCHANGED << network, processor, stream, msg_, next, 
                              mailboxesRead, mailboxesWrite, mailboxesWrite0, 
                              msg_S, mailboxesRead0, mailboxesWrite1, 
                              page_streamRead, mailboxesWrite2, msg >>

req(self) == /\ pc[self] = "req"
             /\ msg' = [msg EXCEPT ![self] = <<GET_PAGE, self>>]
             /\ (Len(network[LoadBalancerId]))<(BUFFER_SIZE)
             /\ network' = [network EXCEPT ![LoadBalancerId] = Append(network[LoadBalancerId], msg'[self])]
             /\ pc' = [pc EXCEPT ![self] = "rcv"]
             /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                             mailboxesWrite, mailboxesWrite0, msg_S, 
                             mailboxesRead0, mailboxesWrite1, page_streamRead, 
                             mailboxesWrite2 >>

rcv(self) == /\ pc[self] = "rcv"
             /\ (Len(network[self]))>(0)
             /\ LET m == Head(network[self]) IN
                  /\ network' = [network EXCEPT ![self] = Tail(network[self])]
                  /\ Assert((m)=(WEB_PAGE), 
                            "Failure of assertion at line 163, column 25.")
             /\ pc' = [pc EXCEPT ![self] = "main"]
             /\ UNCHANGED << processor, stream, msg_, next, mailboxesRead, 
                             mailboxesWrite, mailboxesWrite0, msg_S, 
                             mailboxesRead0, mailboxesWrite1, page_streamRead, 
                             mailboxesWrite2, msg >>

Browser(self) == main(self) \/ req(self) \/ rcv(self)

Next == LoadBalancer
           \/ (\E self \in (1)..(NUM_SERVERS): Servers(self))
           \/ (\E self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)): Browser(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(LoadBalancer)
        /\ \A self \in (1)..(NUM_SERVERS) : WF_vars(Servers(self))
        /\ \A self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(1))+(NUM_CLIENTS)) : WF_vars(Browser(self))

\* END TRANSLATION


(* INVARIANTS *)


(* no buffers over/underflow *)
BufferOk(node) == Len(network[node]) >= 0 /\ Len(network[node]) <= BUFFER_SIZE
BuffersOk == \A node \in DOMAIN network : BufferOk(node)


(* PROPERTIES *)

(* a client that requests a web page eventually receives it *)
ReceivesPage(client) == pc[client] = "rcv" ~> pc[client] = "req"
ClientsOk == \A client \in (NUM_SERVERS+1)..(NUM_SERVERS+1+NUM_CLIENTS) : ReceivesPage(client)

=============================================================================
\* Modification History
\* Last modified Thu Jan 24 14:46:52 PST 2019 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
