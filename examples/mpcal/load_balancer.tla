----------------------------- MODULE load_balancer -----------------------------
(***************************************************************************)
(* Specifies a simple load balancer.                                       *)
(***************************************************************************)

\* Extends some built-in TLA+ modules
EXTENDS Naturals, Sequences, TLC

\* The `TCPChannel` mapping macro used in this specification is parameterized
\* by a `BUFFER_SIZE` constant. This value controls the number of messages being
\* held in a buffer by each process. Processes trying to send a message to another
\* process with a full buffer wil "block" (not be scheduled by TLC).
CONSTANT BUFFER_SIZE

\* Define a constant identifier for the load balancer.
LoadBalancerId == 0

\* The number of servers and clients in the model checking setup.
CONSTANTS NUM_SERVERS, NUM_CLIENTS

\* TLC should assume that both numbers are greater than zero (i.e., we always
\* have at least one server and one client). Note, however, that increasing
\* these numbers makes the number of states to be checked by TLC to grow
\* exponentially.
ASSUME NUM_SERVERS > 0 /\ NUM_CLIENTS > 0

\* GET_PAGE is a label attached to messages sent from the clients to
\* the load balancer.
\*
\* WEB_PAGE abstractly represents a web page that the server may return
\* to clients. The content of the webpage is, obviously, orthogonal to the
\* correctness of our load balancer.
CONSTANTS GET_PAGE, WEB_PAGE

\* total nodes in the system:
\*    number of clients + number of  servers + the load balancer
NUM_NODES == NUM_CLIENTS + NUM_SERVERS + 1

(***************************************************************************
--mpcal LoadBalancer {

  \* The TCPChannel mapping macro models a communication channel
  \* between two processes using TCP-like semantics. In particular:
  \*
  \* - reading from the channel "blocks" unless there is a message
  \*   ready to be read.
  \* - message delivery is reliable and ordered (i.e., FIFO).
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

  \* Mapping macros keep implementation-specific behavior that we don't
  \* want to model check outside of our archetype definitions.
  \* In the case of this load balancer, how a server retrieves a web page
  \* is orthogonal to the correctness of the properties we are interested
  \* to check with this specification.
  \*
  \* This mapping macro abstracts the process of reading a web page by
  \* always returning the `WEB_PAGE` constant when the variable is read.
  \*
  \* Since "writing" to this mapping is meaningless, the attempting to write
  \* to a variable mapped with WebPage will result in a model checking
  \* error (see `assert(FALSE)` in the write definition).
  mapping macro WebPages {
     read {
         yield WEB_PAGE;
     }

     write {
         assert(FALSE);
         yield $value;
     }
  }

  \* ALoadBalancer is the archetype that defines the behavior of
  \* the load balancer process. The `mailboxes` parameter represents
  \* connections to all nodes in the system.
  archetype ALoadBalancer(ref mailboxes)

  \* Local variables of this archetype:
  variables
             \* Holds messages received by the load balancer (sent
             \* by clients)
             msg,

             \* identifier attached to every message sent to servers by
             \* the load balancer.
             next = 0;
  {
      main:
        while (TRUE) {

            \* waits for a message to be received. Upon receipt, the `assert`
            \* call ensures that the message is of type `GET_PAGE`, the only
            \* type of message supported in this simple specification.
            \*
            \* Every message received by the load balancer is expected to
            \* be a tuple in the format:
            \*
            \*    << {message_type}, {client_id} >>
            \*
            \* Note that tuples are 1-indexed.
            rcvMsg:
              msg := mailboxes[LoadBalancerId];
              assert(msg[1] = GET_PAGE);

            \* the load balancer needs to forward the client request to the
            \* server, who will process the request and send a web page back to
            \* the client.
            \*
            \* The message sent to the server is a tuple in the format:
            \*
            \*     << {message_id}, {client_id} >>
            \*
            \* We send the client ID here so that the server can directly
            \* reply to a client, bypassing the load balancer. This is usually
            \* not what happens in practice, but the model is simple
            \* enough for our (illustrative) purposes.
            sendServer:
              next := (next % NUM_SERVERS) + 1;
              mailboxes[next] := << next, msg[2] >>;
        }
  }

  \* AServer is the archetype that defines the behavior of the servers
  \* in our system. The two parameters it receives are:
  \*
  \* - mailboxes: contains connections to every node in the system
  \* - page_stream: a source of web pages for the server. In practice,
  \*                this is implementation specific and irrelevant for
  \*                the properties we want to check in this specification
  archetype AServer(ref mailboxes, page_stream)

  \* Local variables
  variable
            \* temporary buffer to hold incoming messages
            msg;
  {
      serverLoop:
        while (TRUE) {

            \* waits for an incoming message. Note that the only process
            \* that sends messages to the server is the load balancer process
            \* (defined according to the ALoadBalancer archetype) and the
            \* message has the format << {message_id}, {client_id} >>
            rcvReq:
              msg := mailboxes[self];

          sendPage:
            \* sends a web page (read from `page_stream`) back to the requester
            \* i.e., the client.
            mailboxes[msg[2]] := page_stream;
        }
  }

  \* GLOBAL VARIABLES *\

  variables
             \* our network is modeled as a function from node identifier
             \* to a sequence of incoming messages
             network = [id \in 0..NUM_NODES |-> <<>>],

             \* the stream of web pages to be served by the server. Since we
             \* intend to map this variable using the WebPages mapping macro,
             \* the initial value assigned to it here is irrelevant.
             stream = 0;

  \* PROCESS INSTANTIATION *\

  \* The system has a single load balancer entity, instantiated from the ALoadBalancer
  \* archetype. The model of our network is going to be the one defined by the TCPChannel
  \* mapping macro in all instantiations.
  fair process (LoadBalancer = LoadBalancerId) == instance ALoadBalancer(ref network)
      mapping network[_] via TCPChannel;

  \* Instantiate `NUM_SERVERS` server processes according to the AServer archetype.
  \* We map the page stream according to the WebPages mapping macro since this is
  \* an implementation detail that needs to be specified during implementation at
  \* a later stage.
  fair process (Servers \in 1..NUM_SERVERS) == instance AServer(ref network, stream)
      mapping network[_] via TCPChannel
      mapping stream via WebPages;

  \* We have a load balancer that waits for messages and servers that are ready
  \* to serve web pages when the load balancer requests. However, there is one
  \* piece missing from this: a _client_ that actually drives the other two
  \* components.
  \*
  \* To illustrate how regular PlusCal processes can be used with Modular PlusCal,
  \* we model the client as a vanilla PlusCal process.



  \* Client processes are given integer identifiers starting from NUM_SERVERS+1.
  \* Keep in mind that this "range" notation in PlusCal defines a set, and is
  \* _inclusive_ (i.e., NUM_SERVERS+NUM_CLIENTS+1 is part of the set).
  \*
  \* Also note that since the client needs to send network messages to processes
  \* defined by the previous archetypes, we need to have the exact same network
  \* model here. However, since mapping macros are not available for regular
  \* PlusCal processes, we need to copy the specification of the TCPChannel
  \* mapping macro in this client definition.
  fair process (Client \in (NUM_SERVERS+1)..(NUM_SERVERS+NUM_CLIENTS+1))

  \* Local variables
  variable
            \* Temporary buffer to hold incoming messages
            msg;
  {
      clientLoop:
        while (TRUE) {

            \* First, the client makes a request to the load balancer.
            \* The format of the message is a tuple: << {message_type}, {client_id} >>.
            \* If you check the ALoadBalancer definition, this is the message format
            \* expected there.
            \*
            \* Remember that `self` is an implicitly defined, immutable variable that
            \* contains the process identifier of the "running" process.
            clientRequest:
              msg := << GET_PAGE, self >>;
              await Len(network[LoadBalancerId]) < BUFFER_SIZE;
              network[LoadBalancerId] := Append(network[LoadBalancerId], msg);


            \* Clients then wait for the response to the previously sent request.
            \* Since there is only one type of web page in this simple specification
            \* (defined by the WEB_PAGE constant), we assert here that the message
            \* received indeed is equal our expected web page.
            clientReceive:
              await Len(network[self]) > 0;
                with (m = Head(network[self])) {
                    network[self] := Tail(network[self]);
                    assert(m = WEB_PAGE);
                };
        }
  }
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm LoadBalancer {
    variables network = [id \in (0)..(NUM_NODES) |-> <<>>], stream = 0;
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
            };

    }
    fair process (Servers \in (1)..(NUM_SERVERS))
    variables msg, mailboxesRead0, mailboxesWrite1, page_streamRead, mailboxesWrite2;
    {
        serverLoop:
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
                    goto serverLoop;

            } else {
                mailboxesWrite2 := network;
                network := mailboxesWrite2;
            };

    }
    fair process (Client \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)))
    variables msg;
    {
        clientLoop:
            while (TRUE) {
                clientRequest:
                    msg := <<GET_PAGE, self>>;
                    await (Len(network[LoadBalancerId]))<(BUFFER_SIZE);
                    network[LoadBalancerId] := Append(network[LoadBalancerId], msg);

                clientReceive:
                    await (Len(network[self]))>(0);
                    with (m = Head(network[self])) {
                        network[self] := Tail(network[self]);
                        assert (m)=(WEB_PAGE);
                    };

            };

    }
}
\* END PLUSCAL TRANSLATION



***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable msg of process LoadBalancer at line 255 col 15 changed to msg_
\* Process variable msg of process Servers at line 283 col 15 changed to msg_S
CONSTANT defaultInitValue
VARIABLES network, stream, pc, msg_, next, mailboxesRead, mailboxesWrite,
          mailboxesWrite0, msg_S, mailboxesRead0, mailboxesWrite1,
          page_streamRead, mailboxesWrite2, msg

vars == << network, stream, pc, msg_, next, mailboxesRead, mailboxesWrite,
           mailboxesWrite0, msg_S, mailboxesRead0, mailboxesWrite1,
           page_streamRead, mailboxesWrite2, msg >>

ProcSet == {LoadBalancerId} \cup ((1)..(NUM_SERVERS)) \cup (((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)))

Init == (* Global variables *)
        /\ network = [id \in (0)..(NUM_NODES) |-> <<>>]
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
        (* Process Client *)
        /\ msg = [self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = LoadBalancerId -> "main"
                                        [] self \in (1)..(NUM_SERVERS) -> "serverLoop"
                                        [] self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)) -> "clientLoop"]

main == /\ pc[LoadBalancerId] = "main"
        /\ IF TRUE
              THEN /\ pc' = [pc EXCEPT ![LoadBalancerId] = "rcvMsg"]
                   /\ UNCHANGED << network, mailboxesWrite0 >>
              ELSE /\ mailboxesWrite0' = network
                   /\ network' = mailboxesWrite0'
                   /\ pc' = [pc EXCEPT ![LoadBalancerId] = "Done"]
        /\ UNCHANGED << stream, msg_, next, mailboxesRead, mailboxesWrite,
                        msg_S, mailboxesRead0, mailboxesWrite1,
                        page_streamRead, mailboxesWrite2, msg >>

rcvMsg == /\ pc[LoadBalancerId] = "rcvMsg"
          /\ (Len(network[LoadBalancerId]))>(0)
          /\ LET msg0 == Head(network[LoadBalancerId]) IN
               /\ mailboxesWrite' = [network EXCEPT ![LoadBalancerId] = Tail(network[LoadBalancerId])]
               /\ mailboxesRead' = msg0
          /\ msg_' = mailboxesRead'
          /\ Assert((msg_'[1])=(GET_PAGE),
                    "Failure of assertion at line 266, column 21.")
          /\ network' = mailboxesWrite'
          /\ pc' = [pc EXCEPT ![LoadBalancerId] = "sendServer"]
          /\ UNCHANGED << stream, next, mailboxesWrite0, msg_S, mailboxesRead0,
                          mailboxesWrite1, page_streamRead, mailboxesWrite2,
                          msg >>

sendServer == /\ pc[LoadBalancerId] = "sendServer"
              /\ next' = ((next)%(NUM_SERVERS))+(1)
              /\ (Len(network[next']))<(BUFFER_SIZE)
              /\ mailboxesWrite' = [network EXCEPT ![next'] = Append(network[next'], <<next', msg_[2]>>)]
              /\ network' = mailboxesWrite'
              /\ pc' = [pc EXCEPT ![LoadBalancerId] = "main"]
              /\ UNCHANGED << stream, msg_, mailboxesRead, mailboxesWrite0,
                              msg_S, mailboxesRead0, mailboxesWrite1,
                              page_streamRead, mailboxesWrite2, msg >>

LoadBalancer == main \/ rcvMsg \/ sendServer

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ IF TRUE
                          THEN /\ pc' = [pc EXCEPT ![self] = "rcvReq"]
                               /\ UNCHANGED << network, mailboxesWrite2 >>
                          ELSE /\ mailboxesWrite2' = [mailboxesWrite2 EXCEPT ![self] = network]
                               /\ network' = mailboxesWrite2'[self]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << stream, msg_, next, mailboxesRead,
                                    mailboxesWrite, mailboxesWrite0, msg_S,
                                    mailboxesRead0, mailboxesWrite1,
                                    page_streamRead, msg >>

rcvReq(self) == /\ pc[self] = "rcvReq"
                /\ (Len(network[self]))>(0)
                /\ LET msg1 == Head(network[self]) IN
                     /\ mailboxesWrite1' = [mailboxesWrite1 EXCEPT ![self] = [network EXCEPT ![self] = Tail(network[self])]]
                     /\ mailboxesRead0' = [mailboxesRead0 EXCEPT ![self] = msg1]
                /\ msg_S' = [msg_S EXCEPT ![self] = mailboxesRead0'[self]]
                /\ network' = mailboxesWrite1'[self]
                /\ pc' = [pc EXCEPT ![self] = "sendPage"]
                /\ UNCHANGED << stream, msg_, next, mailboxesRead,
                                mailboxesWrite, mailboxesWrite0,
                                page_streamRead, mailboxesWrite2, msg >>

sendPage(self) == /\ pc[self] = "sendPage"
                  /\ page_streamRead' = [page_streamRead EXCEPT ![self] = WEB_PAGE]
                  /\ (Len(network[msg_S[self][2]]))<(BUFFER_SIZE)
                  /\ mailboxesWrite1' = [mailboxesWrite1 EXCEPT ![self] = [network EXCEPT ![msg_S[self][2]] = Append(network[msg_S[self][2]], page_streamRead'[self])]]
                  /\ network' = mailboxesWrite1'[self]
                  /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                  /\ UNCHANGED << stream, msg_, next, mailboxesRead,
                                  mailboxesWrite, mailboxesWrite0, msg_S,
                                  mailboxesRead0, mailboxesWrite2, msg >>

Servers(self) == serverLoop(self) \/ rcvReq(self) \/ sendPage(self)

clientLoop(self) == /\ pc[self] = "clientLoop"
                    /\ pc' = [pc EXCEPT ![self] = "clientRequest"]
                    /\ UNCHANGED << network, stream, msg_, next, mailboxesRead,
                                    mailboxesWrite, mailboxesWrite0, msg_S,
                                    mailboxesRead0, mailboxesWrite1,
                                    page_streamRead, mailboxesWrite2, msg >>

clientRequest(self) == /\ pc[self] = "clientRequest"
                       /\ msg' = [msg EXCEPT ![self] = <<GET_PAGE, self>>]
                       /\ (Len(network[LoadBalancerId]))<(BUFFER_SIZE)
                       /\ network' = [network EXCEPT ![LoadBalancerId] = Append(network[LoadBalancerId], msg'[self])]
                       /\ pc' = [pc EXCEPT ![self] = "clientReceive"]
                       /\ UNCHANGED << stream, msg_, next, mailboxesRead,
                                       mailboxesWrite, mailboxesWrite0, msg_S,
                                       mailboxesRead0, mailboxesWrite1,
                                       page_streamRead, mailboxesWrite2 >>

clientReceive(self) == /\ pc[self] = "clientReceive"
                       /\ (Len(network[self]))>(0)
                       /\ LET m == Head(network[self]) IN
                            /\ network' = [network EXCEPT ![self] = Tail(network[self])]
                            /\ Assert((m)=(WEB_PAGE),
                                      "Failure of assertion at line 323, column 25.")
                       /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                       /\ UNCHANGED << stream, msg_, next, mailboxesRead,
                                       mailboxesWrite, mailboxesWrite0, msg_S,
                                       mailboxesRead0, mailboxesWrite1,
                                       page_streamRead, mailboxesWrite2, msg >>

Client(self) == clientLoop(self) \/ clientRequest(self)
                   \/ clientReceive(self)

Next == LoadBalancer
           \/ (\E self \in (1)..(NUM_SERVERS): Servers(self))
           \/ (\E self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)): Client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(LoadBalancer)
        /\ \A self \in (1)..(NUM_SERVERS) : WF_vars(Servers(self))
        /\ \A self \in ((NUM_SERVERS)+(1))..(((NUM_SERVERS)+(NUM_CLIENTS))+(1)) : WF_vars(Client(self))

\* END TRANSLATION


(* INVARIANTS *)


\* This is an _invariant_ of our specification: in other words,
\* we expect the BuffersOk predicate to always be true in every step of execution
BufferOk(node) == Len(network[node]) >= 0 /\ Len(network[node]) <= BUFFER_SIZE
BuffersOk == \A node \in DOMAIN network : BufferOk(node)


(* PROPERTIES *)

\* This is a property we would like to check about our specification.
\* Properties are defined using _temporal logic_. In this specific example,
\* we want to make sure that every client that requests a web page (i.e., are
\* in the 'clientRequest' label) eventually receive a response (i.e., are
\* in the 'clientReceive' label). In order to specify this property, we have to
\* write the formula as if the client enters 'clientReceive' label, it will
\* eventually successfully receive a response and then go back to issuing
\* another request in the 'clientRequest' label.
ReceivesPage(client) == pc[client] = "clientReceive" ~> pc[client] = "clientRequest"
ClientsOk == \A client \in (NUM_SERVERS+1)..(NUM_SERVERS+NUM_CLIENTS+1) : ReceivesPage(client)

=============================================================================
\* Modification History
\* Last modified Wed Feb 06 17:26:45 PST 2019 by minh
\* Last modified Sat Feb 02 19:59:51 PST 2019 by rmc
