----------------------------- MODULE replicated_kv -----------------------------
(***************************************************************************************)
(* Specifies a simple replicated Key-Value store in MPCal.                             *)
(*                                                                                     *)
(* Specifies a replicated state machines (RSM) approach as described in:               *)
(*                                                                                     *)
(* Implementing fault-tolerant services using the state machine approach: a tutorial.  *)
(* http://dl.acm.org/citation.cfm?id=98167                                             *)
(***************************************************************************************)

\* Use some built-in TLA+ modules
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Constant Definitions
\* --------------------

\* Defines the size of the network buffer in a FIFOChannel (the mapping macro).
\*
\* TLC will explore states with up to `BUFFER_SIZE` messages being held on the buffer.
\* If the communication buffer is full, a process that attempts to send a message will not
\* run until a message on the other end of the channel is received.
CONSTANT BUFFER_SIZE

\* Defines the number of key-value store replicas and clients in the system. The specification
\* is orthogonal to these numbers. Note, however, that increasing the number of replicas and/or
\* clients exponentially increases the state space that TLC needs to explore in order to model
\* check your specification.
CONSTANTS NUM_REPLICAS, NUM_CLIENTS

\* When a client sends a message to a replica, the client needs to be able to identify
\* what type of message it just received. These constants below are such labels. Make sure
\* to give them distinct concrete values when model checking.
CONSTANTS DISCONNECT_MSG, GET_MSG, PUT_MSG, NULL_MSG

\* labels that identify a payload corresponds to the response of a previously issues Get
\* or Put request.
CONSTANTS GET_RESPONSE, PUT_RESPONSE

\* The payload of a message sent by the replica when a `PUT` request is successful.
CONSTANT PUT_OK

\* an arbitrary `NULL` value. We model the underlying key-value store as a function from
\* a certain key-space (function domain) to this `NULL` element. When a client issues a `PUT`
\* request, the database is updated and the key being set no longer maps to `NULL`.
CONSTANT NULL

\* Defines which keys are used by clients when performing Get and Put operations
\* Since we are interested to test properties like message stability detection
\* and the semantics of the database, we keep these constant throughout model checking.
CONSTANT GET_KEY, PUT_KEY

\* Whenever clients issue PUT requests, they set keys to the value declared in this constant.
CONSTANT PUT_VALUE

\* Defines the set of keys a client may set. In this specification, we restrict
\* it to them to GET_KEY and PUT_KEY
KeySpace == { GET_KEY, PUT_KEY }

\* We have clients that perform each of the operations supported by our Replicated KV-store:
\* Get, Put, Disconnect, and ClockUpdate (or 'null' request). PlusCal requires that every process
\* has a unique identifier. The set definitions below just ensure that our clients have
\* consecutive identifiers.
GetSet == (NUM_REPLICAS+1)..(NUM_REPLICAS+NUM_CLIENTS)
PutSet == (NUM_REPLICAS+NUM_CLIENTS+1)..(NUM_REPLICAS + 2*NUM_CLIENTS)
DisconnectSet == (NUM_REPLICAS+1+2*NUM_CLIENTS)..(NUM_REPLICAS+3*NUM_CLIENTS)
NullSet == (NUM_REPLICAS+1+3*NUM_CLIENTS)..(NUM_REPLICAS+4*NUM_CLIENTS)

\* These constants allow PlusCal processes to derive their client identifiers from
\* their PlusCal identifiers.
GET_ORDER == 0
PUT_ORDER == 1
DISCONNECT_ORDER == 2
NULL_ORDER == 3

(***************************************************************************
--mpcal ReplicatedKV {
  define {
      \* Define NUM_NODES to be the total number of nodes in the system, i.e., the number of
      \* clients plus the number of replicas
      NUM_NODES == NUM_REPLICAS + NUM_CLIENTS

      \* Each replica and each client in the system need an identifier. By default, replicas
      \* are identified from 1 to NUM_REPLICAS, and the clients are identified from NUM_REPLICAS+1
      \* to NUM_NODES. It is important that identifiers are unique, consecutive and non-overlapping,
      \* due to the way we are modeling our network in this specification.
      ReplicaSet == 1..NUM_REPLICAS
      ClientSet == (NUM_REPLICAS+1)..NUM_NODES
  }

  \* Broadcasts a certain `msg` to `nodes` with identifiers ranging from
  \* `domainStart` to `domainEnd`.
  \*
  \* Only returns once every message has been sent (i.e., it may "block" if
  \* the buffer of one of the receivers is full).
  macro Broadcast(nodes, i, domainStart, domainEnd, msg) {
      while (i <= domainEnd) {
          nodes[i] := msg;
          i := i + 1;
      }
  }

  \* Models a FIFO channel. Messages are always delivered. Every process
  \* can have up to `BUFFER_SIZE` messages in its buffer before being
  \* processed.
  mapping macro FIFOChannel {
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

  \* Mapping via identity is sometimes necessary in order to inform
  \* the compiler that a certain resource is to be function mapped, but
  \* no meaningful manipulation on reads and writes is necessary.
  mapping macro Identity {
      read  { yield $variable; }
      write { yield $value; }
  }

  \* This archetype defines the behavior of the replica servers in the system.
  \* Its parameters are:
  \*
  \* - clients: connections to all clients in the system; it needs to wait
  \*            for client requests in order to perform operations.
  \* - replicas: connections to replicas. Since replicas do not talk to each
  \*             other, this parameter is only used in order to listen to
  \*             incoming messages.
  \* - kv: the underlying "database". When 'put' requests become stable, this
  \*       database is updated to include the value being set by the client.
  archetype AReplica(ref clients, replicas, ref kv)

  \* Local state in a replica:
  variables
            \* Each replica knows which clients are live (i.e., haven't disconnected)
            \* Initially, all clients are live.
            liveClients = ClientSet,

            \* Replicas remember which requests are pending (i.e., have not been
            \* replied yet). This variable maps client identifiers to a sequence
            \* of pending requests
            pendingRequests = [c \in liveClients |-> <<>>],

            \* Temporary variables: holds messages that are stable
            stableMessages = <<>>,

            \* incremented during in loops
            i,

            \* temporary variable: holds the first pending message from
            \* a client. The first pending message has the lowest logical
            \* clock in the sequence (logical clocks are monotonically increasing)
            firstPending,

            \* temporary variables used while finding the set of stable
            \* messages.
            timestamp,
            nextClient,
            lowestPending,
            chooseMessage,

            \* the replica needs to know the logical clocks of the last
            \* message received by each client in order to determine
            \* request stability.
            currentClocks = [c \in liveClients |-> 0];

            \* determines the lowest logical clock value seen from all
            \* clients. Any pending messages with timestamp lower than this
            \* can be considered stable.
            minClock,

            \* controls while loop execution. See the 'findStableRequestsLoop'
            \* step for more information
            continue,

            \* temporary variable: live clients that have pending
            \* messages (stable or not)
            pendingClients,

            \* Used when iterating over sets of clients
            clientsIter,

            \* used to hold messages sent/received by the replica
            msg,

            \* holds keys/values to be read from/written to the database
            key,
            val,

            \* whether to continue in the replica main loop
            mainLoop = TRUE; {

    \* Main replica loop. In each iteration of the loop, the replica:
    \*
    \*     1. Waits for incoming messages from clients;
    \*     2. Finds stable messages;
    \*     3. Replies to all stable messages.
    replicaLoop:
      while (mainLoop) {

          stableMessages := <<>>;
          continue := TRUE;

          \* Waits for an incoming message from any client. This statement will
          \* "block" the replica until a message is read into 'msg'.
          \* See definition of client archetypes for the format of the messages.
          receiveClientRequest:
            msg := replicas[self];

          \* if the message received is a disconnection from a client,
          \* remove the client from the set of live clients
          clientDisconnected:
            if (msg.op = DISCONNECT_MSG) {
                liveClients := liveClients \ {msg.client};
            };

          \* if the message is a Get request:
          replicaGetRequest:
            if (msg.op = GET_MSG) {
                \* safety assertion: a client requesting for a key must be live
                assert(msg.client \in liveClients);

                \* update our records of the current logical clock of the
                \* requesting client.
                currentClocks[msg.client] := msg.timestamp;

                \* make this a pending message (to be dealt with later, during
                \* stability check)
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

          \* if the message is a Put request: similar to Get request.
          replicaPutRequest:
            if (msg.op = PUT_MSG) {
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

          \* if the message is a clock update from a client, inspect the logical clock
          \* to check if it's lower than that of any other message seen before.
          replicaNullRequest:
            if (msg.op = NULL_MSG) {
                currentClocks[msg.client] := msg.timestamp;
            };

          \* Message stability
          \* -----------------
          \*
          \* The replica needs to detect when messages become stable, and then respond to
          \* those messages. Finding out which messages are stable and totally ordering them
          \* is crucial for the correctness of the algorithm. If message stability does not work
          \* correctly in the replicas, the database may get inconsistent across replicas
          \* (if operations are applied in a different order), or clients may get "stuck"
          \* (if stable messages are not replied).


          \* This is the main loop that finds which of the pending requests (if any) are stable
          findStableRequestsLoop:
            while (continue) {

                \* only consider clients that have messages pending
                pendingClients := {c \in liveClients : Len(pendingRequests[c]) > 0};

                \* if two messages have the same logical clock, total ordering is enforced
                \* based on the client identifier: requests from smaller client identifiers
                \* are applied first
                nextClient := NUM_NODES + 1;

                clientsIter := liveClients;
                i := 0;
                minClock := 0;

                \* in order to find the set of stable messages, we need to determine
                \* the lowest logical clock among our set of live clients. Then, every
                \* pending message with a timestamp greater than 'minClock' can be
                \* considered stable.
                findMinClock:
                  while (i < Cardinality(clientsIter)) {
                      with (client \in clientsIter) {
                          if (minClock = 0 \/ currentClocks[client] < minClock) {
                              minClock := currentClocks[client];
                          };

                          clientsIter := clientsIter \ {client};
                      }
                  };

                \* this variable holds the timestamp of the request with the lowest clock
                \* value that is pending and stable
                lowestPending := minClock + 1;

                i := 0;

                \* find the next stable message to be processed
                findMinClient:
                  while (i < Cardinality(pendingClients)) {
                      with (client \in pendingClients) {

                          \* for each client with pending requests:
                          \* - inspect the first pending message (by definition, the message with
                          \*   lowest clock from that client)
                          \* - extract the timestamp from the message
                          \* - record the client and timestamp in case this is the "oldest" message

                          firstPending := Head(pendingRequests[client]);
                          assert(firstPending.op = GET_MSG \/ firstPending.op = PUT_MSG);
                          timestamp := firstPending.timestamp;

                          \* a message is only stable if its timestamp is lower than
                          \* minClock
                          if (timestamp < minClock) {

                              \* this is the next stable message if it has the lowest
                              \* timestamp seen so far; if the timestamp is the same as
                              \* the lowest seen so far, do a client-id comparison
                              chooseMessage := (timestamp < lowestPending) \/ ((timestamp = lowestPending) /\ (client < nextClient));
                              if (chooseMessage) {
                                  nextClient := client;
                                  lowestPending := timestamp;
                              }
                          };

                          pendingClients := pendingClients \ {client};
                      }
                  };

                \* add the next stable message to the 'stableMessages' sequence.
                \* if 'lowestPending' is >= 'minClock', it means no more stable messages
                \* are pending, and we can leave this loop.
                addStableMessage:
                  if (lowestPending < minClock) {
                      msg := Head(pendingRequests[nextClient]);
                      pendingRequests[nextClient] := Tail(pendingRequests[nextClient]);

                      stableMessages := Append(stableMessages, msg);
                  } else {
                      continue := FALSE;
                  }
            };

          i := 1;

          \* iterate over our sequence of 'stableMessages' built in the previous
          \* step, responding to each of them in order.
          respondPendingRequestsLoop:
            while (i <= Len(stableMessages)) {
                msg := stableMessages[i];
                i := i + 1;

                respondStableGet:
                  if (msg.op = GET_MSG) {
                      key := msg.key;
                      val := kv[key];

                      \* send the value read from the database back to the client
                      clients[msg.client] := [type |-> GET_RESPONSE, result |-> val];
                  };

                respondStablePut:
                  if (msg.op = PUT_MSG) {
                      key := msg.key;
                      val := msg.value;

                      \* update our database and send an OK back to the client
                      kv[key] := val;

                      clients[msg.client] := [type |-> PUT_RESPONSE, result |-> PUT_OK];
                  };
            }
      }
  }


  \* Client Definitions
  \* ------------------
  \*
  \* The following archetypes define the client functions as specified in A1.
  \* Note that these operations are the "logical" versions of the API: for example,
  \* a Put archetype here sends a "Put" message to all replicas.
  \*
  \* In all of the definitions below, note that 'clocks' represent the client's
  \* logical clock. However, upon disconnection, the clock is set to '-1', and
  \* clients know to terminate when that happens.


  \* Specifies a Get request from a client. Arguments:
  \*
  \* - replicas: connections to replica servers
  \* - clients: connections to clients. Used only to listen for incoming messages
  \*            from replicas (i.e., to send the value of the key being read).
  \* - key: the key being read. This *must* belong to the KeySpace set.
  \* - locked: whether or not an RPC call is allowed. Clients do not send
  \*           concurrent requests. This stops a Get request from being sent
  \*           while a Put request is underway.
  \* clock: The initial logical clock
  \*
  \* A Get message sent to the replica is a tuple in the following format:
  \*
  \*     << GET_MSG, key, client_id, lamport_clock >>
  archetype Get(ref replicas, clients, key, locked, ref clock)
  variable continue = TRUE, i = 0, getReq, getResp, clientId;
  {
      \* Loop until disconnected
      getLoop:
        while (continue) {
            getRequest:
              clientId := self - (NUM_CLIENTS * GET_ORDER);

              \* only perform a get request if not locked (i.e., Put request underway)
              await ~locked[clientId];

              \* if disconnected, return
              if (clock = -1) {
                  continue := FALSE
              } else {

                  \* increment the logical clock, and construct a valid
                  \* Get message.
                  clock := clock + 1;
                  getReq := [op |-> GET_MSG, key |-> key, client |-> clientId, timestamp |-> clock];

                  \* Choose some replica from the set of replicas to send this
                  \* request to
                  with (dst \in ReplicaSet) {
                      replicas[dst] := getReq;
                  };

                  \* Waits for the response from the replica
                  getResp := clients[clientId];
              }
        }
  }

  \* Specifies a Put request from a client. Arguments:
  \*
  \* - replicas: connection to the replicas.
  \* - clients: connection to the clients. Used to read incoming messages (response
  \*            from the Put request
  \* - key: the key being set.
  \* - value: the value being written to the key
  \* - locked: set when the Put request is sent to the replica to indicate that
  \*           other calls should wait for its completion
  \* - clock: Lamport clocks
  \*
  \* A Put message sent to the replica is a tuple in the following format:
  \*
  \*     << PUT_MSG, key, value, client_id, lamport_clock >>
  archetype Put(ref replicas, clients, key, value, ref locked, ref clock)
  variables continue = TRUE, i, j, putReq, putResp, clientId;
  {
      \* Loops indefinitely until disconnected
      putLoop:
        while (continue) {
            clientId := self - (NUM_CLIENTS * PUT_ORDER);

            putRequest:
              \* if disconnected, return
              if (clock = -1) {
                  continue := FALSE;
              } else {

                  \* increment the logical clock, construct the payload to be sent
                  \* to the replica, and set 'locked' to TRUE
                  clock := clock + 1;
                  putReq := [op |-> PUT_MSG, key |-> key, value |-> value, client |-> clientId, timestamp |-> clock];
                  locked[clientId] := TRUE;
                  i := 0;
                  j := 1;

                  \* Put requests must be broadcast to all replicas
                  putBroadcast:
                    Broadcast(replicas, j, 1, NUM_REPLICAS, putReq);

                  \* wait for a response from all replicas, and allow other
                  \* calls to the replica to happen after that.
                  putResponse:
                    while (i < Cardinality(ReplicaSet)) {
                        putResp := clients[clientId];
                        assert(putResp.type = PUT_RESPONSE /\ putResp.result = PUT_OK);

                        i := i + 1;
                    };

                    locked[clientId] := FALSE;

                  putComplete:
                    skip;
              }
        }
  }

  \* Specifies a Disconnect message from the client.
  \* Does not disconnect if 'locked' (i.e., a Put request is underway).
  \*
  \* A Disconnect message sent to the replica is a tuple in the following format:
  \*
  \*     << DISCONNECT_MSG, client_id >>
  archetype Disconnect(ref replicas, locked, ref clock)
  variables msg, j, clientId;
  {
      sendDisconnectRequest:
        clientId := self - (NUM_CLIENTS * DISCONNECT_ORDER);
        await ~locked[clientId];

        msg := [op |-> DISCONNECT_MSG, client |-> clientId];

        \* setting the logical clock internally to -1 indicates that this client
        \* has disconnected. Other operations terminate when accordingly.
        clock := -1;
        j := 1;

        \* Disconnection messages need to be broadcast to all replicas.
        disconnectBroadcast:
          Broadcast(replicas, j, 1, NUM_REPLICAS, msg);
  }

  \* Specifies a ClockUpdate ('null') message from the client.
  \* If the client has disconnected, no more clock updates are sent.
  \*
  \* A ClockUpdate message sent to the replica is a tuple in the following format:
  \*
  \*     << NULL_MSG, client_id, logical_clock >>
  archetype ClockUpdate(ref replicas, ref clock)
  variables continue = TRUE, i = 0, j, msg, clientId;
  {
      clockUpdateLoop:
        while (continue) {
            clientId := self - (NUM_CLIENTS * NULL_ORDER);

            \* if we have disconnected, return
            if (clock = -1) {
                continue := FALSE;
            } else {
                \* tick the lock and construct the message accordingly
                clock := clock + 1;
                msg := [op |-> NULL_MSG, client |-> clientId, timestamp |-> clock];
                j := 1;

                \* clock update messages must be broadcast to all replicas.
                nullBroadcast:
                  Broadcast(replicas, j, 1, NUM_REPLICAS, msg);
            }
        }
  }

  \* Global Variables
  \* ----------------

  variables
            \* queue of incoming messages for each of the replicas
            replicasNetwork = [id \in ReplicaSet |-> <<>>],

            \* queue of incoming messages for each of the clients
            clientsNetwork = [id \in ClientSet |-> <<>>],

            \* all clients are not locked initially
            lock = [c \in ClientSet |-> FALSE];


  \* Process Instantiations
  \* ----------------------
  \*
  \* This is where the archetypes defined above are instantiated into actual PlusCal
  \* processes. We instantiate NUM_REPLICAS replica servers and NUM_CLIENTS client
  \* processes for each possible client operation. TLC will be responsible for
  \* exploring the different orderings in which these clients and replicas
  \* may interact.


  \* Instantiate replica servers. The network model used is the one defined in
  \* the FIFOChannel mapping macro.
  fair process (Replica \in ReplicaSet) == instance AReplica(ref clientsNetwork, replicasNetwork, [k \in KeySpace |-> NULL])
      mapping @1[_] via FIFOChannel
      mapping @2[_] via FIFOChannel
      mapping @3[_] via Identity;

  \* Instantiate clients:

  fair process (GetClient \in GetSet) == instance Get(ref replicasNetwork, clientsNetwork, GET_KEY, lock, 0)
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientsNetwork[_] via FIFOChannel
      mapping lock[_] via Identity;

  fair process (PutClient \in PutSet) == instance Put(ref replicasNetwork, clientsNetwork, PUT_KEY, PUT_VALUE, ref lock, 0)
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientsNetwork[_] via FIFOChannel
      mapping lock[_] via Identity;

  fair process (DisconnectClient \in DisconnectSet) == instance Disconnect(ref replicasNetwork, lock, 0)
      mapping replicasNetwork[_] via FIFOChannel
      mapping lock[_] via Identity;

  fair process (ClockUpdateClient \in NullSet) == instance ClockUpdate(ref replicasNetwork, 0)
      mapping replicasNetwork[_] via FIFOChannel;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ReplicatedKV {
    variables replicasNetwork = [id \in ReplicaSet |-> <<>>], clientsNetwork = [id \in ClientSet |-> <<>>], lock = [c \in ClientSet |-> FALSE];
    define {
        NUM_NODES == (NUM_REPLICAS)+(NUM_CLIENTS)ReplicaSet == (1)..(NUM_REPLICAS)ClientSet == ((NUM_REPLICAS)+(1))..(NUM_NODES)}
    fair process (Replica \in ReplicaSet)
    variables kvLocal = [k \in KeySpace |-> NULL], liveClients = ClientSet, pendingRequests = [c \in liveClients |-> <<>>], stableMessages = <<>>, i, firstPending, timestamp, nextClient, lowestPending, chooseMessage, currentClocks = [c \in liveClients |-> 0], minClock, continue, pendingClients, clientsIter, msg, key, val, mainLoop = TRUE, replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1;
    {
        replicaLoop:
            if (mainLoop) {
                stableMessages := <<>>;
                continue := TRUE;
                receiveClientRequest:
                    await (Len(replicasNetwork[self]))>(0);
                    with (msg0 = Head(replicasNetwork[self])) {
                        replicasWrite := [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])];
                        replicasRead := msg0;
                    };
                    msg := replicasRead;
                    replicasNetwork := replicasWrite;

                clientDisconnected:
                    if (((msg).op)=(DISCONNECT_MSG)) {
                        liveClients := (liveClients)\({(msg).client});
                    };

                replicaGetRequest:
                    if (((msg).op)=(GET_MSG)) {
                        assert ((msg).client)\in(liveClients);
                        currentClocks[(msg).client] := (msg).timestamp;
                        pendingRequests[(msg).client] := Append(pendingRequests[(msg).client], msg);
                    };

                replicaPutRequest:
                    if (((msg).op)=(PUT_MSG)) {
                        currentClocks[(msg).client] := (msg).timestamp;
                        pendingRequests[(msg).client] := Append(pendingRequests[(msg).client], msg);
                    };

                replicaNullRequest:
                    if (((msg).op)=(NULL_MSG)) {
                        currentClocks[(msg).client] := (msg).timestamp;
                    };

                findStableRequestsLoop:
                    if (continue) {
                        pendingClients := {c \in liveClients : (Len(pendingRequests[c]))>(0)};
                        nextClient := (NUM_NODES)+(1);
                        clientsIter := liveClients;
                        i := 0;
                        minClock := 0;
                        findMinClock:
                            if ((i)<(Cardinality(clientsIter))) {
                                with (client \in clientsIter) {
                                    if (((minClock)=(0))\/((currentClocks[client])<(minClock))) {
                                        minClock := currentClocks[client];
                                    };
                                    clientsIter := (clientsIter)\({client});
                                };
                                goto findMinClock;
                            } else {
                                lowestPending := (minClock)+(1);
                                i := 0;
                            };

                        findMinClient:
                            if ((i)<(Cardinality(pendingClients))) {
                                with (client \in pendingClients) {
                                    firstPending := Head(pendingRequests[client]);
                                    assert (((firstPending).op)=(GET_MSG))\/(((firstPending).op)=(PUT_MSG));
                                    timestamp := (firstPending).timestamp;
                                    if ((timestamp)<(minClock)) {
                                        chooseMessage := ((timestamp)<(lowestPending))\/(((timestamp)=(lowestPending))/\((client)<(nextClient)));
                                        if (chooseMessage) {
                                            nextClient := client;
                                            lowestPending := timestamp;
                                        };
                                    };
                                    pendingClients := (pendingClients)\({client});
                                };
                                goto findMinClient;
                            };

                        addStableMessage:
                            if ((lowestPending)<(minClock)) {
                                msg := Head(pendingRequests[nextClient]);
                                pendingRequests[nextClient] := Tail(pendingRequests[nextClient]);
                                stableMessages := Append(stableMessages, msg);
                                goto findStableRequestsLoop;
                            } else {
                                continue := FALSE;
                                goto findStableRequestsLoop;
                            };

                    } else {
                        i := 1;
                    };

                respondPendingRequestsLoop:
                    if ((i)<=(Len(stableMessages))) {
                        msg := stableMessages[i];
                        i := (i)+(1);
                        respondStableGet:
                            if (((msg).op)=(GET_MSG)) {
                                key := (msg).key;
                                kvRead := kvLocal[key];
                                val := kvRead;
                                await (Len(clientsNetwork[(msg).client]))<(BUFFER_SIZE);
                                clientsWrite := [clientsNetwork EXCEPT ![(msg).client] = Append(clientsNetwork[(msg).client], [type |-> GET_RESPONSE, result |-> val])];
                                clientsWrite0 := clientsWrite;
                                clientsNetwork := clientsWrite0;
                            } else {
                                clientsWrite0 := clientsNetwork;
                                clientsNetwork := clientsWrite0;
                            };

                        respondStablePut:
                            if (((msg).op)=(PUT_MSG)) {
                                key := (msg).key;
                                val := (msg).value;
                                kvWrite := [kvLocal EXCEPT ![key] = val];
                                await (Len(clientsNetwork[(msg).client]))<(BUFFER_SIZE);
                                clientsWrite := [clientsNetwork EXCEPT ![(msg).client] = Append(clientsNetwork[(msg).client], [type |-> PUT_RESPONSE, result |-> PUT_OK])];
                                kvWrite0 := kvWrite;
                                clientsWrite1 := clientsWrite;
                                clientsNetwork := clientsWrite1;
                                kvLocal := kvWrite0;
                                goto respondPendingRequestsLoop;
                            } else {
                                kvWrite0 := kvLocal;
                                clientsWrite1 := clientsNetwork;
                                clientsNetwork := clientsWrite1;
                                kvLocal := kvWrite0;
                                goto respondPendingRequestsLoop;
                            };

                    } else {
                        goto replicaLoop;
                    };

            };

    }
    fair process (GetClient \in GetSet)
    variables clockLocal = 0, continue = TRUE, i = 0, getReq, getResp, clientId, lockedRead, clockRead, clockRead0, clockWrite, keyRead, clockRead1, replicasWrite0, clientsRead, clientsWrite2, clockWrite0, replicasWrite1, clientsWrite3;
    {
        getLoop:
            if (continue) {
                getRequest:
                    clientId := (self)-((NUM_CLIENTS)*(GET_ORDER));
                    lockedRead := lock[clientId];
                    await ~(lockedRead);
                    clockRead := clockLocal;
                    if ((clockRead)=(-(1))) {
                        continue := FALSE;
                        clockWrite0 := clockLocal;
                        replicasWrite1 := replicasNetwork;
                        clientsWrite3 := clientsNetwork;
                        replicasNetwork := replicasWrite1;
                        clientsNetwork := clientsWrite3;
                        clockLocal := clockWrite0;
                        goto getLoop;
                    } else {
                        clockRead0 := clockLocal;
                        clockWrite := (clockRead0)+(1);
                        keyRead := GET_KEY;
                        clockRead1 := clockWrite;
                        getReq := [op |-> GET_MSG, key |-> keyRead, client |-> clientId, timestamp |-> clockRead1];
                        with (dst \in ReplicaSet) {
                            await (Len(replicasNetwork[dst]))<(BUFFER_SIZE);
                            replicasWrite0 := [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq)];
                        };
                        await (Len(clientsNetwork[clientId]))>(0);
                        with (msg1 = Head(clientsNetwork[clientId])) {
                            clientsWrite2 := [clientsNetwork EXCEPT ![clientId] = Tail(clientsNetwork[clientId])];
                            clientsRead := msg1;
                        };
                        getResp := clientsRead;
                        clockWrite0 := clockWrite;
                        replicasWrite1 := replicasWrite0;
                        clientsWrite3 := clientsWrite2;
                        replicasNetwork := replicasWrite1;
                        clientsNetwork := clientsWrite3;
                        clockLocal := clockWrite0;
                        goto getLoop;
                    };

            };

    }
    fair process (PutClient \in PutSet)
    variables clockLocal0 = 0, continue = TRUE, i, j, putReq, putResp, clientId, clockRead2, clockRead3, clockWrite1, keyRead0, valueRead, clockRead4, lockedWrite, replicasWrite2, replicasWrite3, clientsRead0, clientsWrite4, clientsWrite5, lockedWrite0;
    {
        putLoop:
            if (continue) {
                clientId := (self)-((NUM_CLIENTS)*(PUT_ORDER));
                putRequest:
                    clockRead2 := clockLocal0;
                    if ((clockRead2)=(-(1))) {
                        continue := FALSE;
                        goto putLoop;
                    } else {
                        clockRead3 := clockLocal0;
                        clockWrite1 := (clockRead3)+(1);
                        keyRead0 := PUT_KEY;
                        valueRead := PUT_VALUE;
                        clockRead4 := clockWrite1;
                        putReq := [op |-> PUT_MSG, key |-> keyRead0, value |-> valueRead, client |-> clientId, timestamp |-> clockRead4];
                        lockedWrite := [lock EXCEPT ![clientId] = TRUE];
                        i := 0;
                        j := 1;
                        lock := lockedWrite;
                        clockLocal0 := clockWrite1;
                        putBroadcast:
                            if ((j)<=(NUM_REPLICAS)) {
                                await (Len(replicasNetwork[j]))<(BUFFER_SIZE);
                                replicasWrite2 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], putReq)];
                                j := (j)+(1);
                                replicasWrite3 := replicasWrite2;
                                replicasNetwork := replicasWrite3;
                                goto putBroadcast;
                            } else {
                                replicasWrite3 := replicasNetwork;
                                replicasNetwork := replicasWrite3;
                            };

                        putResponse:
                            if ((i)<(Cardinality(ReplicaSet))) {
                                await (Len(clientsNetwork[clientId]))>(0);
                                with (msg2 = Head(clientsNetwork[clientId])) {
                                    clientsWrite4 := [clientsNetwork EXCEPT ![clientId] = Tail(clientsNetwork[clientId])];
                                    clientsRead0 := msg2;
                                };
                                putResp := clientsRead0;
                                assert (((putResp).type)=(PUT_RESPONSE))/\(((putResp).result)=(PUT_OK));
                                i := (i)+(1);
                                clientsWrite5 := clientsWrite4;
                                lockedWrite0 := lock;
                                clientsNetwork := clientsWrite5;
                                lock := lockedWrite0;
                                goto putResponse;
                            } else {
                                lockedWrite := [lock EXCEPT ![clientId] = FALSE];
                                clientsWrite5 := clientsNetwork;
                                lockedWrite0 := lockedWrite;
                                clientsNetwork := clientsWrite5;
                                lock := lockedWrite0;
                            };

                        putComplete:
                            goto putLoop;

                    };

            };

    }
    fair process (DisconnectClient \in DisconnectSet)
    variables clockLocal1 = 0, msg, j, clientId, lockedRead0, clockWrite2, replicasWrite4, replicasWrite5;
    {
        sendDisconnectRequest:
            clientId := (self)-((NUM_CLIENTS)*(DISCONNECT_ORDER));
            lockedRead0 := lock[clientId];
            await ~(lockedRead0);
            msg := [op |-> DISCONNECT_MSG, client |-> clientId];
            clockWrite2 := -(1);
            j := 1;
            clockLocal1 := clockWrite2;
        disconnectBroadcast:
            if ((j)<=(NUM_REPLICAS)) {
                await (Len(replicasNetwork[j]))<(BUFFER_SIZE);
                replicasWrite4 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                j := (j)+(1);
                replicasWrite5 := replicasWrite4;
                replicasNetwork := replicasWrite5;
                goto disconnectBroadcast;
            } else {
                replicasWrite5 := replicasNetwork;
                replicasNetwork := replicasWrite5;
            };

    }
    fair process (ClockUpdateClient \in NullSet)
    variables clockLocal2 = 0, continue = TRUE, i = 0, j, msg, clientId, clockRead5, clockRead6, clockWrite3, clockRead7, replicasWrite6, replicasWrite7;
    {
        clockUpdateLoop:
            if (continue) {
                clientId := (self)-((NUM_CLIENTS)*(NULL_ORDER));
                clockRead5 := clockLocal2;
                if ((clockRead5)=(-(1))) {
                    continue := FALSE;
                    goto clockUpdateLoop;
                } else {
                    clockRead6 := clockLocal2;
                    clockWrite3 := (clockRead6)+(1);
                    clockRead7 := clockWrite3;
                    msg := [op |-> NULL_MSG, client |-> clientId, timestamp |-> clockRead7];
                    j := 1;
                    clockLocal2 := clockWrite3;
                    nullBroadcast:
                        if ((j)<=(NUM_REPLICAS)) {
                            await (Len(replicasNetwork[j]))<(BUFFER_SIZE);
                            replicasWrite6 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                            j := (j)+(1);
                            replicasWrite7 := replicasWrite6;
                            replicasNetwork := replicasWrite7;
                            goto nullBroadcast;
                        } else {
                            replicasWrite7 := replicasNetwork;
                            replicasNetwork := replicasWrite7;
                            goto clockUpdateLoop;
                        };

                };
            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable i of process Replica at line 610 col 148 changed to i_
\* Process variable continue of process Replica at line 610 col 271 changed to continue_
\* Process variable msg of process Replica at line 610 col 310 changed to msg_
\* Process variable continue of process GetClient at line 748 col 31 changed to continue_G
\* Process variable i of process GetClient at line 748 col 48 changed to i_G
\* Process variable clientId of process GetClient at line 748 col 72 changed to clientId_
\* Process variable continue of process PutClient at line 795 col 32 changed to continue_P
\* Process variable i of process PutClient at line 795 col 49 changed to i_P
\* Process variable j of process PutClient at line 795 col 52 changed to j_
\* Process variable clientId of process PutClient at line 795 col 72 changed to clientId_P
\* Process variable msg of process DisconnectClient at line 862 col 32 changed to msg_D
\* Process variable j of process DisconnectClient at line 862 col 37 changed to j_D
\* Process variable clientId of process DisconnectClient at line 862 col 40 changed to clientId_D
CONSTANT defaultInitValue
VARIABLES replicasNetwork, clientsNetwork, lock, pc

(* define statement *)
NUM_NODES == (NUM_REPLICAS)+(NUM_CLIENTS)ReplicaSet == (1)..(NUM_REPLICAS)ClientSet == ((NUM_REPLICAS)+(1))..(NUM_NODES)

VARIABLES kvLocal, liveClients, pendingRequests, stableMessages, i_,
          firstPending, timestamp, nextClient, lowestPending, chooseMessage,
          currentClocks, minClock, continue_, pendingClients, clientsIter,
          msg_, key, val, mainLoop, replicasRead, replicasWrite, kvRead,
          clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1,
          clockLocal, continue_G, i_G, getReq, getResp, clientId_, lockedRead,
          clockRead, clockRead0, clockWrite, keyRead, clockRead1,
          replicasWrite0, clientsRead, clientsWrite2, clockWrite0,
          replicasWrite1, clientsWrite3, clockLocal0, continue_P, i_P, j_,
          putReq, putResp, clientId_P, clockRead2, clockRead3, clockWrite1,
          keyRead0, valueRead, clockRead4, lockedWrite, replicasWrite2,
          replicasWrite3, clientsRead0, clientsWrite4, clientsWrite5,
          lockedWrite0, clockLocal1, msg_D, j_D, clientId_D, lockedRead0,
          clockWrite2, replicasWrite4, replicasWrite5, clockLocal2, continue,
          i, j, msg, clientId, clockRead5, clockRead6, clockWrite3,
          clockRead7, replicasWrite6, replicasWrite7

vars == << replicasNetwork, clientsNetwork, lock, pc, kvLocal, liveClients,
           pendingRequests, stableMessages, i_, firstPending, timestamp,
           nextClient, lowestPending, chooseMessage, currentClocks, minClock,
           continue_, pendingClients, clientsIter, msg_, key, val, mainLoop,
           replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0,
           kvWrite, kvWrite0, clientsWrite1, clockLocal, continue_G, i_G,
           getReq, getResp, clientId_, lockedRead, clockRead, clockRead0,
           clockWrite, keyRead, clockRead1, replicasWrite0, clientsRead,
           clientsWrite2, clockWrite0, replicasWrite1, clientsWrite3,
           clockLocal0, continue_P, i_P, j_, putReq, putResp, clientId_P,
           clockRead2, clockRead3, clockWrite1, keyRead0, valueRead,
           clockRead4, lockedWrite, replicasWrite2, replicasWrite3,
           clientsRead0, clientsWrite4, clientsWrite5, lockedWrite0,
           clockLocal1, msg_D, j_D, clientId_D, lockedRead0, clockWrite2,
           replicasWrite4, replicasWrite5, clockLocal2, continue, i, j, msg,
           clientId, clockRead5, clockRead6, clockWrite3, clockRead7,
           replicasWrite6, replicasWrite7 >>

ProcSet == (ReplicaSet) \cup (GetSet) \cup (PutSet) \cup (DisconnectSet) \cup (NullSet)

Init == (* Global variables *)
        /\ replicasNetwork = [id \in ReplicaSet |-> <<>>]
        /\ clientsNetwork = [id \in ClientSet |-> <<>>]
        /\ lock = [c \in ClientSet |-> FALSE]
        (* Process Replica *)
        /\ kvLocal = [self \in ReplicaSet |-> [k \in KeySpace |-> NULL]]
        /\ liveClients = [self \in ReplicaSet |-> ClientSet]
        /\ pendingRequests = [self \in ReplicaSet |-> [c \in liveClients[self] |-> <<>>]]
        /\ stableMessages = [self \in ReplicaSet |-> <<>>]
        /\ i_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ firstPending = [self \in ReplicaSet |-> defaultInitValue]
        /\ timestamp = [self \in ReplicaSet |-> defaultInitValue]
        /\ nextClient = [self \in ReplicaSet |-> defaultInitValue]
        /\ lowestPending = [self \in ReplicaSet |-> defaultInitValue]
        /\ chooseMessage = [self \in ReplicaSet |-> defaultInitValue]
        /\ currentClocks = [self \in ReplicaSet |-> [c \in liveClients[self] |-> 0]]
        /\ minClock = [self \in ReplicaSet |-> defaultInitValue]
        /\ continue_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ pendingClients = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsIter = [self \in ReplicaSet |-> defaultInitValue]
        /\ msg_ = [self \in ReplicaSet |-> defaultInitValue]
        /\ key = [self \in ReplicaSet |-> defaultInitValue]
        /\ val = [self \in ReplicaSet |-> defaultInitValue]
        /\ mainLoop = [self \in ReplicaSet |-> TRUE]
        /\ replicasRead = [self \in ReplicaSet |-> defaultInitValue]
        /\ replicasWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvRead = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite0 = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvWrite0 = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite1 = [self \in ReplicaSet |-> defaultInitValue]
        (* Process GetClient *)
        /\ clockLocal = [self \in GetSet |-> 0]
        /\ continue_G = [self \in GetSet |-> TRUE]
        /\ i_G = [self \in GetSet |-> 0]
        /\ getReq = [self \in GetSet |-> defaultInitValue]
        /\ getResp = [self \in GetSet |-> defaultInitValue]
        /\ clientId_ = [self \in GetSet |-> defaultInitValue]
        /\ lockedRead = [self \in GetSet |-> defaultInitValue]
        /\ clockRead = [self \in GetSet |-> defaultInitValue]
        /\ clockRead0 = [self \in GetSet |-> defaultInitValue]
        /\ clockWrite = [self \in GetSet |-> defaultInitValue]
        /\ keyRead = [self \in GetSet |-> defaultInitValue]
        /\ clockRead1 = [self \in GetSet |-> defaultInitValue]
        /\ replicasWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ clientsRead = [self \in GetSet |-> defaultInitValue]
        /\ clientsWrite2 = [self \in GetSet |-> defaultInitValue]
        /\ clockWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ replicasWrite1 = [self \in GetSet |-> defaultInitValue]
        /\ clientsWrite3 = [self \in GetSet |-> defaultInitValue]
        (* Process PutClient *)
        /\ clockLocal0 = [self \in PutSet |-> 0]
        /\ continue_P = [self \in PutSet |-> TRUE]
        /\ i_P = [self \in PutSet |-> defaultInitValue]
        /\ j_ = [self \in PutSet |-> defaultInitValue]
        /\ putReq = [self \in PutSet |-> defaultInitValue]
        /\ putResp = [self \in PutSet |-> defaultInitValue]
        /\ clientId_P = [self \in PutSet |-> defaultInitValue]
        /\ clockRead2 = [self \in PutSet |-> defaultInitValue]
        /\ clockRead3 = [self \in PutSet |-> defaultInitValue]
        /\ clockWrite1 = [self \in PutSet |-> defaultInitValue]
        /\ keyRead0 = [self \in PutSet |-> defaultInitValue]
        /\ valueRead = [self \in PutSet |-> defaultInitValue]
        /\ clockRead4 = [self \in PutSet |-> defaultInitValue]
        /\ lockedWrite = [self \in PutSet |-> defaultInitValue]
        /\ replicasWrite2 = [self \in PutSet |-> defaultInitValue]
        /\ replicasWrite3 = [self \in PutSet |-> defaultInitValue]
        /\ clientsRead0 = [self \in PutSet |-> defaultInitValue]
        /\ clientsWrite4 = [self \in PutSet |-> defaultInitValue]
        /\ clientsWrite5 = [self \in PutSet |-> defaultInitValue]
        /\ lockedWrite0 = [self \in PutSet |-> defaultInitValue]
        (* Process DisconnectClient *)
        /\ clockLocal1 = [self \in DisconnectSet |-> 0]
        /\ msg_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ j_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ clientId_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ lockedRead0 = [self \in DisconnectSet |-> defaultInitValue]
        /\ clockWrite2 = [self \in DisconnectSet |-> defaultInitValue]
        /\ replicasWrite4 = [self \in DisconnectSet |-> defaultInitValue]
        /\ replicasWrite5 = [self \in DisconnectSet |-> defaultInitValue]
        (* Process ClockUpdateClient *)
        /\ clockLocal2 = [self \in NullSet |-> 0]
        /\ continue = [self \in NullSet |-> TRUE]
        /\ i = [self \in NullSet |-> 0]
        /\ j = [self \in NullSet |-> defaultInitValue]
        /\ msg = [self \in NullSet |-> defaultInitValue]
        /\ clientId = [self \in NullSet |-> defaultInitValue]
        /\ clockRead5 = [self \in NullSet |-> defaultInitValue]
        /\ clockRead6 = [self \in NullSet |-> defaultInitValue]
        /\ clockWrite3 = [self \in NullSet |-> defaultInitValue]
        /\ clockRead7 = [self \in NullSet |-> defaultInitValue]
        /\ replicasWrite6 = [self \in NullSet |-> defaultInitValue]
        /\ replicasWrite7 = [self \in NullSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in ReplicaSet -> "replicaLoop"
                                        [] self \in GetSet -> "getLoop"
                                        [] self \in PutSet -> "putLoop"
                                        [] self \in DisconnectSet -> "sendDisconnectRequest"
                                        [] self \in NullSet -> "clockUpdateLoop"]

replicaLoop(self) == /\ pc[self] = "replicaLoop"
                     /\ IF mainLoop[self]
                           THEN /\ stableMessages' = [stableMessages EXCEPT ![self] = <<>>]
                                /\ continue_' = [continue_ EXCEPT ![self] = TRUE]
                                /\ pc' = [pc EXCEPT ![self] = "receiveClientRequest"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << stableMessages, continue_ >>
                     /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                     kvLocal, liveClients, pendingRequests, i_,
                                     firstPending, timestamp, nextClient,
                                     lowestPending, chooseMessage,
                                     currentClocks, minClock, pendingClients,
                                     clientsIter, msg_, key, val, mainLoop,
                                     replicasRead, replicasWrite, kvRead,
                                     clientsWrite, clientsWrite0, kvWrite,
                                     kvWrite0, clientsWrite1, clockLocal,
                                     continue_G, i_G, getReq, getResp,
                                     clientId_, lockedRead, clockRead,
                                     clockRead0, clockWrite, keyRead,
                                     clockRead1, replicasWrite0, clientsRead,
                                     clientsWrite2, clockWrite0,
                                     replicasWrite1, clientsWrite3,
                                     clockLocal0, continue_P, i_P, j_, putReq,
                                     putResp, clientId_P, clockRead2,
                                     clockRead3, clockWrite1, keyRead0,
                                     valueRead, clockRead4, lockedWrite,
                                     replicasWrite2, replicasWrite3,
                                     clientsRead0, clientsWrite4,
                                     clientsWrite5, lockedWrite0, clockLocal1,
                                     msg_D, j_D, clientId_D, lockedRead0,
                                     clockWrite2, replicasWrite4,
                                     replicasWrite5, clockLocal2, continue, i,
                                     j, msg, clientId, clockRead5, clockRead6,
                                     clockWrite3, clockRead7, replicasWrite6,
                                     replicasWrite7 >>

receiveClientRequest(self) == /\ pc[self] = "receiveClientRequest"
                              /\ (Len(replicasNetwork[self]))>(0)
                              /\ LET msg0 == Head(replicasNetwork[self]) IN
                                   /\ replicasWrite' = [replicasWrite EXCEPT ![self] = [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])]]
                                   /\ replicasRead' = [replicasRead EXCEPT ![self] = msg0]
                              /\ msg_' = [msg_ EXCEPT ![self] = replicasRead'[self]]
                              /\ replicasNetwork' = replicasWrite'[self]
                              /\ pc' = [pc EXCEPT ![self] = "clientDisconnected"]
                              /\ UNCHANGED << clientsNetwork, lock, kvLocal,
                                              liveClients, pendingRequests,
                                              stableMessages, i_, firstPending,
                                              timestamp, nextClient,
                                              lowestPending, chooseMessage,
                                              currentClocks, minClock,
                                              continue_, pendingClients,
                                              clientsIter, key, val, mainLoop,
                                              kvRead, clientsWrite,
                                              clientsWrite0, kvWrite, kvWrite0,
                                              clientsWrite1, clockLocal,
                                              continue_G, i_G, getReq, getResp,
                                              clientId_, lockedRead, clockRead,
                                              clockRead0, clockWrite, keyRead,
                                              clockRead1, replicasWrite0,
                                              clientsRead, clientsWrite2,
                                              clockWrite0, replicasWrite1,
                                              clientsWrite3, clockLocal0,
                                              continue_P, i_P, j_, putReq,
                                              putResp, clientId_P, clockRead2,
                                              clockRead3, clockWrite1,
                                              keyRead0, valueRead, clockRead4,
                                              lockedWrite, replicasWrite2,
                                              replicasWrite3, clientsRead0,
                                              clientsWrite4, clientsWrite5,
                                              lockedWrite0, clockLocal1, msg_D,
                                              j_D, clientId_D, lockedRead0,
                                              clockWrite2, replicasWrite4,
                                              replicasWrite5, clockLocal2,
                                              continue, i, j, msg, clientId,
                                              clockRead5, clockRead6,
                                              clockWrite3, clockRead7,
                                              replicasWrite6, replicasWrite7 >>

clientDisconnected(self) == /\ pc[self] = "clientDisconnected"
                            /\ IF ((msg_[self]).op)=(DISCONNECT_MSG)
                                  THEN /\ liveClients' = [liveClients EXCEPT ![self] = (liveClients[self])\({(msg_[self]).client})]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED liveClients
                            /\ pc' = [pc EXCEPT ![self] = "replicaGetRequest"]
                            /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                            lock, kvLocal, pendingRequests,
                                            stableMessages, i_, firstPending,
                                            timestamp, nextClient,
                                            lowestPending, chooseMessage,
                                            currentClocks, minClock, continue_,
                                            pendingClients, clientsIter, msg_,
                                            key, val, mainLoop, replicasRead,
                                            replicasWrite, kvRead,
                                            clientsWrite, clientsWrite0,
                                            kvWrite, kvWrite0, clientsWrite1,
                                            clockLocal, continue_G, i_G,
                                            getReq, getResp, clientId_,
                                            lockedRead, clockRead, clockRead0,
                                            clockWrite, keyRead, clockRead1,
                                            replicasWrite0, clientsRead,
                                            clientsWrite2, clockWrite0,
                                            replicasWrite1, clientsWrite3,
                                            clockLocal0, continue_P, i_P, j_,
                                            putReq, putResp, clientId_P,
                                            clockRead2, clockRead3,
                                            clockWrite1, keyRead0, valueRead,
                                            clockRead4, lockedWrite,
                                            replicasWrite2, replicasWrite3,
                                            clientsRead0, clientsWrite4,
                                            clientsWrite5, lockedWrite0,
                                            clockLocal1, msg_D, j_D,
                                            clientId_D, lockedRead0,
                                            clockWrite2, replicasWrite4,
                                            replicasWrite5, clockLocal2,
                                            continue, i, j, msg, clientId,
                                            clockRead5, clockRead6,
                                            clockWrite3, clockRead7,
                                            replicasWrite6, replicasWrite7 >>

replicaGetRequest(self) == /\ pc[self] = "replicaGetRequest"
                           /\ IF ((msg_[self]).op)=(GET_MSG)
                                 THEN /\ Assert(((msg_[self]).client)\in(liveClients[self]),
                                                "Failure of assertion at line 632, column 25.")
                                      /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][(msg_[self]).client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests,
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaPutRequest"]
                           /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                           lock, kvLocal, liveClients,
                                           stableMessages, i_, firstPending,
                                           timestamp, nextClient,
                                           lowestPending, chooseMessage,
                                           minClock, continue_, pendingClients,
                                           clientsIter, msg_, key, val,
                                           mainLoop, replicasRead,
                                           replicasWrite, kvRead, clientsWrite,
                                           clientsWrite0, kvWrite, kvWrite0,
                                           clientsWrite1, clockLocal,
                                           continue_G, i_G, getReq, getResp,
                                           clientId_, lockedRead, clockRead,
                                           clockRead0, clockWrite, keyRead,
                                           clockRead1, replicasWrite0,
                                           clientsRead, clientsWrite2,
                                           clockWrite0, replicasWrite1,
                                           clientsWrite3, clockLocal0,
                                           continue_P, i_P, j_, putReq,
                                           putResp, clientId_P, clockRead2,
                                           clockRead3, clockWrite1, keyRead0,
                                           valueRead, clockRead4, lockedWrite,
                                           replicasWrite2, replicasWrite3,
                                           clientsRead0, clientsWrite4,
                                           clientsWrite5, lockedWrite0,
                                           clockLocal1, msg_D, j_D, clientId_D,
                                           lockedRead0, clockWrite2,
                                           replicasWrite4, replicasWrite5,
                                           clockLocal2, continue, i, j, msg,
                                           clientId, clockRead5, clockRead6,
                                           clockWrite3, clockRead7,
                                           replicasWrite6, replicasWrite7 >>

replicaPutRequest(self) == /\ pc[self] = "replicaPutRequest"
                           /\ IF ((msg_[self]).op)=(PUT_MSG)
                                 THEN /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][(msg_[self]).client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests,
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaNullRequest"]
                           /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                           lock, kvLocal, liveClients,
                                           stableMessages, i_, firstPending,
                                           timestamp, nextClient,
                                           lowestPending, chooseMessage,
                                           minClock, continue_, pendingClients,
                                           clientsIter, msg_, key, val,
                                           mainLoop, replicasRead,
                                           replicasWrite, kvRead, clientsWrite,
                                           clientsWrite0, kvWrite, kvWrite0,
                                           clientsWrite1, clockLocal,
                                           continue_G, i_G, getReq, getResp,
                                           clientId_, lockedRead, clockRead,
                                           clockRead0, clockWrite, keyRead,
                                           clockRead1, replicasWrite0,
                                           clientsRead, clientsWrite2,
                                           clockWrite0, replicasWrite1,
                                           clientsWrite3, clockLocal0,
                                           continue_P, i_P, j_, putReq,
                                           putResp, clientId_P, clockRead2,
                                           clockRead3, clockWrite1, keyRead0,
                                           valueRead, clockRead4, lockedWrite,
                                           replicasWrite2, replicasWrite3,
                                           clientsRead0, clientsWrite4,
                                           clientsWrite5, lockedWrite0,
                                           clockLocal1, msg_D, j_D, clientId_D,
                                           lockedRead0, clockWrite2,
                                           replicasWrite4, replicasWrite5,
                                           clockLocal2, continue, i, j, msg,
                                           clientId, clockRead5, clockRead6,
                                           clockWrite3, clockRead7,
                                           replicasWrite6, replicasWrite7 >>

replicaNullRequest(self) == /\ pc[self] = "replicaNullRequest"
                            /\ IF ((msg_[self]).op)=(NULL_MSG)
                                  THEN /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED currentClocks
                            /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                            /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                            lock, kvLocal, liveClients,
                                            pendingRequests, stableMessages,
                                            i_, firstPending, timestamp,
                                            nextClient, lowestPending,
                                            chooseMessage, minClock, continue_,
                                            pendingClients, clientsIter, msg_,
                                            key, val, mainLoop, replicasRead,
                                            replicasWrite, kvRead,
                                            clientsWrite, clientsWrite0,
                                            kvWrite, kvWrite0, clientsWrite1,
                                            clockLocal, continue_G, i_G,
                                            getReq, getResp, clientId_,
                                            lockedRead, clockRead, clockRead0,
                                            clockWrite, keyRead, clockRead1,
                                            replicasWrite0, clientsRead,
                                            clientsWrite2, clockWrite0,
                                            replicasWrite1, clientsWrite3,
                                            clockLocal0, continue_P, i_P, j_,
                                            putReq, putResp, clientId_P,
                                            clockRead2, clockRead3,
                                            clockWrite1, keyRead0, valueRead,
                                            clockRead4, lockedWrite,
                                            replicasWrite2, replicasWrite3,
                                            clientsRead0, clientsWrite4,
                                            clientsWrite5, lockedWrite0,
                                            clockLocal1, msg_D, j_D,
                                            clientId_D, lockedRead0,
                                            clockWrite2, replicasWrite4,
                                            replicasWrite5, clockLocal2,
                                            continue, i, j, msg, clientId,
                                            clockRead5, clockRead6,
                                            clockWrite3, clockRead7,
                                            replicasWrite6, replicasWrite7 >>

findStableRequestsLoop(self) == /\ pc[self] = "findStableRequestsLoop"
                                /\ IF continue_[self]
                                      THEN /\ pendingClients' = [pendingClients EXCEPT ![self] = {c \in liveClients[self] : (Len(pendingRequests[self][c]))>(0)}]
                                           /\ nextClient' = [nextClient EXCEPT ![self] = (NUM_NODES)+(1)]
                                           /\ clientsIter' = [clientsIter EXCEPT ![self] = liveClients[self]]
                                           /\ i_' = [i_ EXCEPT ![self] = 0]
                                           /\ minClock' = [minClock EXCEPT ![self] = 0]
                                           /\ pc' = [pc EXCEPT ![self] = "findMinClock"]
                                      ELSE /\ i_' = [i_ EXCEPT ![self] = 1]
                                           /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                           /\ UNCHANGED << nextClient,
                                                           minClock,
                                                           pendingClients,
                                                           clientsIter >>
                                /\ UNCHANGED << replicasNetwork,
                                                clientsNetwork, lock, kvLocal,
                                                liveClients, pendingRequests,
                                                stableMessages, firstPending,
                                                timestamp, lowestPending,
                                                chooseMessage, currentClocks,
                                                continue_, msg_, key, val,
                                                mainLoop, replicasRead,
                                                replicasWrite, kvRead,
                                                clientsWrite, clientsWrite0,
                                                kvWrite, kvWrite0,
                                                clientsWrite1, clockLocal,
                                                continue_G, i_G, getReq,
                                                getResp, clientId_, lockedRead,
                                                clockRead, clockRead0,
                                                clockWrite, keyRead,
                                                clockRead1, replicasWrite0,
                                                clientsRead, clientsWrite2,
                                                clockWrite0, replicasWrite1,
                                                clientsWrite3, clockLocal0,
                                                continue_P, i_P, j_, putReq,
                                                putResp, clientId_P,
                                                clockRead2, clockRead3,
                                                clockWrite1, keyRead0,
                                                valueRead, clockRead4,
                                                lockedWrite, replicasWrite2,
                                                replicasWrite3, clientsRead0,
                                                clientsWrite4, clientsWrite5,
                                                lockedWrite0, clockLocal1,
                                                msg_D, j_D, clientId_D,
                                                lockedRead0, clockWrite2,
                                                replicasWrite4, replicasWrite5,
                                                clockLocal2, continue, i, j,
                                                msg, clientId, clockRead5,
                                                clockRead6, clockWrite3,
                                                clockRead7, replicasWrite6,
                                                replicasWrite7 >>

findMinClock(self) == /\ pc[self] = "findMinClock"
                      /\ IF (i_[self])<(Cardinality(clientsIter[self]))
                            THEN /\ \E client \in clientsIter[self]:
                                      /\ IF ((minClock[self])=(0))\/((currentClocks[self][client])<(minClock[self]))
                                            THEN /\ minClock' = [minClock EXCEPT ![self] = currentClocks[self][client]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED minClock
                                      /\ clientsIter' = [clientsIter EXCEPT ![self] = (clientsIter[self])\({client})]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClock"]
                                 /\ UNCHANGED << i_, lowestPending >>
                            ELSE /\ lowestPending' = [lowestPending EXCEPT ![self] = (minClock[self])+(1)]
                                 /\ i_' = [i_ EXCEPT ![self] = 0]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                                 /\ UNCHANGED << minClock, clientsIter >>
                      /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                      kvLocal, liveClients, pendingRequests,
                                      stableMessages, firstPending, timestamp,
                                      nextClient, chooseMessage, currentClocks,
                                      continue_, pendingClients, msg_, key,
                                      val, mainLoop, replicasRead,
                                      replicasWrite, kvRead, clientsWrite,
                                      clientsWrite0, kvWrite, kvWrite0,
                                      clientsWrite1, clockLocal, continue_G,
                                      i_G, getReq, getResp, clientId_,
                                      lockedRead, clockRead, clockRead0,
                                      clockWrite, keyRead, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      clockLocal0, continue_P, i_P, j_, putReq,
                                      putResp, clientId_P, clockRead2,
                                      clockRead3, clockWrite1, keyRead0,
                                      valueRead, clockRead4, lockedWrite,
                                      replicasWrite2, replicasWrite3,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite0, clockLocal1,
                                      msg_D, j_D, clientId_D, lockedRead0,
                                      clockWrite2, replicasWrite4,
                                      replicasWrite5, clockLocal2, continue, i,
                                      j, msg, clientId, clockRead5, clockRead6,
                                      clockWrite3, clockRead7, replicasWrite6,
                                      replicasWrite7 >>

findMinClient(self) == /\ pc[self] = "findMinClient"
                       /\ IF (i_[self])<(Cardinality(pendingClients[self]))
                             THEN /\ \E client \in pendingClients[self]:
                                       /\ firstPending' = [firstPending EXCEPT ![self] = Head(pendingRequests[self][client])]
                                       /\ Assert((((firstPending'[self]).op)=(GET_MSG))\/(((firstPending'[self]).op)=(PUT_MSG)),
                                                 "Failure of assertion at line 673, column 37.")
                                       /\ timestamp' = [timestamp EXCEPT ![self] = (firstPending'[self]).timestamp]
                                       /\ IF (timestamp'[self])<(minClock[self])
                                             THEN /\ chooseMessage' = [chooseMessage EXCEPT ![self] = ((timestamp'[self])<(lowestPending[self]))\/(((timestamp'[self])=(lowestPending[self]))/\((client)<(nextClient[self])))]
                                                  /\ IF chooseMessage'[self]
                                                        THEN /\ nextClient' = [nextClient EXCEPT ![self] = client]
                                                             /\ lowestPending' = [lowestPending EXCEPT ![self] = timestamp'[self]]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED << nextClient,
                                                                             lowestPending >>
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << nextClient,
                                                                  lowestPending,
                                                                  chooseMessage >>
                                       /\ pendingClients' = [pendingClients EXCEPT ![self] = (pendingClients[self])\({client})]
                                  /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "addStableMessage"]
                                  /\ UNCHANGED << firstPending, timestamp,
                                                  nextClient, lowestPending,
                                                  chooseMessage,
                                                  pendingClients >>
                       /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                       kvLocal, liveClients, pendingRequests,
                                       stableMessages, i_, currentClocks,
                                       minClock, continue_, clientsIter, msg_,
                                       key, val, mainLoop, replicasRead,
                                       replicasWrite, kvRead, clientsWrite,
                                       clientsWrite0, kvWrite, kvWrite0,
                                       clientsWrite1, clockLocal, continue_G,
                                       i_G, getReq, getResp, clientId_,
                                       lockedRead, clockRead, clockRead0,
                                       clockWrite, keyRead, clockRead1,
                                       replicasWrite0, clientsRead,
                                       clientsWrite2, clockWrite0,
                                       replicasWrite1, clientsWrite3,
                                       clockLocal0, continue_P, i_P, j_,
                                       putReq, putResp, clientId_P, clockRead2,
                                       clockRead3, clockWrite1, keyRead0,
                                       valueRead, clockRead4, lockedWrite,
                                       replicasWrite2, replicasWrite3,
                                       clientsRead0, clientsWrite4,
                                       clientsWrite5, lockedWrite0,
                                       clockLocal1, msg_D, j_D, clientId_D,
                                       lockedRead0, clockWrite2,
                                       replicasWrite4, replicasWrite5,
                                       clockLocal2, continue, i, j, msg,
                                       clientId, clockRead5, clockRead6,
                                       clockWrite3, clockRead7, replicasWrite6,
                                       replicasWrite7 >>

addStableMessage(self) == /\ pc[self] = "addStableMessage"
                          /\ IF (lowestPending[self])<(minClock[self])
                                THEN /\ msg_' = [msg_ EXCEPT ![self] = Head(pendingRequests[self][nextClient[self]])]
                                     /\ pendingRequests' = [pendingRequests EXCEPT ![self][nextClient[self]] = Tail(pendingRequests[self][nextClient[self]])]
                                     /\ stableMessages' = [stableMessages EXCEPT ![self] = Append(stableMessages[self], msg_'[self])]
                                     /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                                     /\ UNCHANGED continue_
                                ELSE /\ continue_' = [continue_ EXCEPT ![self] = FALSE]
                                     /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                                     /\ UNCHANGED << pendingRequests,
                                                     stableMessages, msg_ >>
                          /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                          lock, kvLocal, liveClients, i_,
                                          firstPending, timestamp, nextClient,
                                          lowestPending, chooseMessage,
                                          currentClocks, minClock,
                                          pendingClients, clientsIter, key,
                                          val, mainLoop, replicasRead,
                                          replicasWrite, kvRead, clientsWrite,
                                          clientsWrite0, kvWrite, kvWrite0,
                                          clientsWrite1, clockLocal,
                                          continue_G, i_G, getReq, getResp,
                                          clientId_, lockedRead, clockRead,
                                          clockRead0, clockWrite, keyRead,
                                          clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, clockLocal0,
                                          continue_P, i_P, j_, putReq, putResp,
                                          clientId_P, clockRead2, clockRead3,
                                          clockWrite1, keyRead0, valueRead,
                                          clockRead4, lockedWrite,
                                          replicasWrite2, replicasWrite3,
                                          clientsRead0, clientsWrite4,
                                          clientsWrite5, lockedWrite0,
                                          clockLocal1, msg_D, j_D, clientId_D,
                                          lockedRead0, clockWrite2,
                                          replicasWrite4, replicasWrite5,
                                          clockLocal2, continue, i, j, msg,
                                          clientId, clockRead5, clockRead6,
                                          clockWrite3, clockRead7,
                                          replicasWrite6, replicasWrite7 >>

respondPendingRequestsLoop(self) == /\ pc[self] = "respondPendingRequestsLoop"
                                    /\ IF (i_[self])<=(Len(stableMessages[self]))
                                          THEN /\ msg_' = [msg_ EXCEPT ![self] = stableMessages[self][i_[self]]]
                                               /\ i_' = [i_ EXCEPT ![self] = (i_[self])+(1)]
                                               /\ pc' = [pc EXCEPT ![self] = "respondStableGet"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                               /\ UNCHANGED << i_, msg_ >>
                                    /\ UNCHANGED << replicasNetwork,
                                                    clientsNetwork, lock,
                                                    kvLocal, liveClients,
                                                    pendingRequests,
                                                    stableMessages,
                                                    firstPending, timestamp,
                                                    nextClient, lowestPending,
                                                    chooseMessage,
                                                    currentClocks, minClock,
                                                    continue_, pendingClients,
                                                    clientsIter, key, val,
                                                    mainLoop, replicasRead,
                                                    replicasWrite, kvRead,
                                                    clientsWrite,
                                                    clientsWrite0, kvWrite,
                                                    kvWrite0, clientsWrite1,
                                                    clockLocal, continue_G,
                                                    i_G, getReq, getResp,
                                                    clientId_, lockedRead,
                                                    clockRead, clockRead0,
                                                    clockWrite, keyRead,
                                                    clockRead1, replicasWrite0,
                                                    clientsRead, clientsWrite2,
                                                    clockWrite0,
                                                    replicasWrite1,
                                                    clientsWrite3, clockLocal0,
                                                    continue_P, i_P, j_,
                                                    putReq, putResp,
                                                    clientId_P, clockRead2,
                                                    clockRead3, clockWrite1,
                                                    keyRead0, valueRead,
                                                    clockRead4, lockedWrite,
                                                    replicasWrite2,
                                                    replicasWrite3,
                                                    clientsRead0,
                                                    clientsWrite4,
                                                    clientsWrite5,
                                                    lockedWrite0, clockLocal1,
                                                    msg_D, j_D, clientId_D,
                                                    lockedRead0, clockWrite2,
                                                    replicasWrite4,
                                                    replicasWrite5,
                                                    clockLocal2, continue, i,
                                                    j, msg, clientId,
                                                    clockRead5, clockRead6,
                                                    clockWrite3, clockRead7,
                                                    replicasWrite6,
                                                    replicasWrite7 >>

respondStableGet(self) == /\ pc[self] = "respondStableGet"
                          /\ IF ((msg_[self]).op)=(GET_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ kvRead' = [kvRead EXCEPT ![self] = kvLocal[self][key'[self]]]
                                     /\ val' = [val EXCEPT ![self] = kvRead'[self]]
                                     /\ (Len(clientsNetwork[(msg_[self]).client]))<(BUFFER_SIZE)
                                     /\ clientsWrite' = [clientsWrite EXCEPT ![self] = [clientsNetwork EXCEPT ![(msg_[self]).client] = Append(clientsNetwork[(msg_[self]).client], [type |-> GET_RESPONSE, result |-> val'[self]])]]
                                     /\ clientsWrite0' = [clientsWrite0 EXCEPT ![self] = clientsWrite'[self]]
                                     /\ clientsNetwork' = clientsWrite0'[self]
                                ELSE /\ clientsWrite0' = [clientsWrite0 EXCEPT ![self] = clientsNetwork]
                                     /\ clientsNetwork' = clientsWrite0'[self]
                                     /\ UNCHANGED << key, val, kvRead,
                                                     clientsWrite >>
                          /\ pc' = [pc EXCEPT ![self] = "respondStablePut"]
                          /\ UNCHANGED << replicasNetwork, lock, kvLocal,
                                          liveClients, pendingRequests,
                                          stableMessages, i_, firstPending,
                                          timestamp, nextClient, lowestPending,
                                          chooseMessage, currentClocks,
                                          minClock, continue_, pendingClients,
                                          clientsIter, msg_, mainLoop,
                                          replicasRead, replicasWrite, kvWrite,
                                          kvWrite0, clientsWrite1, clockLocal,
                                          continue_G, i_G, getReq, getResp,
                                          clientId_, lockedRead, clockRead,
                                          clockRead0, clockWrite, keyRead,
                                          clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, clockLocal0,
                                          continue_P, i_P, j_, putReq, putResp,
                                          clientId_P, clockRead2, clockRead3,
                                          clockWrite1, keyRead0, valueRead,
                                          clockRead4, lockedWrite,
                                          replicasWrite2, replicasWrite3,
                                          clientsRead0, clientsWrite4,
                                          clientsWrite5, lockedWrite0,
                                          clockLocal1, msg_D, j_D, clientId_D,
                                          lockedRead0, clockWrite2,
                                          replicasWrite4, replicasWrite5,
                                          clockLocal2, continue, i, j, msg,
                                          clientId, clockRead5, clockRead6,
                                          clockWrite3, clockRead7,
                                          replicasWrite6, replicasWrite7 >>

respondStablePut(self) == /\ pc[self] = "respondStablePut"
                          /\ IF ((msg_[self]).op)=(PUT_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ val' = [val EXCEPT ![self] = (msg_[self]).value]
                                     /\ kvWrite' = [kvWrite EXCEPT ![self] = [kvLocal[self] EXCEPT ![key'[self]] = val'[self]]]
                                     /\ (Len(clientsNetwork[(msg_[self]).client]))<(BUFFER_SIZE)
                                     /\ clientsWrite' = [clientsWrite EXCEPT ![self] = [clientsNetwork EXCEPT ![(msg_[self]).client] = Append(clientsNetwork[(msg_[self]).client], [type |-> PUT_RESPONSE, result |-> PUT_OK])]]
                                     /\ kvWrite0' = [kvWrite0 EXCEPT ![self] = kvWrite'[self]]
                                     /\ clientsWrite1' = [clientsWrite1 EXCEPT ![self] = clientsWrite'[self]]
                                     /\ clientsNetwork' = clientsWrite1'[self]
                                     /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite0'[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                ELSE /\ kvWrite0' = [kvWrite0 EXCEPT ![self] = kvLocal[self]]
                                     /\ clientsWrite1' = [clientsWrite1 EXCEPT ![self] = clientsNetwork]
                                     /\ clientsNetwork' = clientsWrite1'[self]
                                     /\ kvLocal' = [kvLocal EXCEPT ![self] = kvWrite0'[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "respondPendingRequestsLoop"]
                                     /\ UNCHANGED << key, val, clientsWrite,
                                                     kvWrite >>
                          /\ UNCHANGED << replicasNetwork, lock, liveClients,
                                          pendingRequests, stableMessages, i_,
                                          firstPending, timestamp, nextClient,
                                          lowestPending, chooseMessage,
                                          currentClocks, minClock, continue_,
                                          pendingClients, clientsIter, msg_,
                                          mainLoop, replicasRead,
                                          replicasWrite, kvRead, clientsWrite0,
                                          clockLocal, continue_G, i_G, getReq,
                                          getResp, clientId_, lockedRead,
                                          clockRead, clockRead0, clockWrite,
                                          keyRead, clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, clockLocal0,
                                          continue_P, i_P, j_, putReq, putResp,
                                          clientId_P, clockRead2, clockRead3,
                                          clockWrite1, keyRead0, valueRead,
                                          clockRead4, lockedWrite,
                                          replicasWrite2, replicasWrite3,
                                          clientsRead0, clientsWrite4,
                                          clientsWrite5, lockedWrite0,
                                          clockLocal1, msg_D, j_D, clientId_D,
                                          lockedRead0, clockWrite2,
                                          replicasWrite4, replicasWrite5,
                                          clockLocal2, continue, i, j, msg,
                                          clientId, clockRead5, clockRead6,
                                          clockWrite3, clockRead7,
                                          replicasWrite6, replicasWrite7 >>

Replica(self) == replicaLoop(self) \/ receiveClientRequest(self)
                    \/ clientDisconnected(self) \/ replicaGetRequest(self)
                    \/ replicaPutRequest(self) \/ replicaNullRequest(self)
                    \/ findStableRequestsLoop(self) \/ findMinClock(self)
                    \/ findMinClient(self) \/ addStableMessage(self)
                    \/ respondPendingRequestsLoop(self)
                    \/ respondStableGet(self) \/ respondStablePut(self)

getLoop(self) == /\ pc[self] = "getLoop"
                 /\ IF continue_G[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "getRequest"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                 kvLocal, liveClients, pendingRequests,
                                 stableMessages, i_, firstPending, timestamp,
                                 nextClient, lowestPending, chooseMessage,
                                 currentClocks, minClock, continue_,
                                 pendingClients, clientsIter, msg_, key, val,
                                 mainLoop, replicasRead, replicasWrite, kvRead,
                                 clientsWrite, clientsWrite0, kvWrite,
                                 kvWrite0, clientsWrite1, clockLocal,
                                 continue_G, i_G, getReq, getResp, clientId_,
                                 lockedRead, clockRead, clockRead0, clockWrite,
                                 keyRead, clockRead1, replicasWrite0,
                                 clientsRead, clientsWrite2, clockWrite0,
                                 replicasWrite1, clientsWrite3, clockLocal0,
                                 continue_P, i_P, j_, putReq, putResp,
                                 clientId_P, clockRead2, clockRead3,
                                 clockWrite1, keyRead0, valueRead, clockRead4,
                                 lockedWrite, replicasWrite2, replicasWrite3,
                                 clientsRead0, clientsWrite4, clientsWrite5,
                                 lockedWrite0, clockLocal1, msg_D, j_D,
                                 clientId_D, lockedRead0, clockWrite2,
                                 replicasWrite4, replicasWrite5, clockLocal2,
                                 continue, i, j, msg, clientId, clockRead5,
                                 clockRead6, clockWrite3, clockRead7,
                                 replicasWrite6, replicasWrite7 >>

getRequest(self) == /\ pc[self] = "getRequest"
                    /\ clientId_' = [clientId_ EXCEPT ![self] = (self)-((NUM_CLIENTS)*(GET_ORDER))]
                    /\ lockedRead' = [lockedRead EXCEPT ![self] = lock[clientId_'[self]]]
                    /\ ~(lockedRead'[self])
                    /\ clockRead' = [clockRead EXCEPT ![self] = clockLocal[self]]
                    /\ IF (clockRead'[self])=(-(1))
                          THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                               /\ clockWrite0' = [clockWrite0 EXCEPT ![self] = clockLocal[self]]
                               /\ replicasWrite1' = [replicasWrite1 EXCEPT ![self] = replicasNetwork]
                               /\ clientsWrite3' = [clientsWrite3 EXCEPT ![self] = clientsNetwork]
                               /\ replicasNetwork' = replicasWrite1'[self]
                               /\ clientsNetwork' = clientsWrite3'[self]
                               /\ clockLocal' = [clockLocal EXCEPT ![self] = clockWrite0'[self]]
                               /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                               /\ UNCHANGED << getReq, getResp, clockRead0,
                                               clockWrite, keyRead, clockRead1,
                                               replicasWrite0, clientsRead,
                                               clientsWrite2 >>
                          ELSE /\ clockRead0' = [clockRead0 EXCEPT ![self] = clockLocal[self]]
                               /\ clockWrite' = [clockWrite EXCEPT ![self] = (clockRead0'[self])+(1)]
                               /\ keyRead' = [keyRead EXCEPT ![self] = GET_KEY]
                               /\ clockRead1' = [clockRead1 EXCEPT ![self] = clockWrite'[self]]
                               /\ getReq' = [getReq EXCEPT ![self] = [op |-> GET_MSG, key |-> keyRead'[self], client |-> clientId_'[self], timestamp |-> clockRead1'[self]]]
                               /\ \E dst \in ReplicaSet:
                                    /\ (Len(replicasNetwork[dst]))<(BUFFER_SIZE)
                                    /\ replicasWrite0' = [replicasWrite0 EXCEPT ![self] = [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq'[self])]]
                               /\ (Len(clientsNetwork[clientId_'[self]]))>(0)
                               /\ LET msg1 == Head(clientsNetwork[clientId_'[self]]) IN
                                    /\ clientsWrite2' = [clientsWrite2 EXCEPT ![self] = [clientsNetwork EXCEPT ![clientId_'[self]] = Tail(clientsNetwork[clientId_'[self]])]]
                                    /\ clientsRead' = [clientsRead EXCEPT ![self] = msg1]
                               /\ getResp' = [getResp EXCEPT ![self] = clientsRead'[self]]
                               /\ clockWrite0' = [clockWrite0 EXCEPT ![self] = clockWrite'[self]]
                               /\ replicasWrite1' = [replicasWrite1 EXCEPT ![self] = replicasWrite0'[self]]
                               /\ clientsWrite3' = [clientsWrite3 EXCEPT ![self] = clientsWrite2'[self]]
                               /\ replicasNetwork' = replicasWrite1'[self]
                               /\ clientsNetwork' = clientsWrite3'[self]
                               /\ clockLocal' = [clockLocal EXCEPT ![self] = clockWrite0'[self]]
                               /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                               /\ UNCHANGED continue_G
                    /\ UNCHANGED << lock, kvLocal, liveClients,
                                    pendingRequests, stableMessages, i_,
                                    firstPending, timestamp, nextClient,
                                    lowestPending, chooseMessage,
                                    currentClocks, minClock, continue_,
                                    pendingClients, clientsIter, msg_, key,
                                    val, mainLoop, replicasRead, replicasWrite,
                                    kvRead, clientsWrite, clientsWrite0,
                                    kvWrite, kvWrite0, clientsWrite1, i_G,
                                    clockLocal0, continue_P, i_P, j_, putReq,
                                    putResp, clientId_P, clockRead2,
                                    clockRead3, clockWrite1, keyRead0,
                                    valueRead, clockRead4, lockedWrite,
                                    replicasWrite2, replicasWrite3,
                                    clientsRead0, clientsWrite4, clientsWrite5,
                                    lockedWrite0, clockLocal1, msg_D, j_D,
                                    clientId_D, lockedRead0, clockWrite2,
                                    replicasWrite4, replicasWrite5,
                                    clockLocal2, continue, i, j, msg, clientId,
                                    clockRead5, clockRead6, clockWrite3,
                                    clockRead7, replicasWrite6, replicasWrite7 >>

GetClient(self) == getLoop(self) \/ getRequest(self)

putLoop(self) == /\ pc[self] = "putLoop"
                 /\ IF continue_P[self]
                       THEN /\ clientId_P' = [clientId_P EXCEPT ![self] = (self)-((NUM_CLIENTS)*(PUT_ORDER))]
                            /\ pc' = [pc EXCEPT ![self] = "putRequest"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED clientId_P
                 /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                 kvLocal, liveClients, pendingRequests,
                                 stableMessages, i_, firstPending, timestamp,
                                 nextClient, lowestPending, chooseMessage,
                                 currentClocks, minClock, continue_,
                                 pendingClients, clientsIter, msg_, key, val,
                                 mainLoop, replicasRead, replicasWrite, kvRead,
                                 clientsWrite, clientsWrite0, kvWrite,
                                 kvWrite0, clientsWrite1, clockLocal,
                                 continue_G, i_G, getReq, getResp, clientId_,
                                 lockedRead, clockRead, clockRead0, clockWrite,
                                 keyRead, clockRead1, replicasWrite0,
                                 clientsRead, clientsWrite2, clockWrite0,
                                 replicasWrite1, clientsWrite3, clockLocal0,
                                 continue_P, i_P, j_, putReq, putResp,
                                 clockRead2, clockRead3, clockWrite1, keyRead0,
                                 valueRead, clockRead4, lockedWrite,
                                 replicasWrite2, replicasWrite3, clientsRead0,
                                 clientsWrite4, clientsWrite5, lockedWrite0,
                                 clockLocal1, msg_D, j_D, clientId_D,
                                 lockedRead0, clockWrite2, replicasWrite4,
                                 replicasWrite5, clockLocal2, continue, i, j,
                                 msg, clientId, clockRead5, clockRead6,
                                 clockWrite3, clockRead7, replicasWrite6,
                                 replicasWrite7 >>

putRequest(self) == /\ pc[self] = "putRequest"
                    /\ clockRead2' = [clockRead2 EXCEPT ![self] = clockLocal0[self]]
                    /\ IF (clockRead2'[self])=(-(1))
                          THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                               /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                               /\ UNCHANGED << lock, clockLocal0, i_P, j_,
                                               putReq, clockRead3, clockWrite1,
                                               keyRead0, valueRead, clockRead4,
                                               lockedWrite >>
                          ELSE /\ clockRead3' = [clockRead3 EXCEPT ![self] = clockLocal0[self]]
                               /\ clockWrite1' = [clockWrite1 EXCEPT ![self] = (clockRead3'[self])+(1)]
                               /\ keyRead0' = [keyRead0 EXCEPT ![self] = PUT_KEY]
                               /\ valueRead' = [valueRead EXCEPT ![self] = PUT_VALUE]
                               /\ clockRead4' = [clockRead4 EXCEPT ![self] = clockWrite1'[self]]
                               /\ putReq' = [putReq EXCEPT ![self] = [op |-> PUT_MSG, key |-> keyRead0'[self], value |-> valueRead'[self], client |-> clientId_P[self], timestamp |-> clockRead4'[self]]]
                               /\ lockedWrite' = [lockedWrite EXCEPT ![self] = [lock EXCEPT ![clientId_P[self]] = TRUE]]
                               /\ i_P' = [i_P EXCEPT ![self] = 0]
                               /\ j_' = [j_ EXCEPT ![self] = 1]
                               /\ lock' = lockedWrite'[self]
                               /\ clockLocal0' = [clockLocal0 EXCEPT ![self] = clockWrite1'[self]]
                               /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                               /\ UNCHANGED continue_P
                    /\ UNCHANGED << replicasNetwork, clientsNetwork, kvLocal,
                                    liveClients, pendingRequests,
                                    stableMessages, i_, firstPending,
                                    timestamp, nextClient, lowestPending,
                                    chooseMessage, currentClocks, minClock,
                                    continue_, pendingClients, clientsIter,
                                    msg_, key, val, mainLoop, replicasRead,
                                    replicasWrite, kvRead, clientsWrite,
                                    clientsWrite0, kvWrite, kvWrite0,
                                    clientsWrite1, clockLocal, continue_G, i_G,
                                    getReq, getResp, clientId_, lockedRead,
                                    clockRead, clockRead0, clockWrite, keyRead,
                                    clockRead1, replicasWrite0, clientsRead,
                                    clientsWrite2, clockWrite0, replicasWrite1,
                                    clientsWrite3, putResp, clientId_P,
                                    replicasWrite2, replicasWrite3,
                                    clientsRead0, clientsWrite4, clientsWrite5,
                                    lockedWrite0, clockLocal1, msg_D, j_D,
                                    clientId_D, lockedRead0, clockWrite2,
                                    replicasWrite4, replicasWrite5,
                                    clockLocal2, continue, i, j, msg, clientId,
                                    clockRead5, clockRead6, clockWrite3,
                                    clockRead7, replicasWrite6, replicasWrite7 >>

putBroadcast(self) == /\ pc[self] = "putBroadcast"
                      /\ IF (j_[self])<=(NUM_REPLICAS)
                            THEN /\ (Len(replicasNetwork[j_[self]]))<(BUFFER_SIZE)
                                 /\ replicasWrite2' = [replicasWrite2 EXCEPT ![self] = [replicasNetwork EXCEPT ![j_[self]] = Append(replicasNetwork[j_[self]], putReq[self])]]
                                 /\ j_' = [j_ EXCEPT ![self] = (j_[self])+(1)]
                                 /\ replicasWrite3' = [replicasWrite3 EXCEPT ![self] = replicasWrite2'[self]]
                                 /\ replicasNetwork' = replicasWrite3'[self]
                                 /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                            ELSE /\ replicasWrite3' = [replicasWrite3 EXCEPT ![self] = replicasNetwork]
                                 /\ replicasNetwork' = replicasWrite3'[self]
                                 /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                 /\ UNCHANGED << j_, replicasWrite2 >>
                      /\ UNCHANGED << clientsNetwork, lock, kvLocal,
                                      liveClients, pendingRequests,
                                      stableMessages, i_, firstPending,
                                      timestamp, nextClient, lowestPending,
                                      chooseMessage, currentClocks, minClock,
                                      continue_, pendingClients, clientsIter,
                                      msg_, key, val, mainLoop, replicasRead,
                                      replicasWrite, kvRead, clientsWrite,
                                      clientsWrite0, kvWrite, kvWrite0,
                                      clientsWrite1, clockLocal, continue_G,
                                      i_G, getReq, getResp, clientId_,
                                      lockedRead, clockRead, clockRead0,
                                      clockWrite, keyRead, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      clockLocal0, continue_P, i_P, putReq,
                                      putResp, clientId_P, clockRead2,
                                      clockRead3, clockWrite1, keyRead0,
                                      valueRead, clockRead4, lockedWrite,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite0, clockLocal1,
                                      msg_D, j_D, clientId_D, lockedRead0,
                                      clockWrite2, replicasWrite4,
                                      replicasWrite5, clockLocal2, continue, i,
                                      j, msg, clientId, clockRead5, clockRead6,
                                      clockWrite3, clockRead7, replicasWrite6,
                                      replicasWrite7 >>

putResponse(self) == /\ pc[self] = "putResponse"
                     /\ IF (i_P[self])<(Cardinality(ReplicaSet))
                           THEN /\ (Len(clientsNetwork[clientId_P[self]]))>(0)
                                /\ LET msg2 == Head(clientsNetwork[clientId_P[self]]) IN
                                     /\ clientsWrite4' = [clientsWrite4 EXCEPT ![self] = [clientsNetwork EXCEPT ![clientId_P[self]] = Tail(clientsNetwork[clientId_P[self]])]]
                                     /\ clientsRead0' = [clientsRead0 EXCEPT ![self] = msg2]
                                /\ putResp' = [putResp EXCEPT ![self] = clientsRead0'[self]]
                                /\ Assert((((putResp'[self]).type)=(PUT_RESPONSE))/\(((putResp'[self]).result)=(PUT_OK)),
                                          "Failure of assertion at line 838, column 33.")
                                /\ i_P' = [i_P EXCEPT ![self] = (i_P[self])+(1)]
                                /\ clientsWrite5' = [clientsWrite5 EXCEPT ![self] = clientsWrite4'[self]]
                                /\ lockedWrite0' = [lockedWrite0 EXCEPT ![self] = lock]
                                /\ clientsNetwork' = clientsWrite5'[self]
                                /\ lock' = lockedWrite0'[self]
                                /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                /\ UNCHANGED lockedWrite
                           ELSE /\ lockedWrite' = [lockedWrite EXCEPT ![self] = [lock EXCEPT ![clientId_P[self]] = FALSE]]
                                /\ clientsWrite5' = [clientsWrite5 EXCEPT ![self] = clientsNetwork]
                                /\ lockedWrite0' = [lockedWrite0 EXCEPT ![self] = lockedWrite'[self]]
                                /\ clientsNetwork' = clientsWrite5'[self]
                                /\ lock' = lockedWrite0'[self]
                                /\ pc' = [pc EXCEPT ![self] = "putComplete"]
                                /\ UNCHANGED << i_P, putResp, clientsRead0,
                                                clientsWrite4 >>
                     /\ UNCHANGED << replicasNetwork, kvLocal, liveClients,
                                     pendingRequests, stableMessages, i_,
                                     firstPending, timestamp, nextClient,
                                     lowestPending, chooseMessage,
                                     currentClocks, minClock, continue_,
                                     pendingClients, clientsIter, msg_, key,
                                     val, mainLoop, replicasRead,
                                     replicasWrite, kvRead, clientsWrite,
                                     clientsWrite0, kvWrite, kvWrite0,
                                     clientsWrite1, clockLocal, continue_G,
                                     i_G, getReq, getResp, clientId_,
                                     lockedRead, clockRead, clockRead0,
                                     clockWrite, keyRead, clockRead1,
                                     replicasWrite0, clientsRead,
                                     clientsWrite2, clockWrite0,
                                     replicasWrite1, clientsWrite3,
                                     clockLocal0, continue_P, j_, putReq,
                                     clientId_P, clockRead2, clockRead3,
                                     clockWrite1, keyRead0, valueRead,
                                     clockRead4, replicasWrite2,
                                     replicasWrite3, clockLocal1, msg_D, j_D,
                                     clientId_D, lockedRead0, clockWrite2,
                                     replicasWrite4, replicasWrite5,
                                     clockLocal2, continue, i, j, msg,
                                     clientId, clockRead5, clockRead6,
                                     clockWrite3, clockRead7, replicasWrite6,
                                     replicasWrite7 >>

putComplete(self) == /\ pc[self] = "putComplete"
                     /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                     /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                     kvLocal, liveClients, pendingRequests,
                                     stableMessages, i_, firstPending,
                                     timestamp, nextClient, lowestPending,
                                     chooseMessage, currentClocks, minClock,
                                     continue_, pendingClients, clientsIter,
                                     msg_, key, val, mainLoop, replicasRead,
                                     replicasWrite, kvRead, clientsWrite,
                                     clientsWrite0, kvWrite, kvWrite0,
                                     clientsWrite1, clockLocal, continue_G,
                                     i_G, getReq, getResp, clientId_,
                                     lockedRead, clockRead, clockRead0,
                                     clockWrite, keyRead, clockRead1,
                                     replicasWrite0, clientsRead,
                                     clientsWrite2, clockWrite0,
                                     replicasWrite1, clientsWrite3,
                                     clockLocal0, continue_P, i_P, j_, putReq,
                                     putResp, clientId_P, clockRead2,
                                     clockRead3, clockWrite1, keyRead0,
                                     valueRead, clockRead4, lockedWrite,
                                     replicasWrite2, replicasWrite3,
                                     clientsRead0, clientsWrite4,
                                     clientsWrite5, lockedWrite0, clockLocal1,
                                     msg_D, j_D, clientId_D, lockedRead0,
                                     clockWrite2, replicasWrite4,
                                     replicasWrite5, clockLocal2, continue, i,
                                     j, msg, clientId, clockRead5, clockRead6,
                                     clockWrite3, clockRead7, replicasWrite6,
                                     replicasWrite7 >>

PutClient(self) == putLoop(self) \/ putRequest(self) \/ putBroadcast(self)
                      \/ putResponse(self) \/ putComplete(self)

sendDisconnectRequest(self) == /\ pc[self] = "sendDisconnectRequest"
                               /\ clientId_D' = [clientId_D EXCEPT ![self] = (self)-((NUM_CLIENTS)*(DISCONNECT_ORDER))]
                               /\ lockedRead0' = [lockedRead0 EXCEPT ![self] = lock[clientId_D'[self]]]
                               /\ ~(lockedRead0'[self])
                               /\ msg_D' = [msg_D EXCEPT ![self] = [op |-> DISCONNECT_MSG, client |-> clientId_D'[self]]]
                               /\ clockWrite2' = [clockWrite2 EXCEPT ![self] = -(1)]
                               /\ j_D' = [j_D EXCEPT ![self] = 1]
                               /\ clockLocal1' = [clockLocal1 EXCEPT ![self] = clockWrite2'[self]]
                               /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                               /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                               lock, kvLocal, liveClients,
                                               pendingRequests, stableMessages,
                                               i_, firstPending, timestamp,
                                               nextClient, lowestPending,
                                               chooseMessage, currentClocks,
                                               minClock, continue_,
                                               pendingClients, clientsIter,
                                               msg_, key, val, mainLoop,
                                               replicasRead, replicasWrite,
                                               kvRead, clientsWrite,
                                               clientsWrite0, kvWrite,
                                               kvWrite0, clientsWrite1,
                                               clockLocal, continue_G, i_G,
                                               getReq, getResp, clientId_,
                                               lockedRead, clockRead,
                                               clockRead0, clockWrite, keyRead,
                                               clockRead1, replicasWrite0,
                                               clientsRead, clientsWrite2,
                                               clockWrite0, replicasWrite1,
                                               clientsWrite3, clockLocal0,
                                               continue_P, i_P, j_, putReq,
                                               putResp, clientId_P, clockRead2,
                                               clockRead3, clockWrite1,
                                               keyRead0, valueRead, clockRead4,
                                               lockedWrite, replicasWrite2,
                                               replicasWrite3, clientsRead0,
                                               clientsWrite4, clientsWrite5,
                                               lockedWrite0, replicasWrite4,
                                               replicasWrite5, clockLocal2,
                                               continue, i, j, msg, clientId,
                                               clockRead5, clockRead6,
                                               clockWrite3, clockRead7,
                                               replicasWrite6, replicasWrite7 >>

disconnectBroadcast(self) == /\ pc[self] = "disconnectBroadcast"
                             /\ IF (j_D[self])<=(NUM_REPLICAS)
                                   THEN /\ (Len(replicasNetwork[j_D[self]]))<(BUFFER_SIZE)
                                        /\ replicasWrite4' = [replicasWrite4 EXCEPT ![self] = [replicasNetwork EXCEPT ![j_D[self]] = Append(replicasNetwork[j_D[self]], msg_D[self])]]
                                        /\ j_D' = [j_D EXCEPT ![self] = (j_D[self])+(1)]
                                        /\ replicasWrite5' = [replicasWrite5 EXCEPT ![self] = replicasWrite4'[self]]
                                        /\ replicasNetwork' = replicasWrite5'[self]
                                        /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                                   ELSE /\ replicasWrite5' = [replicasWrite5 EXCEPT ![self] = replicasNetwork]
                                        /\ replicasNetwork' = replicasWrite5'[self]
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << j_D, replicasWrite4 >>
                             /\ UNCHANGED << clientsNetwork, lock, kvLocal,
                                             liveClients, pendingRequests,
                                             stableMessages, i_, firstPending,
                                             timestamp, nextClient,
                                             lowestPending, chooseMessage,
                                             currentClocks, minClock,
                                             continue_, pendingClients,
                                             clientsIter, msg_, key, val,
                                             mainLoop, replicasRead,
                                             replicasWrite, kvRead,
                                             clientsWrite, clientsWrite0,
                                             kvWrite, kvWrite0, clientsWrite1,
                                             clockLocal, continue_G, i_G,
                                             getReq, getResp, clientId_,
                                             lockedRead, clockRead, clockRead0,
                                             clockWrite, keyRead, clockRead1,
                                             replicasWrite0, clientsRead,
                                             clientsWrite2, clockWrite0,
                                             replicasWrite1, clientsWrite3,
                                             clockLocal0, continue_P, i_P, j_,
                                             putReq, putResp, clientId_P,
                                             clockRead2, clockRead3,
                                             clockWrite1, keyRead0, valueRead,
                                             clockRead4, lockedWrite,
                                             replicasWrite2, replicasWrite3,
                                             clientsRead0, clientsWrite4,
                                             clientsWrite5, lockedWrite0,
                                             clockLocal1, msg_D, clientId_D,
                                             lockedRead0, clockWrite2,
                                             clockLocal2, continue, i, j, msg,
                                             clientId, clockRead5, clockRead6,
                                             clockWrite3, clockRead7,
                                             replicasWrite6, replicasWrite7 >>

DisconnectClient(self) == sendDisconnectRequest(self)
                             \/ disconnectBroadcast(self)

clockUpdateLoop(self) == /\ pc[self] = "clockUpdateLoop"
                         /\ IF continue[self]
                               THEN /\ clientId' = [clientId EXCEPT ![self] = (self)-((NUM_CLIENTS)*(NULL_ORDER))]
                                    /\ clockRead5' = [clockRead5 EXCEPT ![self] = clockLocal2[self]]
                                    /\ IF (clockRead5'[self])=(-(1))
                                          THEN /\ continue' = [continue EXCEPT ![self] = FALSE]
                                               /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                                               /\ UNCHANGED << clockLocal2, j,
                                                               msg, clockRead6,
                                                               clockWrite3,
                                                               clockRead7 >>
                                          ELSE /\ clockRead6' = [clockRead6 EXCEPT ![self] = clockLocal2[self]]
                                               /\ clockWrite3' = [clockWrite3 EXCEPT ![self] = (clockRead6'[self])+(1)]
                                               /\ clockRead7' = [clockRead7 EXCEPT ![self] = clockWrite3'[self]]
                                               /\ msg' = [msg EXCEPT ![self] = [op |-> NULL_MSG, client |-> clientId'[self], timestamp |-> clockRead7'[self]]]
                                               /\ j' = [j EXCEPT ![self] = 1]
                                               /\ clockLocal2' = [clockLocal2 EXCEPT ![self] = clockWrite3'[self]]
                                               /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                                               /\ UNCHANGED continue
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << clockLocal2, continue, j,
                                                    msg, clientId, clockRead5,
                                                    clockRead6, clockWrite3,
                                                    clockRead7 >>
                         /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                         kvLocal, liveClients, pendingRequests,
                                         stableMessages, i_, firstPending,
                                         timestamp, nextClient, lowestPending,
                                         chooseMessage, currentClocks,
                                         minClock, continue_, pendingClients,
                                         clientsIter, msg_, key, val, mainLoop,
                                         replicasRead, replicasWrite, kvRead,
                                         clientsWrite, clientsWrite0, kvWrite,
                                         kvWrite0, clientsWrite1, clockLocal,
                                         continue_G, i_G, getReq, getResp,
                                         clientId_, lockedRead, clockRead,
                                         clockRead0, clockWrite, keyRead,
                                         clockRead1, replicasWrite0,
                                         clientsRead, clientsWrite2,
                                         clockWrite0, replicasWrite1,
                                         clientsWrite3, clockLocal0,
                                         continue_P, i_P, j_, putReq, putResp,
                                         clientId_P, clockRead2, clockRead3,
                                         clockWrite1, keyRead0, valueRead,
                                         clockRead4, lockedWrite,
                                         replicasWrite2, replicasWrite3,
                                         clientsRead0, clientsWrite4,
                                         clientsWrite5, lockedWrite0,
                                         clockLocal1, msg_D, j_D, clientId_D,
                                         lockedRead0, clockWrite2,
                                         replicasWrite4, replicasWrite5, i,
                                         replicasWrite6, replicasWrite7 >>

nullBroadcast(self) == /\ pc[self] = "nullBroadcast"
                       /\ IF (j[self])<=(NUM_REPLICAS)
                             THEN /\ (Len(replicasNetwork[j[self]]))<(BUFFER_SIZE)
                                  /\ replicasWrite6' = [replicasWrite6 EXCEPT ![self] = [replicasNetwork EXCEPT ![j[self]] = Append(replicasNetwork[j[self]], msg[self])]]
                                  /\ j' = [j EXCEPT ![self] = (j[self])+(1)]
                                  /\ replicasWrite7' = [replicasWrite7 EXCEPT ![self] = replicasWrite6'[self]]
                                  /\ replicasNetwork' = replicasWrite7'[self]
                                  /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                             ELSE /\ replicasWrite7' = [replicasWrite7 EXCEPT ![self] = replicasNetwork]
                                  /\ replicasNetwork' = replicasWrite7'[self]
                                  /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                                  /\ UNCHANGED << j, replicasWrite6 >>
                       /\ UNCHANGED << clientsNetwork, lock, kvLocal,
                                       liveClients, pendingRequests,
                                       stableMessages, i_, firstPending,
                                       timestamp, nextClient, lowestPending,
                                       chooseMessage, currentClocks, minClock,
                                       continue_, pendingClients, clientsIter,
                                       msg_, key, val, mainLoop, replicasRead,
                                       replicasWrite, kvRead, clientsWrite,
                                       clientsWrite0, kvWrite, kvWrite0,
                                       clientsWrite1, clockLocal, continue_G,
                                       i_G, getReq, getResp, clientId_,
                                       lockedRead, clockRead, clockRead0,
                                       clockWrite, keyRead, clockRead1,
                                       replicasWrite0, clientsRead,
                                       clientsWrite2, clockWrite0,
                                       replicasWrite1, clientsWrite3,
                                       clockLocal0, continue_P, i_P, j_,
                                       putReq, putResp, clientId_P, clockRead2,
                                       clockRead3, clockWrite1, keyRead0,
                                       valueRead, clockRead4, lockedWrite,
                                       replicasWrite2, replicasWrite3,
                                       clientsRead0, clientsWrite4,
                                       clientsWrite5, lockedWrite0,
                                       clockLocal1, msg_D, j_D, clientId_D,
                                       lockedRead0, clockWrite2,
                                       replicasWrite4, replicasWrite5,
                                       clockLocal2, continue, i, msg, clientId,
                                       clockRead5, clockRead6, clockWrite3,
                                       clockRead7 >>

ClockUpdateClient(self) == clockUpdateLoop(self) \/ nullBroadcast(self)

Next == (\E self \in ReplicaSet: Replica(self))
           \/ (\E self \in GetSet: GetClient(self))
           \/ (\E self \in PutSet: PutClient(self))
           \/ (\E self \in DisconnectSet: DisconnectClient(self))
           \/ (\E self \in NullSet: ClockUpdateClient(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ReplicaSet : WF_vars(Replica(self))
        /\ \A self \in GetSet : WF_vars(GetClient(self))
        /\ \A self \in PutSet : WF_vars(PutClient(self))
        /\ \A self \in DisconnectSet : WF_vars(DisconnectClient(self))
        /\ \A self \in NullSet : WF_vars(ClockUpdateClient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* This predicate is true when all client processes are finished.
AllClientsDisconnected == LET allClients == GetSet \cup PutSet \cup DisconnectSet \cup NullSet
                          IN
                             \A client \in allClients : pc[client] = "Done"


\* Invariants
\* **********

\* These ensure that, in all states explored by TLC, the buffers (from client to replica and vice versa)
\* are within bounds. Using the FIFOChannel mapping macro is sufficient for this invariant to
\* hold.
BufferOk(net, node) == Len(net[node]) >= 0 /\ Len(net[node]) <= BUFFER_SIZE
ClientBuffersOk == \A node \in DOMAIN clientsNetwork : BufferOk(clientsNetwork, node)
ReplicaBuffersOk == \A node \in DOMAIN replicasNetwork : BufferOk(replicasNetwork, node)
AllBuffersOk == ClientBuffersOk /\ ReplicaBuffersOk

\* This invariant tests that message stability detection in the replica is safe:
\* every message considered stable must have a timestamp lower than the current logical
\* clock of any live client.
MessageStability == \A replica \in ReplicaSet :
                        LET stable == stableMessages[replica]
                            alive == { c \in ClientSet : clockLocal[c] > 0 }
                        IN
                            Len(stable) > 0 =>
                                \A m_id \in DOMAIN stable :
                                    \A client \in alive : stable[m_id].timestamp < clockLocal[client]


\* Put semantics: once a client has been notified that a Put request was succesful
\* every replica must have the updated value.
PersistentPut == \A client \in PutSet :
                     pc[client] = "putComplete" => \A replica \in ReplicaSet : kvLocal[replica][PUT_KEY] = PUT_VALUE


\* Properties
\* **********

\* Logical clocks are monotonically increasing. This property checks that in every state,
\* pending messages in the replicas have increasing timestamps (or the process disconnected)
ClockIncreased == clockLocal' /= clockLocal =>
                 \E c \in ClientSet : clockLocal'[c] = clockLocal[c]+1 \/ clockLocal'[c] = -1

MonotonicallyIncreasingClocks == [][ClockIncreased]_<<clockLocal>>


\* Safety of disconnection: once a client has disconnected (and sent a message to all replicas
\* informing of that event), then the logical clock of that client should remain
\* unchanced -- i.e., no more messages from that client should be seen in the system.
DisconnectionSafe == \A client \in ClientSet : <>[](clockLocal[client] = -1)

=============================================================================
\* Modification History
\* Last modified Wed Mar 06 19:29:48 PST 2019 by rmc
\* Last modified Wed Feb 27 12:42:52 PST 2019 by minh
