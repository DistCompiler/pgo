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

\* These constants allow PlusCal processes to derive their client identifiers from
\* their PlusCal identifiers.
GET_ORDER == 0
PUT_ORDER == 1
DISCONNECT_ORDER == 2
NULL_ORDER == 3

\* We have clients that perform each of the operations supported by our Replicated KV-store:
\* Get, Put, Disconnect, and ClockUpdate (or 'null' request). PlusCal requires that every process
\* has a unique identifier. The set definitions below just ensure that our clients have
\* consecutive identifiers.
GetSet == (NUM_REPLICAS)..(NUM_REPLICAS+NUM_CLIENTS-1)
PutSet == (NUM_REPLICAS+NUM_CLIENTS)..(NUM_REPLICAS + 2*NUM_CLIENTS - 1)
DisconnectSet == (NUM_REPLICAS+2*NUM_CLIENTS)..(NUM_REPLICAS+3*NUM_CLIENTS-1)
NullSet == (NUM_REPLICAS+3*NUM_CLIENTS)..(NUM_REPLICAS+4*NUM_CLIENTS-1)

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
      ReplicaSet == 0..(NUM_REPLICAS-1)
      ClientSet == NUM_REPLICAS..(NUM_NODES-1)
  }

  \* Broadcasts a certain `msg` to `nodes` with identifiers ranging from
  \* `domainStart` to `domainEnd`.
  \*
  \* Only returns once every message has been sent (i.e., it may "block" if
  \* the buffer of one of the receivers is full).
  macro Broadcast(nodes, i, until, msg) {
      while (i <= until) {
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

  \* The following mapping macros make sure that archetypes that
  \* perform client functions read the correct client identifier with
  \* respect to their PlusCal process identifier (`self`).

  mapping macro GetClientId {
      read  { yield self - (NUM_CLIENTS * GET_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro PutClientId {
      read  { yield self - (NUM_CLIENTS * PUT_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro DisconnectClientId {
      read  { yield self - (NUM_CLIENTS * DISCONNECT_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  mapping macro NullClientId {
      read  { yield self - (NUM_CLIENTS * NULL_ORDER); }
      write { assert(FALSE); yield $value; }
  }

  \* Mapping via identity is sometimes necessary in order to inform
  \* the compiler that a certain resource is to be function mapped, but
  \* no meaningful manipulation on reads and writes is necessary.
  mapping macro Identity {
      read  { yield $variable; }
      write { yield $value; }
  }

  mapping macro BlockingLock {
      read {
          await ~$variable;
          yield FALSE;
      }

      write {
          yield $value;
      }
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

            \* put requests were successful
            ok,

            \* holds keys/values to be read from/written to the database
            key,
            val; {

    \* Main replica loop. In each iteration of the loop, the replica:
    \*
    \*     1. Waits for incoming messages from clients;
    \*     2. Finds stable messages;
    \*     3. Replies to all stable messages.
    replicaLoop:
      while (TRUE) {

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

                      clients[msg.client] := [type |-> PUT_RESPONSE, result |-> ok];
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
  \* A Get message sent to the replica is a record in the following format:
  \*
  \*     [op: GET_MSG, key: key, client: client_id, timestamp: lamport_clock]
  archetype Get(clientId, ref replicas, clients, key, ref locked, ref clock, spin, ref outside)
  variable continue = TRUE, getReq, getResp;
  {
      \* Loop until disconnected
      getLoop:
        while (continue) {
            getRequest:
              \* only perform a get request if not locked (i.e., Put request underway)
              if (~locked[clientId]) {
                  \* if disconnected, return
                  if (clock[clientId] = -1) {
                      continue := FALSE
                  } else {
                      \* lock requests
                      locked[clientId] := TRUE;

                      \* increment the logical clock, and construct a valid
                      \* Get message.
                      clock[clientId] := clock[clientId] + 1;
                      getReq := [op |-> GET_MSG, key |-> key, client |-> clientId, timestamp |-> clock[clientId]];

                      \* Choose some replica from the set of replicas to send this
                      \* request to
                      with (dst \in ReplicaSet) {
                          replicas[dst] := getReq;
                      };

                      \* Waits for the response from the replica
                      getReply:
                        getResp := clients[clientId];
                        assert(getResp.type = GET_RESPONSE);
                        locked[clientId] := FALSE;
                        outside := getResp.result;
                  };
              };

              getCheckSpin:
                if (~spin) {
                    continue := FALSE;
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
  \* A Put message sent to the replica is a record in the following format:
  \*
  \*     [op: PUT_MSG, key: key, value: value, client: client_id, timestamp: lamport_clock]
  archetype Put(clientId, ref replicas, clients, key, value, ref locked, ref clock, spin, ref outside)
  variables continue = TRUE, i, j, putReq, putResp;
  {
      \* Loops indefinitely until disconnected
      putLoop:
        while (continue) {
            putRequest:
              \* only perform a get request if not locked (i.e., Get request underway)
              if (~locked[clientId]) {
                  \* if disconnected, return
                  if (clock[clientId] = -1) {
                      continue := FALSE;
                  } else {
                      \* increment the logical clock, construct the payload to be sent
                      \* to the replica, and set 'locked' to TRUE
                      clock[clientId] := clock[clientId] + 1;
                      putReq := [op |-> PUT_MSG, key |-> key, value |-> value, client |-> clientId, timestamp |-> clock[clientId]];
                      locked[clientId] := TRUE;
                      i := 0;
                      j := 0;

                      \* Put requests must be broadcast to all replicas
                      putBroadcast:
                        Broadcast(replicas, j, NUM_REPLICAS-1, putReq);

                      \* wait for a response from all replicas, and allow other
                      \* calls to the replica to happen after that.
                      putResponse:
                        while (i < Cardinality(ReplicaSet)) {
                            putResp := clients[clientId];
                            assert(putResp.type = PUT_RESPONSE);

                            i := i + 1;
                        };

                        locked[clientId] := FALSE;

                      putComplete:
                        outside := PUT_RESPONSE;
                  };
              };

              putCheckSpin:
                if (~spin) {
                    continue := FALSE;
                }
        }
  }

  \* Specifies a Disconnect message from the client.
  \* Does not disconnect if 'locked' (i.e., a Put request is underway).
  \*
  \* A Disconnect message sent to the replica is a record in the following format:
  \*
  \*     [op: DISCONNECT_MSG, client: client_id]
  archetype Disconnect(clientId, ref replicas, locked, ref clock)
  variables msg, j;
  {
      sendDisconnectRequest:
        if (~locked[clientId]) {
            msg := [op |-> DISCONNECT_MSG, client |-> clientId];

            \* setting the logical clock internally to -1 indicates that this client
            \* has disconnected. Other operations terminate accordingly.
            clock[clientId] := -1;
            j := 0;
        };

      \* Disconnection messages need to be broadcast to all replicas.
      disconnectBroadcast:
        Broadcast(replicas, j, NUM_REPLICAS-1, msg);
  }

  \* Specifies a ClockUpdate ('null') message from the client.
  \* If the client has disconnected, no more clock updates are sent.
  \*
  \* A ClockUpdate message sent to the replica is a record in the following format:
  \*
  \*     [op: NULL_MSG, client: client_id, timestamp: logical_clock]
  archetype ClockUpdate(clientId, ref replicas, ref clock, spin)
  variables continue = TRUE, j, msg;
  {
      clockUpdateLoop:
        while (continue) {
            \* if we have disconnected, return
            if (clock[clientId] = -1) {
                continue := FALSE;
            } else {
                \* tick the lock and construct the message accordingly
                clock[clientId] := clock[clientId] + 1;
                msg := [op |-> NULL_MSG, client |-> clientId, timestamp |-> clock[clientId]];
                j := 0;

                \* clock update messages must be broadcast to all replicas.
                nullBroadcast:
                  Broadcast(replicas, j, NUM_REPLICAS-1, msg);
            };

            nullCheckSpin:
              if (~spin) {
                  continue := FALSE;
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
            lock = [c \in ClientSet |-> FALSE],

            \* client identifier: to be appropriately mapped
            cid = 0,

            \* communication channel with the caller; astracted
            \* in this specification
            out = 0,

            \* all clocks set to 0 initially
            clocks = [c \in ClientSet |-> 0];


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

  fair process (GetClient \in GetSet) == instance Get(cid, ref replicasNetwork, clientsNetwork, GET_KEY, ref lock, ref clocks, TRUE, ref out)
      mapping cid via GetClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientsNetwork[_] via FIFOChannel
      mapping lock[_] via BlockingLock
      mapping clocks[_] via Identity;

  fair process (PutClient \in PutSet) == instance Put(cid, ref replicasNetwork, clientsNetwork, PUT_KEY, PUT_VALUE, ref lock, ref clocks, TRUE, ref out)
      mapping cid via PutClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientsNetwork[_] via FIFOChannel
      mapping lock[_] via BlockingLock
      mapping clocks[_] via Identity;

  fair process (DisconnectClient \in DisconnectSet) == instance Disconnect(cid, ref replicasNetwork, lock, ref clocks)
      mapping cid via DisconnectClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping lock[_] via BlockingLock
      mapping clocks[_] via Identity;

  fair process (ClockUpdateClient \in NullSet) == instance ClockUpdate(cid, ref replicasNetwork, ref clocks, TRUE)
      mapping cid via NullClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clocks[_] via Identity;
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm ReplicatedKV {
    variables replicasNetwork = [id \in ReplicaSet |-> <<>>], clientsNetwork = [id \in ClientSet |-> <<>>], lock = [c \in ClientSet |-> FALSE], cid = 0, out = 0, clocks = [c \in ClientSet |-> 0];
    define {
        NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
        ReplicaSet == (0) .. ((NUM_REPLICAS) - (1))
        ClientSet == (NUM_REPLICAS) .. ((NUM_NODES) - (1))
    }
    fair process (Replica \in ReplicaSet)
    variables kvLocal = [k \in KeySpace |-> NULL], liveClients = ClientSet, pendingRequests = [c \in liveClients |-> <<>>], stableMessages = <<>>, i, firstPending, timestamp, nextClient, lowestPending, chooseMessage, currentClocks = [c \in liveClients |-> 0], minClock, continue, pendingClients, clientsIter, msg, ok, key, val, replicasRead, replicasWrite, kvRead, clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1;
    {
        replicaLoop:
            if (TRUE) {
                stableMessages := <<>>;
                continue := TRUE;
                receiveClientRequest:
                    await (Len(replicasNetwork[self])) > (0);
                    with (msg0 = Head(replicasNetwork[self])) {
                        replicasWrite := [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])];
                        replicasRead := msg0;
                    };
                    msg := replicasRead;
                    replicasNetwork := replicasWrite;

                clientDisconnected:
                    if (((msg).op) = (DISCONNECT_MSG)) {
                        liveClients := (liveClients) \ ({(msg).client});
                    };

                replicaGetRequest:
                    if (((msg).op) = (GET_MSG)) {
                        assert ((msg).client) \in (liveClients);
                        currentClocks[(msg).client] := (msg).timestamp;
                        pendingRequests[(msg).client] := Append(pendingRequests[(msg).client], msg);
                    };

                replicaPutRequest:
                    if (((msg).op) = (PUT_MSG)) {
                        currentClocks[(msg).client] := (msg).timestamp;
                        pendingRequests[(msg).client] := Append(pendingRequests[(msg).client], msg);
                    };

                replicaNullRequest:
                    if (((msg).op) = (NULL_MSG)) {
                        currentClocks[(msg).client] := (msg).timestamp;
                    };

                findStableRequestsLoop:
                    if (continue) {
                        pendingClients := {c \in liveClients : (Len(pendingRequests[c])) > (0)};
                        nextClient := (NUM_NODES) + (1);
                        clientsIter := liveClients;
                        i := 0;
                        minClock := 0;
                        findMinClock:
                            if ((i) < (Cardinality(clientsIter))) {
                                with (client \in clientsIter) {
                                    if (((minClock) = (0)) \/ ((currentClocks[client]) < (minClock))) {
                                        minClock := currentClocks[client];
                                    };
                                    clientsIter := (clientsIter) \ ({client});
                                };
                                goto findMinClock;
                            } else {
                                lowestPending := (minClock) + (1);
                                i := 0;
                            };

                        findMinClient:
                            if ((i) < (Cardinality(pendingClients))) {
                                with (client \in pendingClients) {
                                    firstPending := Head(pendingRequests[client]);
                                    assert (((firstPending).op) = (GET_MSG)) \/ (((firstPending).op) = (PUT_MSG));
                                    timestamp := (firstPending).timestamp;
                                    if ((timestamp) < (minClock)) {
                                        chooseMessage := ((timestamp) < (lowestPending)) \/ (((timestamp) = (lowestPending)) /\ ((client) < (nextClient)));
                                        if (chooseMessage) {
                                            nextClient := client;
                                            lowestPending := timestamp;
                                        };
                                    };
                                    pendingClients := (pendingClients) \ ({client});
                                };
                                goto findMinClient;
                            };

                        addStableMessage:
                            if ((lowestPending) < (minClock)) {
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
                    if ((i) <= (Len(stableMessages))) {
                        msg := stableMessages[i];
                        i := (i) + (1);
                        respondStableGet:
                            if (((msg).op) = (GET_MSG)) {
                                key := (msg).key;
                                kvRead := kvLocal[key];
                                val := kvRead;
                                await (Len(clientsNetwork[(msg).client])) < (BUFFER_SIZE);
                                clientsWrite := [clientsNetwork EXCEPT ![(msg).client] = Append(clientsNetwork[(msg).client], [type |-> GET_RESPONSE, result |-> val])];
                                clientsWrite0 := clientsWrite;
                                clientsNetwork := clientsWrite0;
                            } else {
                                clientsWrite0 := clientsNetwork;
                                clientsNetwork := clientsWrite0;
                            };

                        respondStablePut:
                            if (((msg).op) = (PUT_MSG)) {
                                key := (msg).key;
                                val := (msg).value;
                                kvWrite := [kvLocal EXCEPT ![key] = val];
                                await (Len(clientsNetwork[(msg).client])) < (BUFFER_SIZE);
                                clientsWrite := [clientsNetwork EXCEPT ![(msg).client] = Append(clientsNetwork[(msg).client], [type |-> PUT_RESPONSE, result |-> ok])];
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
    variables spinLocal = TRUE, continue = TRUE, getReq, getResp, clientIdRead, lockedRead, clientIdRead0, clockRead, clientIdRead1, lockedWrite, clientIdRead2, clockRead0, clientIdRead3, clockWrite, keyRead, clientIdRead4, clientIdRead5, clockRead1, replicasWrite0, clientsRead, clientsWrite2, outsideWrite, lockedWrite0, clockWrite0, replicasWrite1, clientsWrite3, outsideWrite0, spinRead;
    {
        getLoop:
            if (continue) {
                getRequest:
                    clientIdRead := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                    await ~(lock[clientIdRead]);
                    lockedRead := FALSE;
                    if (~(lockedRead)) {
                        clientIdRead0 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                        clockRead := clocks[clientIdRead0];
                        if ((clockRead) = (-(1))) {
                            continue := FALSE;
                            lockedWrite0 := lock;
                            clockWrite0 := clocks;
                            replicasWrite1 := replicasNetwork;
                            clientsWrite3 := clientsNetwork;
                            outsideWrite0 := out;
                            replicasNetwork := replicasWrite1;
                            clientsNetwork := clientsWrite3;
                            lock := lockedWrite0;
                            clocks := clockWrite0;
                            out := outsideWrite0;
                        } else {
                            clientIdRead1 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            lockedWrite := [lock EXCEPT ![clientIdRead1] = TRUE];
                            clientIdRead2 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            clockRead0 := clocks[clientIdRead2];
                            clientIdRead3 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            clockWrite := [clocks EXCEPT ![clientIdRead3] = (clockRead0) + (1)];
                            keyRead := GET_KEY;
                            clientIdRead4 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            clientIdRead5 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                            clockRead1 := clockWrite[clientIdRead5];
                            getReq := [op |-> GET_MSG, key |-> keyRead, client |-> clientIdRead4, timestamp |-> clockRead1];
                            with (dst \in ReplicaSet) {
                                await (Len(replicasNetwork[dst])) < (BUFFER_SIZE);
                                replicasWrite0 := [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq)];
                            };
                            replicasNetwork := replicasWrite0;
                            lock := lockedWrite;
                            clocks := clockWrite;
                            getReply:
                                clientIdRead := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                                await (Len(clientsNetwork[clientIdRead])) > (0);
                                with (msg1 = Head(clientsNetwork[clientIdRead])) {
                                    clientsWrite2 := [clientsNetwork EXCEPT ![clientIdRead] = Tail(clientsNetwork[clientIdRead])];
                                    clientsRead := msg1;
                                };
                                getResp := clientsRead;
                                assert ((getResp).type) = (GET_RESPONSE);
                                clientIdRead0 := (self) - ((NUM_CLIENTS) * (GET_ORDER));
                                lockedWrite := [lock EXCEPT ![clientIdRead0] = FALSE];
                                outsideWrite := (getResp).result;
                                clientsNetwork := clientsWrite2;
                                lock := lockedWrite;
                                out := outsideWrite;

                        };
                    } else {
                        replicasNetwork := replicasWrite1;
                        clientsNetwork := clientsWrite3;
                        lock := lockedWrite0;
                        clocks := clockWrite0;
                        out := outsideWrite0;
                    };

                getCheckSpin:
                    spinRead := spinLocal;
                    if (~(spinRead)) {
                        continue := FALSE;
                        goto getLoop;
                    } else {
                        goto getLoop;
                    };

            };

    }
    fair process (PutClient \in PutSet)
    variables spinLocal0 = TRUE, continue = TRUE, i, j, putReq, putResp, clientIdRead6, lockedRead0, clientIdRead7, clockRead2, clientIdRead8, clockRead3, clientIdRead9, clockWrite1, keyRead0, valueRead, clientIdRead10, clientIdRead11, clockRead4, clientIdRead12, lockedWrite1, replicasWrite2, replicasWrite3, clientsRead0, clientsWrite4, clientsWrite5, lockedWrite2, outsideWrite1, spinRead0;
    {
        putLoop:
            if (continue) {
                putRequest:
                    clientIdRead6 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                    await ~(lock[clientIdRead6]);
                    lockedRead0 := FALSE;
                    if (~(lockedRead0)) {
                        clientIdRead7 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                        clockRead2 := clocks[clientIdRead7];
                        if ((clockRead2) = (-(1))) {
                            continue := FALSE;
                        } else {
                            clientIdRead8 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            clockRead3 := clocks[clientIdRead8];
                            clientIdRead9 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            clockWrite1 := [clocks EXCEPT ![clientIdRead9] = (clockRead3) + (1)];
                            keyRead0 := PUT_KEY;
                            valueRead := PUT_VALUE;
                            clientIdRead10 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            clientIdRead11 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            clockRead4 := clockWrite1[clientIdRead11];
                            putReq := [op |-> PUT_MSG, key |-> keyRead0, value |-> valueRead, client |-> clientIdRead10, timestamp |-> clockRead4];
                            clientIdRead12 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                            lockedWrite1 := [lock EXCEPT ![clientIdRead12] = TRUE];
                            i := 0;
                            j := 0;
                            lock := lockedWrite1;
                            clocks := clockWrite1;
                            putBroadcast:
                                if ((j) <= ((NUM_REPLICAS) - (1))) {
                                    await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                                    replicasWrite2 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], putReq)];
                                    j := (j) + (1);
                                    replicasWrite3 := replicasWrite2;
                                    replicasNetwork := replicasWrite3;
                                    goto putBroadcast;
                                } else {
                                    replicasWrite3 := replicasNetwork;
                                    replicasNetwork := replicasWrite3;
                                };

                            putResponse:
                                if ((i) < (Cardinality(ReplicaSet))) {
                                    clientIdRead6 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                                    await (Len(clientsNetwork[clientIdRead6])) > (0);
                                    with (msg2 = Head(clientsNetwork[clientIdRead6])) {
                                        clientsWrite4 := [clientsNetwork EXCEPT ![clientIdRead6] = Tail(clientsNetwork[clientIdRead6])];
                                        clientsRead0 := msg2;
                                    };
                                    putResp := clientsRead0;
                                    assert ((putResp).type) = (PUT_RESPONSE);
                                    i := (i) + (1);
                                    clientsWrite5 := clientsWrite4;
                                    lockedWrite2 := lock;
                                    clientsNetwork := clientsWrite5;
                                    lock := lockedWrite2;
                                    goto putResponse;
                                } else {
                                    clientIdRead7 := (self) - ((NUM_CLIENTS) * (PUT_ORDER));
                                    lockedWrite1 := [lock EXCEPT ![clientIdRead7] = FALSE];
                                    clientsWrite5 := clientsNetwork;
                                    lockedWrite2 := lockedWrite1;
                                    clientsNetwork := clientsWrite5;
                                    lock := lockedWrite2;
                                };

                            putComplete:
                                outsideWrite1 := PUT_RESPONSE;
                                out := outsideWrite1;

                        };
                    };

                putCheckSpin:
                    spinRead0 := spinLocal0;
                    if (~(spinRead0)) {
                        continue := FALSE;
                        goto putLoop;
                    } else {
                        goto putLoop;
                    };

            };

    }
    fair process (DisconnectClient \in DisconnectSet)
    variables msg, j, clientIdRead13, lockedRead1, clientIdRead14, clientIdRead15, clockWrite2, clockWrite3, replicasWrite4, replicasWrite5;
    {
        sendDisconnectRequest:
            clientIdRead13 := (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER));
            await ~(lock[clientIdRead13]);
            lockedRead1 := FALSE;
            if (~(lockedRead1)) {
                clientIdRead14 := (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER));
                msg := [op |-> DISCONNECT_MSG, client |-> clientIdRead14];
                clientIdRead15 := (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER));
                clockWrite2 := [clocks EXCEPT ![clientIdRead15] = -(1)];
                j := 0;
                clockWrite3 := clockWrite2;
                clocks := clockWrite3;
            } else {
                clockWrite3 := clocks;
                clocks := clockWrite3;
            };
        disconnectBroadcast:
            if ((j) <= ((NUM_REPLICAS) - (1))) {
                await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                replicasWrite4 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                j := (j) + (1);
                replicasWrite5 := replicasWrite4;
                replicasNetwork := replicasWrite5;
                goto disconnectBroadcast;
            } else {
                replicasWrite5 := replicasNetwork;
                replicasNetwork := replicasWrite5;
            };

    }
    fair process (ClockUpdateClient \in NullSet)
    variables spinLocal1 = TRUE, continue = TRUE, j, msg, clientIdRead16, clockRead5, clientIdRead17, clockRead6, clientIdRead18, clockWrite4, clientIdRead19, clientIdRead20, clockRead7, replicasWrite6, replicasWrite7, spinRead1;
    {
        clockUpdateLoop:
            if (continue) {
                clientIdRead16 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                clockRead5 := clocks[clientIdRead16];
                if ((clockRead5) = (-(1))) {
                    continue := FALSE;
                } else {
                    clientIdRead17 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockRead6 := clocks[clientIdRead17];
                    clientIdRead18 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockWrite4 := [clocks EXCEPT ![clientIdRead18] = (clockRead6) + (1)];
                    clientIdRead19 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clientIdRead20 := (self) - ((NUM_CLIENTS) * (NULL_ORDER));
                    clockRead7 := clockWrite4[clientIdRead20];
                    msg := [op |-> NULL_MSG, client |-> clientIdRead19, timestamp |-> clockRead7];
                    j := 0;
                    clocks := clockWrite4;
                    nullBroadcast:
                        if ((j) <= ((NUM_REPLICAS) - (1))) {
                            await (Len(replicasNetwork[j])) < (BUFFER_SIZE);
                            replicasWrite6 := [replicasNetwork EXCEPT ![j] = Append(replicasNetwork[j], msg)];
                            j := (j) + (1);
                            replicasWrite7 := replicasWrite6;
                            replicasNetwork := replicasWrite7;
                            goto nullBroadcast;
                        } else {
                            replicasWrite7 := replicasNetwork;
                            replicasNetwork := replicasWrite7;
                        };

                };
                nullCheckSpin:
                    spinRead1 := spinLocal1;
                    if (~(spinRead1)) {
                        continue := FALSE;
                        goto clockUpdateLoop;
                    } else {
                        goto clockUpdateLoop;
                    };

            };

    }
}
\* END PLUSCAL TRANSLATION


***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable i of process Replica at line 679 col 148 changed to i_
\* Process variable continue of process Replica at line 679 col 271 changed to continue_
\* Process variable msg of process Replica at line 679 col 310 changed to msg_
\* Process variable continue of process GetClient at line 817 col 33 changed to continue_G
\* Process variable continue of process PutClient at line 897 col 34 changed to continue_P
\* Process variable j of process PutClient at line 897 col 54 changed to j_
\* Process variable msg of process DisconnectClient at line 985 col 15 changed to msg_D
\* Process variable j of process DisconnectClient at line 985 col 20 changed to j_D
CONSTANT defaultInitValue
VARIABLES replicasNetwork, clientsNetwork, lock, cid, out, clocks, pc

(* define statement *)
NUM_NODES == (NUM_REPLICAS) + (NUM_CLIENTS)
ReplicaSet == (0) .. ((NUM_REPLICAS) - (1))
ClientSet == (NUM_REPLICAS) .. ((NUM_NODES) - (1))

VARIABLES kvLocal, liveClients, pendingRequests, stableMessages, i_,
          firstPending, timestamp, nextClient, lowestPending, chooseMessage,
          currentClocks, minClock, continue_, pendingClients, clientsIter,
          msg_, ok, key, val, replicasRead, replicasWrite, kvRead,
          clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1,
          spinLocal, continue_G, getReq, getResp, clientIdRead, lockedRead,
          clientIdRead0, clockRead, clientIdRead1, lockedWrite, clientIdRead2,
          clockRead0, clientIdRead3, clockWrite, keyRead, clientIdRead4,
          clientIdRead5, clockRead1, replicasWrite0, clientsRead,
          clientsWrite2, outsideWrite, lockedWrite0, clockWrite0,
          replicasWrite1, clientsWrite3, outsideWrite0, spinRead, spinLocal0,
          continue_P, i, j_, putReq, putResp, clientIdRead6, lockedRead0,
          clientIdRead7, clockRead2, clientIdRead8, clockRead3, clientIdRead9,
          clockWrite1, keyRead0, valueRead, clientIdRead10, clientIdRead11,
          clockRead4, clientIdRead12, lockedWrite1, replicasWrite2,
          replicasWrite3, clientsRead0, clientsWrite4, clientsWrite5,
          lockedWrite2, outsideWrite1, spinRead0, msg_D, j_D, clientIdRead13,
          lockedRead1, clientIdRead14, clientIdRead15, clockWrite2,
          clockWrite3, replicasWrite4, replicasWrite5, spinLocal1, continue,
          j, msg, clientIdRead16, clockRead5, clientIdRead17, clockRead6,
          clientIdRead18, clockWrite4, clientIdRead19, clientIdRead20,
          clockRead7, replicasWrite6, replicasWrite7, spinRead1

vars == << replicasNetwork, clientsNetwork, lock, cid, out, clocks, pc,
           kvLocal, liveClients, pendingRequests, stableMessages, i_,
           firstPending, timestamp, nextClient, lowestPending, chooseMessage,
           currentClocks, minClock, continue_, pendingClients, clientsIter,
           msg_, ok, key, val, replicasRead, replicasWrite, kvRead,
           clientsWrite, clientsWrite0, kvWrite, kvWrite0, clientsWrite1,
           spinLocal, continue_G, getReq, getResp, clientIdRead, lockedRead,
           clientIdRead0, clockRead, clientIdRead1, lockedWrite,
           clientIdRead2, clockRead0, clientIdRead3, clockWrite, keyRead,
           clientIdRead4, clientIdRead5, clockRead1, replicasWrite0,
           clientsRead, clientsWrite2, outsideWrite, lockedWrite0,
           clockWrite0, replicasWrite1, clientsWrite3, outsideWrite0,
           spinRead, spinLocal0, continue_P, i, j_, putReq, putResp,
           clientIdRead6, lockedRead0, clientIdRead7, clockRead2,
           clientIdRead8, clockRead3, clientIdRead9, clockWrite1, keyRead0,
           valueRead, clientIdRead10, clientIdRead11, clockRead4,
           clientIdRead12, lockedWrite1, replicasWrite2, replicasWrite3,
           clientsRead0, clientsWrite4, clientsWrite5, lockedWrite2,
           outsideWrite1, spinRead0, msg_D, j_D, clientIdRead13, lockedRead1,
           clientIdRead14, clientIdRead15, clockWrite2, clockWrite3,
           replicasWrite4, replicasWrite5, spinLocal1, continue, j, msg,
           clientIdRead16, clockRead5, clientIdRead17, clockRead6,
           clientIdRead18, clockWrite4, clientIdRead19, clientIdRead20,
           clockRead7, replicasWrite6, replicasWrite7, spinRead1 >>

ProcSet == (ReplicaSet) \cup (GetSet) \cup (PutSet) \cup (DisconnectSet) \cup (NullSet)

Init == (* Global variables *)
        /\ replicasNetwork = [id \in ReplicaSet |-> <<>>]
        /\ clientsNetwork = [id \in ClientSet |-> <<>>]
        /\ lock = [c \in ClientSet |-> FALSE]
        /\ cid = 0
        /\ out = 0
        /\ clocks = [c \in ClientSet |-> 0]
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
        /\ ok = [self \in ReplicaSet |-> defaultInitValue]
        /\ key = [self \in ReplicaSet |-> defaultInitValue]
        /\ val = [self \in ReplicaSet |-> defaultInitValue]
        /\ replicasRead = [self \in ReplicaSet |-> defaultInitValue]
        /\ replicasWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvRead = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite0 = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvWrite = [self \in ReplicaSet |-> defaultInitValue]
        /\ kvWrite0 = [self \in ReplicaSet |-> defaultInitValue]
        /\ clientsWrite1 = [self \in ReplicaSet |-> defaultInitValue]
        (* Process GetClient *)
        /\ spinLocal = [self \in GetSet |-> TRUE]
        /\ continue_G = [self \in GetSet |-> TRUE]
        /\ getReq = [self \in GetSet |-> defaultInitValue]
        /\ getResp = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead = [self \in GetSet |-> defaultInitValue]
        /\ lockedRead = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead0 = [self \in GetSet |-> defaultInitValue]
        /\ clockRead = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead1 = [self \in GetSet |-> defaultInitValue]
        /\ lockedWrite = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead2 = [self \in GetSet |-> defaultInitValue]
        /\ clockRead0 = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead3 = [self \in GetSet |-> defaultInitValue]
        /\ clockWrite = [self \in GetSet |-> defaultInitValue]
        /\ keyRead = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead4 = [self \in GetSet |-> defaultInitValue]
        /\ clientIdRead5 = [self \in GetSet |-> defaultInitValue]
        /\ clockRead1 = [self \in GetSet |-> defaultInitValue]
        /\ replicasWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ clientsRead = [self \in GetSet |-> defaultInitValue]
        /\ clientsWrite2 = [self \in GetSet |-> defaultInitValue]
        /\ outsideWrite = [self \in GetSet |-> defaultInitValue]
        /\ lockedWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ clockWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ replicasWrite1 = [self \in GetSet |-> defaultInitValue]
        /\ clientsWrite3 = [self \in GetSet |-> defaultInitValue]
        /\ outsideWrite0 = [self \in GetSet |-> defaultInitValue]
        /\ spinRead = [self \in GetSet |-> defaultInitValue]
        (* Process PutClient *)
        /\ spinLocal0 = [self \in PutSet |-> TRUE]
        /\ continue_P = [self \in PutSet |-> TRUE]
        /\ i = [self \in PutSet |-> defaultInitValue]
        /\ j_ = [self \in PutSet |-> defaultInitValue]
        /\ putReq = [self \in PutSet |-> defaultInitValue]
        /\ putResp = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead6 = [self \in PutSet |-> defaultInitValue]
        /\ lockedRead0 = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead7 = [self \in PutSet |-> defaultInitValue]
        /\ clockRead2 = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead8 = [self \in PutSet |-> defaultInitValue]
        /\ clockRead3 = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead9 = [self \in PutSet |-> defaultInitValue]
        /\ clockWrite1 = [self \in PutSet |-> defaultInitValue]
        /\ keyRead0 = [self \in PutSet |-> defaultInitValue]
        /\ valueRead = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead10 = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead11 = [self \in PutSet |-> defaultInitValue]
        /\ clockRead4 = [self \in PutSet |-> defaultInitValue]
        /\ clientIdRead12 = [self \in PutSet |-> defaultInitValue]
        /\ lockedWrite1 = [self \in PutSet |-> defaultInitValue]
        /\ replicasWrite2 = [self \in PutSet |-> defaultInitValue]
        /\ replicasWrite3 = [self \in PutSet |-> defaultInitValue]
        /\ clientsRead0 = [self \in PutSet |-> defaultInitValue]
        /\ clientsWrite4 = [self \in PutSet |-> defaultInitValue]
        /\ clientsWrite5 = [self \in PutSet |-> defaultInitValue]
        /\ lockedWrite2 = [self \in PutSet |-> defaultInitValue]
        /\ outsideWrite1 = [self \in PutSet |-> defaultInitValue]
        /\ spinRead0 = [self \in PutSet |-> defaultInitValue]
        (* Process DisconnectClient *)
        /\ msg_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ j_D = [self \in DisconnectSet |-> defaultInitValue]
        /\ clientIdRead13 = [self \in DisconnectSet |-> defaultInitValue]
        /\ lockedRead1 = [self \in DisconnectSet |-> defaultInitValue]
        /\ clientIdRead14 = [self \in DisconnectSet |-> defaultInitValue]
        /\ clientIdRead15 = [self \in DisconnectSet |-> defaultInitValue]
        /\ clockWrite2 = [self \in DisconnectSet |-> defaultInitValue]
        /\ clockWrite3 = [self \in DisconnectSet |-> defaultInitValue]
        /\ replicasWrite4 = [self \in DisconnectSet |-> defaultInitValue]
        /\ replicasWrite5 = [self \in DisconnectSet |-> defaultInitValue]
        (* Process ClockUpdateClient *)
        /\ spinLocal1 = [self \in NullSet |-> TRUE]
        /\ continue = [self \in NullSet |-> TRUE]
        /\ j = [self \in NullSet |-> defaultInitValue]
        /\ msg = [self \in NullSet |-> defaultInitValue]
        /\ clientIdRead16 = [self \in NullSet |-> defaultInitValue]
        /\ clockRead5 = [self \in NullSet |-> defaultInitValue]
        /\ clientIdRead17 = [self \in NullSet |-> defaultInitValue]
        /\ clockRead6 = [self \in NullSet |-> defaultInitValue]
        /\ clientIdRead18 = [self \in NullSet |-> defaultInitValue]
        /\ clockWrite4 = [self \in NullSet |-> defaultInitValue]
        /\ clientIdRead19 = [self \in NullSet |-> defaultInitValue]
        /\ clientIdRead20 = [self \in NullSet |-> defaultInitValue]
        /\ clockRead7 = [self \in NullSet |-> defaultInitValue]
        /\ replicasWrite6 = [self \in NullSet |-> defaultInitValue]
        /\ replicasWrite7 = [self \in NullSet |-> defaultInitValue]
        /\ spinRead1 = [self \in NullSet |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in ReplicaSet -> "replicaLoop"
                                        [] self \in GetSet -> "getLoop"
                                        [] self \in PutSet -> "putLoop"
                                        [] self \in DisconnectSet -> "sendDisconnectRequest"
                                        [] self \in NullSet -> "clockUpdateLoop"]

replicaLoop(self) == /\ pc[self] = "replicaLoop"
                     /\ IF TRUE
                           THEN /\ stableMessages' = [stableMessages EXCEPT ![self] = <<>>]
                                /\ continue_' = [continue_ EXCEPT ![self] = TRUE]
                                /\ pc' = [pc EXCEPT ![self] = "receiveClientRequest"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << stableMessages, continue_ >>
                     /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                     cid, out, clocks, kvLocal, liveClients,
                                     pendingRequests, i_, firstPending,
                                     timestamp, nextClient, lowestPending,
                                     chooseMessage, currentClocks, minClock,
                                     pendingClients, clientsIter, msg_, ok,
                                     key, val, replicasRead, replicasWrite,
                                     kvRead, clientsWrite, clientsWrite0,
                                     kvWrite, kvWrite0, clientsWrite1,
                                     spinLocal, continue_G, getReq, getResp,
                                     clientIdRead, lockedRead, clientIdRead0,
                                     clockRead, clientIdRead1, lockedWrite,
                                     clientIdRead2, clockRead0, clientIdRead3,
                                     clockWrite, keyRead, clientIdRead4,
                                     clientIdRead5, clockRead1, replicasWrite0,
                                     clientsRead, clientsWrite2, outsideWrite,
                                     lockedWrite0, clockWrite0, replicasWrite1,
                                     clientsWrite3, outsideWrite0, spinRead,
                                     spinLocal0, continue_P, i, j_, putReq,
                                     putResp, clientIdRead6, lockedRead0,
                                     clientIdRead7, clockRead2, clientIdRead8,
                                     clockRead3, clientIdRead9, clockWrite1,
                                     keyRead0, valueRead, clientIdRead10,
                                     clientIdRead11, clockRead4,
                                     clientIdRead12, lockedWrite1,
                                     replicasWrite2, replicasWrite3,
                                     clientsRead0, clientsWrite4,
                                     clientsWrite5, lockedWrite2,
                                     outsideWrite1, spinRead0, msg_D, j_D,
                                     clientIdRead13, lockedRead1,
                                     clientIdRead14, clientIdRead15,
                                     clockWrite2, clockWrite3, replicasWrite4,
                                     replicasWrite5, spinLocal1, continue, j,
                                     msg, clientIdRead16, clockRead5,
                                     clientIdRead17, clockRead6,
                                     clientIdRead18, clockWrite4,
                                     clientIdRead19, clientIdRead20,
                                     clockRead7, replicasWrite6,
                                     replicasWrite7, spinRead1 >>

receiveClientRequest(self) == /\ pc[self] = "receiveClientRequest"
                              /\ (Len(replicasNetwork[self])) > (0)
                              /\ LET msg0 == Head(replicasNetwork[self]) IN
                                   /\ replicasWrite' = [replicasWrite EXCEPT ![self] = [replicasNetwork EXCEPT ![self] = Tail(replicasNetwork[self])]]
                                   /\ replicasRead' = [replicasRead EXCEPT ![self] = msg0]
                              /\ msg_' = [msg_ EXCEPT ![self] = replicasRead'[self]]
                              /\ replicasNetwork' = replicasWrite'[self]
                              /\ pc' = [pc EXCEPT ![self] = "clientDisconnected"]
                              /\ UNCHANGED << clientsNetwork, lock, cid, out,
                                              clocks, kvLocal, liveClients,
                                              pendingRequests, stableMessages,
                                              i_, firstPending, timestamp,
                                              nextClient, lowestPending,
                                              chooseMessage, currentClocks,
                                              minClock, continue_,
                                              pendingClients, clientsIter, ok,
                                              key, val, kvRead, clientsWrite,
                                              clientsWrite0, kvWrite, kvWrite0,
                                              clientsWrite1, spinLocal,
                                              continue_G, getReq, getResp,
                                              clientIdRead, lockedRead,
                                              clientIdRead0, clockRead,
                                              clientIdRead1, lockedWrite,
                                              clientIdRead2, clockRead0,
                                              clientIdRead3, clockWrite,
                                              keyRead, clientIdRead4,
                                              clientIdRead5, clockRead1,
                                              replicasWrite0, clientsRead,
                                              clientsWrite2, outsideWrite,
                                              lockedWrite0, clockWrite0,
                                              replicasWrite1, clientsWrite3,
                                              outsideWrite0, spinRead,
                                              spinLocal0, continue_P, i, j_,
                                              putReq, putResp, clientIdRead6,
                                              lockedRead0, clientIdRead7,
                                              clockRead2, clientIdRead8,
                                              clockRead3, clientIdRead9,
                                              clockWrite1, keyRead0, valueRead,
                                              clientIdRead10, clientIdRead11,
                                              clockRead4, clientIdRead12,
                                              lockedWrite1, replicasWrite2,
                                              replicasWrite3, clientsRead0,
                                              clientsWrite4, clientsWrite5,
                                              lockedWrite2, outsideWrite1,
                                              spinRead0, msg_D, j_D,
                                              clientIdRead13, lockedRead1,
                                              clientIdRead14, clientIdRead15,
                                              clockWrite2, clockWrite3,
                                              replicasWrite4, replicasWrite5,
                                              spinLocal1, continue, j, msg,
                                              clientIdRead16, clockRead5,
                                              clientIdRead17, clockRead6,
                                              clientIdRead18, clockWrite4,
                                              clientIdRead19, clientIdRead20,
                                              clockRead7, replicasWrite6,
                                              replicasWrite7, spinRead1 >>

clientDisconnected(self) == /\ pc[self] = "clientDisconnected"
                            /\ IF ((msg_[self]).op) = (DISCONNECT_MSG)
                                  THEN /\ liveClients' = [liveClients EXCEPT ![self] = (liveClients[self]) \ ({(msg_[self]).client})]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED liveClients
                            /\ pc' = [pc EXCEPT ![self] = "replicaGetRequest"]
                            /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                            lock, cid, out, clocks, kvLocal,
                                            pendingRequests, stableMessages,
                                            i_, firstPending, timestamp,
                                            nextClient, lowestPending,
                                            chooseMessage, currentClocks,
                                            minClock, continue_,
                                            pendingClients, clientsIter, msg_,
                                            ok, key, val, replicasRead,
                                            replicasWrite, kvRead,
                                            clientsWrite, clientsWrite0,
                                            kvWrite, kvWrite0, clientsWrite1,
                                            spinLocal, continue_G, getReq,
                                            getResp, clientIdRead, lockedRead,
                                            clientIdRead0, clockRead,
                                            clientIdRead1, lockedWrite,
                                            clientIdRead2, clockRead0,
                                            clientIdRead3, clockWrite, keyRead,
                                            clientIdRead4, clientIdRead5,
                                            clockRead1, replicasWrite0,
                                            clientsRead, clientsWrite2,
                                            outsideWrite, lockedWrite0,
                                            clockWrite0, replicasWrite1,
                                            clientsWrite3, outsideWrite0,
                                            spinRead, spinLocal0, continue_P,
                                            i, j_, putReq, putResp,
                                            clientIdRead6, lockedRead0,
                                            clientIdRead7, clockRead2,
                                            clientIdRead8, clockRead3,
                                            clientIdRead9, clockWrite1,
                                            keyRead0, valueRead,
                                            clientIdRead10, clientIdRead11,
                                            clockRead4, clientIdRead12,
                                            lockedWrite1, replicasWrite2,
                                            replicasWrite3, clientsRead0,
                                            clientsWrite4, clientsWrite5,
                                            lockedWrite2, outsideWrite1,
                                            spinRead0, msg_D, j_D,
                                            clientIdRead13, lockedRead1,
                                            clientIdRead14, clientIdRead15,
                                            clockWrite2, clockWrite3,
                                            replicasWrite4, replicasWrite5,
                                            spinLocal1, continue, j, msg,
                                            clientIdRead16, clockRead5,
                                            clientIdRead17, clockRead6,
                                            clientIdRead18, clockWrite4,
                                            clientIdRead19, clientIdRead20,
                                            clockRead7, replicasWrite6,
                                            replicasWrite7, spinRead1 >>

replicaGetRequest(self) == /\ pc[self] = "replicaGetRequest"
                           /\ IF ((msg_[self]).op) = (GET_MSG)
                                 THEN /\ Assert(((msg_[self]).client) \in (liveClients[self]),
                                                "Failure of assertion at line 701, column 25.")
                                      /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][(msg_[self]).client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests,
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaPutRequest"]
                           /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                           lock, cid, out, clocks, kvLocal,
                                           liveClients, stableMessages, i_,
                                           firstPending, timestamp, nextClient,
                                           lowestPending, chooseMessage,
                                           minClock, continue_, pendingClients,
                                           clientsIter, msg_, ok, key, val,
                                           replicasRead, replicasWrite, kvRead,
                                           clientsWrite, clientsWrite0,
                                           kvWrite, kvWrite0, clientsWrite1,
                                           spinLocal, continue_G, getReq,
                                           getResp, clientIdRead, lockedRead,
                                           clientIdRead0, clockRead,
                                           clientIdRead1, lockedWrite,
                                           clientIdRead2, clockRead0,
                                           clientIdRead3, clockWrite, keyRead,
                                           clientIdRead4, clientIdRead5,
                                           clockRead1, replicasWrite0,
                                           clientsRead, clientsWrite2,
                                           outsideWrite, lockedWrite0,
                                           clockWrite0, replicasWrite1,
                                           clientsWrite3, outsideWrite0,
                                           spinRead, spinLocal0, continue_P, i,
                                           j_, putReq, putResp, clientIdRead6,
                                           lockedRead0, clientIdRead7,
                                           clockRead2, clientIdRead8,
                                           clockRead3, clientIdRead9,
                                           clockWrite1, keyRead0, valueRead,
                                           clientIdRead10, clientIdRead11,
                                           clockRead4, clientIdRead12,
                                           lockedWrite1, replicasWrite2,
                                           replicasWrite3, clientsRead0,
                                           clientsWrite4, clientsWrite5,
                                           lockedWrite2, outsideWrite1,
                                           spinRead0, msg_D, j_D,
                                           clientIdRead13, lockedRead1,
                                           clientIdRead14, clientIdRead15,
                                           clockWrite2, clockWrite3,
                                           replicasWrite4, replicasWrite5,
                                           spinLocal1, continue, j, msg,
                                           clientIdRead16, clockRead5,
                                           clientIdRead17, clockRead6,
                                           clientIdRead18, clockWrite4,
                                           clientIdRead19, clientIdRead20,
                                           clockRead7, replicasWrite6,
                                           replicasWrite7, spinRead1 >>

replicaPutRequest(self) == /\ pc[self] = "replicaPutRequest"
                           /\ IF ((msg_[self]).op) = (PUT_MSG)
                                 THEN /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                      /\ pendingRequests' = [pendingRequests EXCEPT ![self][(msg_[self]).client] = Append(pendingRequests[self][(msg_[self]).client], msg_[self])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << pendingRequests,
                                                      currentClocks >>
                           /\ pc' = [pc EXCEPT ![self] = "replicaNullRequest"]
                           /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                           lock, cid, out, clocks, kvLocal,
                                           liveClients, stableMessages, i_,
                                           firstPending, timestamp, nextClient,
                                           lowestPending, chooseMessage,
                                           minClock, continue_, pendingClients,
                                           clientsIter, msg_, ok, key, val,
                                           replicasRead, replicasWrite, kvRead,
                                           clientsWrite, clientsWrite0,
                                           kvWrite, kvWrite0, clientsWrite1,
                                           spinLocal, continue_G, getReq,
                                           getResp, clientIdRead, lockedRead,
                                           clientIdRead0, clockRead,
                                           clientIdRead1, lockedWrite,
                                           clientIdRead2, clockRead0,
                                           clientIdRead3, clockWrite, keyRead,
                                           clientIdRead4, clientIdRead5,
                                           clockRead1, replicasWrite0,
                                           clientsRead, clientsWrite2,
                                           outsideWrite, lockedWrite0,
                                           clockWrite0, replicasWrite1,
                                           clientsWrite3, outsideWrite0,
                                           spinRead, spinLocal0, continue_P, i,
                                           j_, putReq, putResp, clientIdRead6,
                                           lockedRead0, clientIdRead7,
                                           clockRead2, clientIdRead8,
                                           clockRead3, clientIdRead9,
                                           clockWrite1, keyRead0, valueRead,
                                           clientIdRead10, clientIdRead11,
                                           clockRead4, clientIdRead12,
                                           lockedWrite1, replicasWrite2,
                                           replicasWrite3, clientsRead0,
                                           clientsWrite4, clientsWrite5,
                                           lockedWrite2, outsideWrite1,
                                           spinRead0, msg_D, j_D,
                                           clientIdRead13, lockedRead1,
                                           clientIdRead14, clientIdRead15,
                                           clockWrite2, clockWrite3,
                                           replicasWrite4, replicasWrite5,
                                           spinLocal1, continue, j, msg,
                                           clientIdRead16, clockRead5,
                                           clientIdRead17, clockRead6,
                                           clientIdRead18, clockWrite4,
                                           clientIdRead19, clientIdRead20,
                                           clockRead7, replicasWrite6,
                                           replicasWrite7, spinRead1 >>

replicaNullRequest(self) == /\ pc[self] = "replicaNullRequest"
                            /\ IF ((msg_[self]).op) = (NULL_MSG)
                                  THEN /\ currentClocks' = [currentClocks EXCEPT ![self][(msg_[self]).client] = (msg_[self]).timestamp]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED currentClocks
                            /\ pc' = [pc EXCEPT ![self] = "findStableRequestsLoop"]
                            /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                            lock, cid, out, clocks, kvLocal,
                                            liveClients, pendingRequests,
                                            stableMessages, i_, firstPending,
                                            timestamp, nextClient,
                                            lowestPending, chooseMessage,
                                            minClock, continue_,
                                            pendingClients, clientsIter, msg_,
                                            ok, key, val, replicasRead,
                                            replicasWrite, kvRead,
                                            clientsWrite, clientsWrite0,
                                            kvWrite, kvWrite0, clientsWrite1,
                                            spinLocal, continue_G, getReq,
                                            getResp, clientIdRead, lockedRead,
                                            clientIdRead0, clockRead,
                                            clientIdRead1, lockedWrite,
                                            clientIdRead2, clockRead0,
                                            clientIdRead3, clockWrite, keyRead,
                                            clientIdRead4, clientIdRead5,
                                            clockRead1, replicasWrite0,
                                            clientsRead, clientsWrite2,
                                            outsideWrite, lockedWrite0,
                                            clockWrite0, replicasWrite1,
                                            clientsWrite3, outsideWrite0,
                                            spinRead, spinLocal0, continue_P,
                                            i, j_, putReq, putResp,
                                            clientIdRead6, lockedRead0,
                                            clientIdRead7, clockRead2,
                                            clientIdRead8, clockRead3,
                                            clientIdRead9, clockWrite1,
                                            keyRead0, valueRead,
                                            clientIdRead10, clientIdRead11,
                                            clockRead4, clientIdRead12,
                                            lockedWrite1, replicasWrite2,
                                            replicasWrite3, clientsRead0,
                                            clientsWrite4, clientsWrite5,
                                            lockedWrite2, outsideWrite1,
                                            spinRead0, msg_D, j_D,
                                            clientIdRead13, lockedRead1,
                                            clientIdRead14, clientIdRead15,
                                            clockWrite2, clockWrite3,
                                            replicasWrite4, replicasWrite5,
                                            spinLocal1, continue, j, msg,
                                            clientIdRead16, clockRead5,
                                            clientIdRead17, clockRead6,
                                            clientIdRead18, clockWrite4,
                                            clientIdRead19, clientIdRead20,
                                            clockRead7, replicasWrite6,
                                            replicasWrite7, spinRead1 >>

findStableRequestsLoop(self) == /\ pc[self] = "findStableRequestsLoop"
                                /\ IF continue_[self]
                                      THEN /\ pendingClients' = [pendingClients EXCEPT ![self] = {c \in liveClients[self] : (Len(pendingRequests[self][c])) > (0)}]
                                           /\ nextClient' = [nextClient EXCEPT ![self] = (NUM_NODES) + (1)]
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
                                                clientsNetwork, lock, cid, out,
                                                clocks, kvLocal, liveClients,
                                                pendingRequests,
                                                stableMessages, firstPending,
                                                timestamp, lowestPending,
                                                chooseMessage, currentClocks,
                                                continue_, msg_, ok, key, val,
                                                replicasRead, replicasWrite,
                                                kvRead, clientsWrite,
                                                clientsWrite0, kvWrite,
                                                kvWrite0, clientsWrite1,
                                                spinLocal, continue_G, getReq,
                                                getResp, clientIdRead,
                                                lockedRead, clientIdRead0,
                                                clockRead, clientIdRead1,
                                                lockedWrite, clientIdRead2,
                                                clockRead0, clientIdRead3,
                                                clockWrite, keyRead,
                                                clientIdRead4, clientIdRead5,
                                                clockRead1, replicasWrite0,
                                                clientsRead, clientsWrite2,
                                                outsideWrite, lockedWrite0,
                                                clockWrite0, replicasWrite1,
                                                clientsWrite3, outsideWrite0,
                                                spinRead, spinLocal0,
                                                continue_P, i, j_, putReq,
                                                putResp, clientIdRead6,
                                                lockedRead0, clientIdRead7,
                                                clockRead2, clientIdRead8,
                                                clockRead3, clientIdRead9,
                                                clockWrite1, keyRead0,
                                                valueRead, clientIdRead10,
                                                clientIdRead11, clockRead4,
                                                clientIdRead12, lockedWrite1,
                                                replicasWrite2, replicasWrite3,
                                                clientsRead0, clientsWrite4,
                                                clientsWrite5, lockedWrite2,
                                                outsideWrite1, spinRead0,
                                                msg_D, j_D, clientIdRead13,
                                                lockedRead1, clientIdRead14,
                                                clientIdRead15, clockWrite2,
                                                clockWrite3, replicasWrite4,
                                                replicasWrite5, spinLocal1,
                                                continue, j, msg,
                                                clientIdRead16, clockRead5,
                                                clientIdRead17, clockRead6,
                                                clientIdRead18, clockWrite4,
                                                clientIdRead19, clientIdRead20,
                                                clockRead7, replicasWrite6,
                                                replicasWrite7, spinRead1 >>

findMinClock(self) == /\ pc[self] = "findMinClock"
                      /\ IF (i_[self]) < (Cardinality(clientsIter[self]))
                            THEN /\ \E client \in clientsIter[self]:
                                      /\ IF ((minClock[self]) = (0)) \/ ((currentClocks[self][client]) < (minClock[self]))
                                            THEN /\ minClock' = [minClock EXCEPT ![self] = currentClocks[self][client]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED minClock
                                      /\ clientsIter' = [clientsIter EXCEPT ![self] = (clientsIter[self]) \ ({client})]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClock"]
                                 /\ UNCHANGED << i_, lowestPending >>
                            ELSE /\ lowestPending' = [lowestPending EXCEPT ![self] = (minClock[self]) + (1)]
                                 /\ i_' = [i_ EXCEPT ![self] = 0]
                                 /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                                 /\ UNCHANGED << minClock, clientsIter >>
                      /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                      cid, out, clocks, kvLocal, liveClients,
                                      pendingRequests, stableMessages,
                                      firstPending, timestamp, nextClient,
                                      chooseMessage, currentClocks, continue_,
                                      pendingClients, msg_, ok, key, val,
                                      replicasRead, replicasWrite, kvRead,
                                      clientsWrite, clientsWrite0, kvWrite,
                                      kvWrite0, clientsWrite1, spinLocal,
                                      continue_G, getReq, getResp,
                                      clientIdRead, lockedRead, clientIdRead0,
                                      clockRead, clientIdRead1, lockedWrite,
                                      clientIdRead2, clockRead0, clientIdRead3,
                                      clockWrite, keyRead, clientIdRead4,
                                      clientIdRead5, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, outsideWrite,
                                      lockedWrite0, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      outsideWrite0, spinRead, spinLocal0,
                                      continue_P, i, j_, putReq, putResp,
                                      clientIdRead6, lockedRead0,
                                      clientIdRead7, clockRead2, clientIdRead8,
                                      clockRead3, clientIdRead9, clockWrite1,
                                      keyRead0, valueRead, clientIdRead10,
                                      clientIdRead11, clockRead4,
                                      clientIdRead12, lockedWrite1,
                                      replicasWrite2, replicasWrite3,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite2,
                                      outsideWrite1, spinRead0, msg_D, j_D,
                                      clientIdRead13, lockedRead1,
                                      clientIdRead14, clientIdRead15,
                                      clockWrite2, clockWrite3, replicasWrite4,
                                      replicasWrite5, spinLocal1, continue, j,
                                      msg, clientIdRead16, clockRead5,
                                      clientIdRead17, clockRead6,
                                      clientIdRead18, clockWrite4,
                                      clientIdRead19, clientIdRead20,
                                      clockRead7, replicasWrite6,
                                      replicasWrite7, spinRead1 >>

findMinClient(self) == /\ pc[self] = "findMinClient"
                       /\ IF (i_[self]) < (Cardinality(pendingClients[self]))
                             THEN /\ \E client \in pendingClients[self]:
                                       /\ firstPending' = [firstPending EXCEPT ![self] = Head(pendingRequests[self][client])]
                                       /\ Assert((((firstPending'[self]).op) = (GET_MSG)) \/ (((firstPending'[self]).op) = (PUT_MSG)),
                                                 "Failure of assertion at line 742, column 37.")
                                       /\ timestamp' = [timestamp EXCEPT ![self] = (firstPending'[self]).timestamp]
                                       /\ IF (timestamp'[self]) < (minClock[self])
                                             THEN /\ chooseMessage' = [chooseMessage EXCEPT ![self] = ((timestamp'[self]) < (lowestPending[self])) \/ (((timestamp'[self]) = (lowestPending[self])) /\ ((client) < (nextClient[self])))]
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
                                       /\ pendingClients' = [pendingClients EXCEPT ![self] = (pendingClients[self]) \ ({client})]
                                  /\ pc' = [pc EXCEPT ![self] = "findMinClient"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "addStableMessage"]
                                  /\ UNCHANGED << firstPending, timestamp,
                                                  nextClient, lowestPending,
                                                  chooseMessage,
                                                  pendingClients >>
                       /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                       cid, out, clocks, kvLocal, liveClients,
                                       pendingRequests, stableMessages, i_,
                                       currentClocks, minClock, continue_,
                                       clientsIter, msg_, ok, key, val,
                                       replicasRead, replicasWrite, kvRead,
                                       clientsWrite, clientsWrite0, kvWrite,
                                       kvWrite0, clientsWrite1, spinLocal,
                                       continue_G, getReq, getResp,
                                       clientIdRead, lockedRead, clientIdRead0,
                                       clockRead, clientIdRead1, lockedWrite,
                                       clientIdRead2, clockRead0,
                                       clientIdRead3, clockWrite, keyRead,
                                       clientIdRead4, clientIdRead5,
                                       clockRead1, replicasWrite0, clientsRead,
                                       clientsWrite2, outsideWrite,
                                       lockedWrite0, clockWrite0,
                                       replicasWrite1, clientsWrite3,
                                       outsideWrite0, spinRead, spinLocal0,
                                       continue_P, i, j_, putReq, putResp,
                                       clientIdRead6, lockedRead0,
                                       clientIdRead7, clockRead2,
                                       clientIdRead8, clockRead3,
                                       clientIdRead9, clockWrite1, keyRead0,
                                       valueRead, clientIdRead10,
                                       clientIdRead11, clockRead4,
                                       clientIdRead12, lockedWrite1,
                                       replicasWrite2, replicasWrite3,
                                       clientsRead0, clientsWrite4,
                                       clientsWrite5, lockedWrite2,
                                       outsideWrite1, spinRead0, msg_D, j_D,
                                       clientIdRead13, lockedRead1,
                                       clientIdRead14, clientIdRead15,
                                       clockWrite2, clockWrite3,
                                       replicasWrite4, replicasWrite5,
                                       spinLocal1, continue, j, msg,
                                       clientIdRead16, clockRead5,
                                       clientIdRead17, clockRead6,
                                       clientIdRead18, clockWrite4,
                                       clientIdRead19, clientIdRead20,
                                       clockRead7, replicasWrite6,
                                       replicasWrite7, spinRead1 >>

addStableMessage(self) == /\ pc[self] = "addStableMessage"
                          /\ IF (lowestPending[self]) < (minClock[self])
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
                                          lock, cid, out, clocks, kvLocal,
                                          liveClients, i_, firstPending,
                                          timestamp, nextClient, lowestPending,
                                          chooseMessage, currentClocks,
                                          minClock, pendingClients,
                                          clientsIter, ok, key, val,
                                          replicasRead, replicasWrite, kvRead,
                                          clientsWrite, clientsWrite0, kvWrite,
                                          kvWrite0, clientsWrite1, spinLocal,
                                          continue_G, getReq, getResp,
                                          clientIdRead, lockedRead,
                                          clientIdRead0, clockRead,
                                          clientIdRead1, lockedWrite,
                                          clientIdRead2, clockRead0,
                                          clientIdRead3, clockWrite, keyRead,
                                          clientIdRead4, clientIdRead5,
                                          clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          outsideWrite, lockedWrite0,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, outsideWrite0,
                                          spinRead, spinLocal0, continue_P, i,
                                          j_, putReq, putResp, clientIdRead6,
                                          lockedRead0, clientIdRead7,
                                          clockRead2, clientIdRead8,
                                          clockRead3, clientIdRead9,
                                          clockWrite1, keyRead0, valueRead,
                                          clientIdRead10, clientIdRead11,
                                          clockRead4, clientIdRead12,
                                          lockedWrite1, replicasWrite2,
                                          replicasWrite3, clientsRead0,
                                          clientsWrite4, clientsWrite5,
                                          lockedWrite2, outsideWrite1,
                                          spinRead0, msg_D, j_D,
                                          clientIdRead13, lockedRead1,
                                          clientIdRead14, clientIdRead15,
                                          clockWrite2, clockWrite3,
                                          replicasWrite4, replicasWrite5,
                                          spinLocal1, continue, j, msg,
                                          clientIdRead16, clockRead5,
                                          clientIdRead17, clockRead6,
                                          clientIdRead18, clockWrite4,
                                          clientIdRead19, clientIdRead20,
                                          clockRead7, replicasWrite6,
                                          replicasWrite7, spinRead1 >>

respondPendingRequestsLoop(self) == /\ pc[self] = "respondPendingRequestsLoop"
                                    /\ IF (i_[self]) <= (Len(stableMessages[self]))
                                          THEN /\ msg_' = [msg_ EXCEPT ![self] = stableMessages[self][i_[self]]]
                                               /\ i_' = [i_ EXCEPT ![self] = (i_[self]) + (1)]
                                               /\ pc' = [pc EXCEPT ![self] = "respondStableGet"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "replicaLoop"]
                                               /\ UNCHANGED << i_, msg_ >>
                                    /\ UNCHANGED << replicasNetwork,
                                                    clientsNetwork, lock, cid,
                                                    out, clocks, kvLocal,
                                                    liveClients,
                                                    pendingRequests,
                                                    stableMessages,
                                                    firstPending, timestamp,
                                                    nextClient, lowestPending,
                                                    chooseMessage,
                                                    currentClocks, minClock,
                                                    continue_, pendingClients,
                                                    clientsIter, ok, key, val,
                                                    replicasRead,
                                                    replicasWrite, kvRead,
                                                    clientsWrite,
                                                    clientsWrite0, kvWrite,
                                                    kvWrite0, clientsWrite1,
                                                    spinLocal, continue_G,
                                                    getReq, getResp,
                                                    clientIdRead, lockedRead,
                                                    clientIdRead0, clockRead,
                                                    clientIdRead1, lockedWrite,
                                                    clientIdRead2, clockRead0,
                                                    clientIdRead3, clockWrite,
                                                    keyRead, clientIdRead4,
                                                    clientIdRead5, clockRead1,
                                                    replicasWrite0,
                                                    clientsRead, clientsWrite2,
                                                    outsideWrite, lockedWrite0,
                                                    clockWrite0,
                                                    replicasWrite1,
                                                    clientsWrite3,
                                                    outsideWrite0, spinRead,
                                                    spinLocal0, continue_P, i,
                                                    j_, putReq, putResp,
                                                    clientIdRead6, lockedRead0,
                                                    clientIdRead7, clockRead2,
                                                    clientIdRead8, clockRead3,
                                                    clientIdRead9, clockWrite1,
                                                    keyRead0, valueRead,
                                                    clientIdRead10,
                                                    clientIdRead11, clockRead4,
                                                    clientIdRead12,
                                                    lockedWrite1,
                                                    replicasWrite2,
                                                    replicasWrite3,
                                                    clientsRead0,
                                                    clientsWrite4,
                                                    clientsWrite5,
                                                    lockedWrite2,
                                                    outsideWrite1, spinRead0,
                                                    msg_D, j_D, clientIdRead13,
                                                    lockedRead1,
                                                    clientIdRead14,
                                                    clientIdRead15,
                                                    clockWrite2, clockWrite3,
                                                    replicasWrite4,
                                                    replicasWrite5, spinLocal1,
                                                    continue, j, msg,
                                                    clientIdRead16, clockRead5,
                                                    clientIdRead17, clockRead6,
                                                    clientIdRead18,
                                                    clockWrite4,
                                                    clientIdRead19,
                                                    clientIdRead20, clockRead7,
                                                    replicasWrite6,
                                                    replicasWrite7, spinRead1 >>

respondStableGet(self) == /\ pc[self] = "respondStableGet"
                          /\ IF ((msg_[self]).op) = (GET_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ kvRead' = [kvRead EXCEPT ![self] = kvLocal[self][key'[self]]]
                                     /\ val' = [val EXCEPT ![self] = kvRead'[self]]
                                     /\ (Len(clientsNetwork[(msg_[self]).client])) < (BUFFER_SIZE)
                                     /\ clientsWrite' = [clientsWrite EXCEPT ![self] = [clientsNetwork EXCEPT ![(msg_[self]).client] = Append(clientsNetwork[(msg_[self]).client], [type |-> GET_RESPONSE, result |-> val'[self]])]]
                                     /\ clientsWrite0' = [clientsWrite0 EXCEPT ![self] = clientsWrite'[self]]
                                     /\ clientsNetwork' = clientsWrite0'[self]
                                ELSE /\ clientsWrite0' = [clientsWrite0 EXCEPT ![self] = clientsNetwork]
                                     /\ clientsNetwork' = clientsWrite0'[self]
                                     /\ UNCHANGED << key, val, kvRead,
                                                     clientsWrite >>
                          /\ pc' = [pc EXCEPT ![self] = "respondStablePut"]
                          /\ UNCHANGED << replicasNetwork, lock, cid, out,
                                          clocks, kvLocal, liveClients,
                                          pendingRequests, stableMessages, i_,
                                          firstPending, timestamp, nextClient,
                                          lowestPending, chooseMessage,
                                          currentClocks, minClock, continue_,
                                          pendingClients, clientsIter, msg_,
                                          ok, replicasRead, replicasWrite,
                                          kvWrite, kvWrite0, clientsWrite1,
                                          spinLocal, continue_G, getReq,
                                          getResp, clientIdRead, lockedRead,
                                          clientIdRead0, clockRead,
                                          clientIdRead1, lockedWrite,
                                          clientIdRead2, clockRead0,
                                          clientIdRead3, clockWrite, keyRead,
                                          clientIdRead4, clientIdRead5,
                                          clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          outsideWrite, lockedWrite0,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, outsideWrite0,
                                          spinRead, spinLocal0, continue_P, i,
                                          j_, putReq, putResp, clientIdRead6,
                                          lockedRead0, clientIdRead7,
                                          clockRead2, clientIdRead8,
                                          clockRead3, clientIdRead9,
                                          clockWrite1, keyRead0, valueRead,
                                          clientIdRead10, clientIdRead11,
                                          clockRead4, clientIdRead12,
                                          lockedWrite1, replicasWrite2,
                                          replicasWrite3, clientsRead0,
                                          clientsWrite4, clientsWrite5,
                                          lockedWrite2, outsideWrite1,
                                          spinRead0, msg_D, j_D,
                                          clientIdRead13, lockedRead1,
                                          clientIdRead14, clientIdRead15,
                                          clockWrite2, clockWrite3,
                                          replicasWrite4, replicasWrite5,
                                          spinLocal1, continue, j, msg,
                                          clientIdRead16, clockRead5,
                                          clientIdRead17, clockRead6,
                                          clientIdRead18, clockWrite4,
                                          clientIdRead19, clientIdRead20,
                                          clockRead7, replicasWrite6,
                                          replicasWrite7, spinRead1 >>

respondStablePut(self) == /\ pc[self] = "respondStablePut"
                          /\ IF ((msg_[self]).op) = (PUT_MSG)
                                THEN /\ key' = [key EXCEPT ![self] = (msg_[self]).key]
                                     /\ val' = [val EXCEPT ![self] = (msg_[self]).value]
                                     /\ kvWrite' = [kvWrite EXCEPT ![self] = [kvLocal[self] EXCEPT ![key'[self]] = val'[self]]]
                                     /\ (Len(clientsNetwork[(msg_[self]).client])) < (BUFFER_SIZE)
                                     /\ clientsWrite' = [clientsWrite EXCEPT ![self] = [clientsNetwork EXCEPT ![(msg_[self]).client] = Append(clientsNetwork[(msg_[self]).client], [type |-> PUT_RESPONSE, result |-> ok[self]])]]
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
                          /\ UNCHANGED << replicasNetwork, lock, cid, out,
                                          clocks, liveClients, pendingRequests,
                                          stableMessages, i_, firstPending,
                                          timestamp, nextClient, lowestPending,
                                          chooseMessage, currentClocks,
                                          minClock, continue_, pendingClients,
                                          clientsIter, msg_, ok, replicasRead,
                                          replicasWrite, kvRead, clientsWrite0,
                                          spinLocal, continue_G, getReq,
                                          getResp, clientIdRead, lockedRead,
                                          clientIdRead0, clockRead,
                                          clientIdRead1, lockedWrite,
                                          clientIdRead2, clockRead0,
                                          clientIdRead3, clockWrite, keyRead,
                                          clientIdRead4, clientIdRead5,
                                          clockRead1, replicasWrite0,
                                          clientsRead, clientsWrite2,
                                          outsideWrite, lockedWrite0,
                                          clockWrite0, replicasWrite1,
                                          clientsWrite3, outsideWrite0,
                                          spinRead, spinLocal0, continue_P, i,
                                          j_, putReq, putResp, clientIdRead6,
                                          lockedRead0, clientIdRead7,
                                          clockRead2, clientIdRead8,
                                          clockRead3, clientIdRead9,
                                          clockWrite1, keyRead0, valueRead,
                                          clientIdRead10, clientIdRead11,
                                          clockRead4, clientIdRead12,
                                          lockedWrite1, replicasWrite2,
                                          replicasWrite3, clientsRead0,
                                          clientsWrite4, clientsWrite5,
                                          lockedWrite2, outsideWrite1,
                                          spinRead0, msg_D, j_D,
                                          clientIdRead13, lockedRead1,
                                          clientIdRead14, clientIdRead15,
                                          clockWrite2, clockWrite3,
                                          replicasWrite4, replicasWrite5,
                                          spinLocal1, continue, j, msg,
                                          clientIdRead16, clockRead5,
                                          clientIdRead17, clockRead6,
                                          clientIdRead18, clockWrite4,
                                          clientIdRead19, clientIdRead20,
                                          clockRead7, replicasWrite6,
                                          replicasWrite7, spinRead1 >>

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
                 /\ UNCHANGED << replicasNetwork, clientsNetwork, lock, cid,
                                 out, clocks, kvLocal, liveClients,
                                 pendingRequests, stableMessages, i_,
                                 firstPending, timestamp, nextClient,
                                 lowestPending, chooseMessage, currentClocks,
                                 minClock, continue_, pendingClients,
                                 clientsIter, msg_, ok, key, val, replicasRead,
                                 replicasWrite, kvRead, clientsWrite,
                                 clientsWrite0, kvWrite, kvWrite0,
                                 clientsWrite1, spinLocal, continue_G, getReq,
                                 getResp, clientIdRead, lockedRead,
                                 clientIdRead0, clockRead, clientIdRead1,
                                 lockedWrite, clientIdRead2, clockRead0,
                                 clientIdRead3, clockWrite, keyRead,
                                 clientIdRead4, clientIdRead5, clockRead1,
                                 replicasWrite0, clientsRead, clientsWrite2,
                                 outsideWrite, lockedWrite0, clockWrite0,
                                 replicasWrite1, clientsWrite3, outsideWrite0,
                                 spinRead, spinLocal0, continue_P, i, j_,
                                 putReq, putResp, clientIdRead6, lockedRead0,
                                 clientIdRead7, clockRead2, clientIdRead8,
                                 clockRead3, clientIdRead9, clockWrite1,
                                 keyRead0, valueRead, clientIdRead10,
                                 clientIdRead11, clockRead4, clientIdRead12,
                                 lockedWrite1, replicasWrite2, replicasWrite3,
                                 clientsRead0, clientsWrite4, clientsWrite5,
                                 lockedWrite2, outsideWrite1, spinRead0, msg_D,
                                 j_D, clientIdRead13, lockedRead1,
                                 clientIdRead14, clientIdRead15, clockWrite2,
                                 clockWrite3, replicasWrite4, replicasWrite5,
                                 spinLocal1, continue, j, msg, clientIdRead16,
                                 clockRead5, clientIdRead17, clockRead6,
                                 clientIdRead18, clockWrite4, clientIdRead19,
                                 clientIdRead20, clockRead7, replicasWrite6,
                                 replicasWrite7, spinRead1 >>

getRequest(self) == /\ pc[self] = "getRequest"
                    /\ clientIdRead' = [clientIdRead EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                    /\ ~(lock[clientIdRead'[self]])
                    /\ lockedRead' = [lockedRead EXCEPT ![self] = FALSE]
                    /\ IF ~(lockedRead'[self])
                          THEN /\ clientIdRead0' = [clientIdRead0 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                               /\ clockRead' = [clockRead EXCEPT ![self] = clocks[clientIdRead0'[self]]]
                               /\ IF (clockRead'[self]) = (-(1))
                                     THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                                          /\ lockedWrite0' = [lockedWrite0 EXCEPT ![self] = lock]
                                          /\ clockWrite0' = [clockWrite0 EXCEPT ![self] = clocks]
                                          /\ replicasWrite1' = [replicasWrite1 EXCEPT ![self] = replicasNetwork]
                                          /\ clientsWrite3' = [clientsWrite3 EXCEPT ![self] = clientsNetwork]
                                          /\ outsideWrite0' = [outsideWrite0 EXCEPT ![self] = out]
                                          /\ replicasNetwork' = replicasWrite1'[self]
                                          /\ clientsNetwork' = clientsWrite3'[self]
                                          /\ lock' = lockedWrite0'[self]
                                          /\ clocks' = clockWrite0'[self]
                                          /\ out' = outsideWrite0'[self]
                                          /\ pc' = [pc EXCEPT ![self] = "getCheckSpin"]
                                          /\ UNCHANGED << getReq,
                                                          clientIdRead1,
                                                          lockedWrite,
                                                          clientIdRead2,
                                                          clockRead0,
                                                          clientIdRead3,
                                                          clockWrite, keyRead,
                                                          clientIdRead4,
                                                          clientIdRead5,
                                                          clockRead1,
                                                          replicasWrite0 >>
                                     ELSE /\ clientIdRead1' = [clientIdRead1 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                                          /\ lockedWrite' = [lockedWrite EXCEPT ![self] = [lock EXCEPT ![clientIdRead1'[self]] = TRUE]]
                                          /\ clientIdRead2' = [clientIdRead2 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                                          /\ clockRead0' = [clockRead0 EXCEPT ![self] = clocks[clientIdRead2'[self]]]
                                          /\ clientIdRead3' = [clientIdRead3 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                                          /\ clockWrite' = [clockWrite EXCEPT ![self] = [clocks EXCEPT ![clientIdRead3'[self]] = (clockRead0'[self]) + (1)]]
                                          /\ keyRead' = [keyRead EXCEPT ![self] = GET_KEY]
                                          /\ clientIdRead4' = [clientIdRead4 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                                          /\ clientIdRead5' = [clientIdRead5 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                                          /\ clockRead1' = [clockRead1 EXCEPT ![self] = clockWrite'[self][clientIdRead5'[self]]]
                                          /\ getReq' = [getReq EXCEPT ![self] = [op |-> GET_MSG, key |-> keyRead'[self], client |-> clientIdRead4'[self], timestamp |-> clockRead1'[self]]]
                                          /\ \E dst \in ReplicaSet:
                                               /\ (Len(replicasNetwork[dst])) < (BUFFER_SIZE)
                                               /\ replicasWrite0' = [replicasWrite0 EXCEPT ![self] = [replicasNetwork EXCEPT ![dst] = Append(replicasNetwork[dst], getReq'[self])]]
                                          /\ replicasNetwork' = replicasWrite0'[self]
                                          /\ lock' = lockedWrite'[self]
                                          /\ clocks' = clockWrite'[self]
                                          /\ pc' = [pc EXCEPT ![self] = "getReply"]
                                          /\ UNCHANGED << clientsNetwork, out,
                                                          continue_G,
                                                          lockedWrite0,
                                                          clockWrite0,
                                                          replicasWrite1,
                                                          clientsWrite3,
                                                          outsideWrite0 >>
                          ELSE /\ replicasNetwork' = replicasWrite1[self]
                               /\ clientsNetwork' = clientsWrite3[self]
                               /\ lock' = lockedWrite0[self]
                               /\ clocks' = clockWrite0[self]
                               /\ out' = outsideWrite0[self]
                               /\ pc' = [pc EXCEPT ![self] = "getCheckSpin"]
                               /\ UNCHANGED << continue_G, getReq,
                                               clientIdRead0, clockRead,
                                               clientIdRead1, lockedWrite,
                                               clientIdRead2, clockRead0,
                                               clientIdRead3, clockWrite,
                                               keyRead, clientIdRead4,
                                               clientIdRead5, clockRead1,
                                               replicasWrite0, lockedWrite0,
                                               clockWrite0, replicasWrite1,
                                               clientsWrite3, outsideWrite0 >>
                    /\ UNCHANGED << cid, kvLocal, liveClients, pendingRequests,
                                    stableMessages, i_, firstPending,
                                    timestamp, nextClient, lowestPending,
                                    chooseMessage, currentClocks, minClock,
                                    continue_, pendingClients, clientsIter,
                                    msg_, ok, key, val, replicasRead,
                                    replicasWrite, kvRead, clientsWrite,
                                    clientsWrite0, kvWrite, kvWrite0,
                                    clientsWrite1, spinLocal, getResp,
                                    clientsRead, clientsWrite2, outsideWrite,
                                    spinRead, spinLocal0, continue_P, i, j_,
                                    putReq, putResp, clientIdRead6,
                                    lockedRead0, clientIdRead7, clockRead2,
                                    clientIdRead8, clockRead3, clientIdRead9,
                                    clockWrite1, keyRead0, valueRead,
                                    clientIdRead10, clientIdRead11, clockRead4,
                                    clientIdRead12, lockedWrite1,
                                    replicasWrite2, replicasWrite3,
                                    clientsRead0, clientsWrite4, clientsWrite5,
                                    lockedWrite2, outsideWrite1, spinRead0,
                                    msg_D, j_D, clientIdRead13, lockedRead1,
                                    clientIdRead14, clientIdRead15,
                                    clockWrite2, clockWrite3, replicasWrite4,
                                    replicasWrite5, spinLocal1, continue, j,
                                    msg, clientIdRead16, clockRead5,
                                    clientIdRead17, clockRead6, clientIdRead18,
                                    clockWrite4, clientIdRead19,
                                    clientIdRead20, clockRead7, replicasWrite6,
                                    replicasWrite7, spinRead1 >>

getReply(self) == /\ pc[self] = "getReply"
                  /\ clientIdRead' = [clientIdRead EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                  /\ (Len(clientsNetwork[clientIdRead'[self]])) > (0)
                  /\ LET msg1 == Head(clientsNetwork[clientIdRead'[self]]) IN
                       /\ clientsWrite2' = [clientsWrite2 EXCEPT ![self] = [clientsNetwork EXCEPT ![clientIdRead'[self]] = Tail(clientsNetwork[clientIdRead'[self]])]]
                       /\ clientsRead' = [clientsRead EXCEPT ![self] = msg1]
                  /\ getResp' = [getResp EXCEPT ![self] = clientsRead'[self]]
                  /\ Assert(((getResp'[self]).type) = (GET_RESPONSE),
                            "Failure of assertion at line 867, column 33.")
                  /\ clientIdRead0' = [clientIdRead0 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (GET_ORDER))]
                  /\ lockedWrite' = [lockedWrite EXCEPT ![self] = [lock EXCEPT ![clientIdRead0'[self]] = FALSE]]
                  /\ outsideWrite' = [outsideWrite EXCEPT ![self] = (getResp'[self]).result]
                  /\ clientsNetwork' = clientsWrite2'[self]
                  /\ lock' = lockedWrite'[self]
                  /\ out' = outsideWrite'[self]
                  /\ pc' = [pc EXCEPT ![self] = "getCheckSpin"]
                  /\ UNCHANGED << replicasNetwork, cid, clocks, kvLocal,
                                  liveClients, pendingRequests, stableMessages,
                                  i_, firstPending, timestamp, nextClient,
                                  lowestPending, chooseMessage, currentClocks,
                                  minClock, continue_, pendingClients,
                                  clientsIter, msg_, ok, key, val,
                                  replicasRead, replicasWrite, kvRead,
                                  clientsWrite, clientsWrite0, kvWrite,
                                  kvWrite0, clientsWrite1, spinLocal,
                                  continue_G, getReq, lockedRead, clockRead,
                                  clientIdRead1, clientIdRead2, clockRead0,
                                  clientIdRead3, clockWrite, keyRead,
                                  clientIdRead4, clientIdRead5, clockRead1,
                                  replicasWrite0, lockedWrite0, clockWrite0,
                                  replicasWrite1, clientsWrite3, outsideWrite0,
                                  spinRead, spinLocal0, continue_P, i, j_,
                                  putReq, putResp, clientIdRead6, lockedRead0,
                                  clientIdRead7, clockRead2, clientIdRead8,
                                  clockRead3, clientIdRead9, clockWrite1,
                                  keyRead0, valueRead, clientIdRead10,
                                  clientIdRead11, clockRead4, clientIdRead12,
                                  lockedWrite1, replicasWrite2, replicasWrite3,
                                  clientsRead0, clientsWrite4, clientsWrite5,
                                  lockedWrite2, outsideWrite1, spinRead0,
                                  msg_D, j_D, clientIdRead13, lockedRead1,
                                  clientIdRead14, clientIdRead15, clockWrite2,
                                  clockWrite3, replicasWrite4, replicasWrite5,
                                  spinLocal1, continue, j, msg, clientIdRead16,
                                  clockRead5, clientIdRead17, clockRead6,
                                  clientIdRead18, clockWrite4, clientIdRead19,
                                  clientIdRead20, clockRead7, replicasWrite6,
                                  replicasWrite7, spinRead1 >>

getCheckSpin(self) == /\ pc[self] = "getCheckSpin"
                      /\ spinRead' = [spinRead EXCEPT ![self] = spinLocal[self]]
                      /\ IF ~(spinRead'[self])
                            THEN /\ continue_G' = [continue_G EXCEPT ![self] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "getLoop"]
                                 /\ UNCHANGED continue_G
                      /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                      cid, out, clocks, kvLocal, liveClients,
                                      pendingRequests, stableMessages, i_,
                                      firstPending, timestamp, nextClient,
                                      lowestPending, chooseMessage,
                                      currentClocks, minClock, continue_,
                                      pendingClients, clientsIter, msg_, ok,
                                      key, val, replicasRead, replicasWrite,
                                      kvRead, clientsWrite, clientsWrite0,
                                      kvWrite, kvWrite0, clientsWrite1,
                                      spinLocal, getReq, getResp, clientIdRead,
                                      lockedRead, clientIdRead0, clockRead,
                                      clientIdRead1, lockedWrite,
                                      clientIdRead2, clockRead0, clientIdRead3,
                                      clockWrite, keyRead, clientIdRead4,
                                      clientIdRead5, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, outsideWrite,
                                      lockedWrite0, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      outsideWrite0, spinLocal0, continue_P, i,
                                      j_, putReq, putResp, clientIdRead6,
                                      lockedRead0, clientIdRead7, clockRead2,
                                      clientIdRead8, clockRead3, clientIdRead9,
                                      clockWrite1, keyRead0, valueRead,
                                      clientIdRead10, clientIdRead11,
                                      clockRead4, clientIdRead12, lockedWrite1,
                                      replicasWrite2, replicasWrite3,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite2,
                                      outsideWrite1, spinRead0, msg_D, j_D,
                                      clientIdRead13, lockedRead1,
                                      clientIdRead14, clientIdRead15,
                                      clockWrite2, clockWrite3, replicasWrite4,
                                      replicasWrite5, spinLocal1, continue, j,
                                      msg, clientIdRead16, clockRead5,
                                      clientIdRead17, clockRead6,
                                      clientIdRead18, clockWrite4,
                                      clientIdRead19, clientIdRead20,
                                      clockRead7, replicasWrite6,
                                      replicasWrite7, spinRead1 >>

GetClient(self) == getLoop(self) \/ getRequest(self) \/ getReply(self)
                      \/ getCheckSpin(self)

putLoop(self) == /\ pc[self] = "putLoop"
                 /\ IF continue_P[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "putRequest"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << replicasNetwork, clientsNetwork, lock, cid,
                                 out, clocks, kvLocal, liveClients,
                                 pendingRequests, stableMessages, i_,
                                 firstPending, timestamp, nextClient,
                                 lowestPending, chooseMessage, currentClocks,
                                 minClock, continue_, pendingClients,
                                 clientsIter, msg_, ok, key, val, replicasRead,
                                 replicasWrite, kvRead, clientsWrite,
                                 clientsWrite0, kvWrite, kvWrite0,
                                 clientsWrite1, spinLocal, continue_G, getReq,
                                 getResp, clientIdRead, lockedRead,
                                 clientIdRead0, clockRead, clientIdRead1,
                                 lockedWrite, clientIdRead2, clockRead0,
                                 clientIdRead3, clockWrite, keyRead,
                                 clientIdRead4, clientIdRead5, clockRead1,
                                 replicasWrite0, clientsRead, clientsWrite2,
                                 outsideWrite, lockedWrite0, clockWrite0,
                                 replicasWrite1, clientsWrite3, outsideWrite0,
                                 spinRead, spinLocal0, continue_P, i, j_,
                                 putReq, putResp, clientIdRead6, lockedRead0,
                                 clientIdRead7, clockRead2, clientIdRead8,
                                 clockRead3, clientIdRead9, clockWrite1,
                                 keyRead0, valueRead, clientIdRead10,
                                 clientIdRead11, clockRead4, clientIdRead12,
                                 lockedWrite1, replicasWrite2, replicasWrite3,
                                 clientsRead0, clientsWrite4, clientsWrite5,
                                 lockedWrite2, outsideWrite1, spinRead0, msg_D,
                                 j_D, clientIdRead13, lockedRead1,
                                 clientIdRead14, clientIdRead15, clockWrite2,
                                 clockWrite3, replicasWrite4, replicasWrite5,
                                 spinLocal1, continue, j, msg, clientIdRead16,
                                 clockRead5, clientIdRead17, clockRead6,
                                 clientIdRead18, clockWrite4, clientIdRead19,
                                 clientIdRead20, clockRead7, replicasWrite6,
                                 replicasWrite7, spinRead1 >>

putRequest(self) == /\ pc[self] = "putRequest"
                    /\ clientIdRead6' = [clientIdRead6 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                    /\ ~(lock[clientIdRead6'[self]])
                    /\ lockedRead0' = [lockedRead0 EXCEPT ![self] = FALSE]
                    /\ IF ~(lockedRead0'[self])
                          THEN /\ clientIdRead7' = [clientIdRead7 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                               /\ clockRead2' = [clockRead2 EXCEPT ![self] = clocks[clientIdRead7'[self]]]
                               /\ IF (clockRead2'[self]) = (-(1))
                                     THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                                          /\ pc' = [pc EXCEPT ![self] = "putCheckSpin"]
                                          /\ UNCHANGED << lock, clocks, i, j_,
                                                          putReq,
                                                          clientIdRead8,
                                                          clockRead3,
                                                          clientIdRead9,
                                                          clockWrite1,
                                                          keyRead0, valueRead,
                                                          clientIdRead10,
                                                          clientIdRead11,
                                                          clockRead4,
                                                          clientIdRead12,
                                                          lockedWrite1 >>
                                     ELSE /\ clientIdRead8' = [clientIdRead8 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                          /\ clockRead3' = [clockRead3 EXCEPT ![self] = clocks[clientIdRead8'[self]]]
                                          /\ clientIdRead9' = [clientIdRead9 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                          /\ clockWrite1' = [clockWrite1 EXCEPT ![self] = [clocks EXCEPT ![clientIdRead9'[self]] = (clockRead3'[self]) + (1)]]
                                          /\ keyRead0' = [keyRead0 EXCEPT ![self] = PUT_KEY]
                                          /\ valueRead' = [valueRead EXCEPT ![self] = PUT_VALUE]
                                          /\ clientIdRead10' = [clientIdRead10 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                          /\ clientIdRead11' = [clientIdRead11 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                          /\ clockRead4' = [clockRead4 EXCEPT ![self] = clockWrite1'[self][clientIdRead11'[self]]]
                                          /\ putReq' = [putReq EXCEPT ![self] = [op |-> PUT_MSG, key |-> keyRead0'[self], value |-> valueRead'[self], client |-> clientIdRead10'[self], timestamp |-> clockRead4'[self]]]
                                          /\ clientIdRead12' = [clientIdRead12 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                          /\ lockedWrite1' = [lockedWrite1 EXCEPT ![self] = [lock EXCEPT ![clientIdRead12'[self]] = TRUE]]
                                          /\ i' = [i EXCEPT ![self] = 0]
                                          /\ j_' = [j_ EXCEPT ![self] = 0]
                                          /\ lock' = lockedWrite1'[self]
                                          /\ clocks' = clockWrite1'[self]
                                          /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                                          /\ UNCHANGED continue_P
                          ELSE /\ pc' = [pc EXCEPT ![self] = "putCheckSpin"]
                               /\ UNCHANGED << lock, clocks, continue_P, i, j_,
                                               putReq, clientIdRead7,
                                               clockRead2, clientIdRead8,
                                               clockRead3, clientIdRead9,
                                               clockWrite1, keyRead0,
                                               valueRead, clientIdRead10,
                                               clientIdRead11, clockRead4,
                                               clientIdRead12, lockedWrite1 >>
                    /\ UNCHANGED << replicasNetwork, clientsNetwork, cid, out,
                                    kvLocal, liveClients, pendingRequests,
                                    stableMessages, i_, firstPending,
                                    timestamp, nextClient, lowestPending,
                                    chooseMessage, currentClocks, minClock,
                                    continue_, pendingClients, clientsIter,
                                    msg_, ok, key, val, replicasRead,
                                    replicasWrite, kvRead, clientsWrite,
                                    clientsWrite0, kvWrite, kvWrite0,
                                    clientsWrite1, spinLocal, continue_G,
                                    getReq, getResp, clientIdRead, lockedRead,
                                    clientIdRead0, clockRead, clientIdRead1,
                                    lockedWrite, clientIdRead2, clockRead0,
                                    clientIdRead3, clockWrite, keyRead,
                                    clientIdRead4, clientIdRead5, clockRead1,
                                    replicasWrite0, clientsRead, clientsWrite2,
                                    outsideWrite, lockedWrite0, clockWrite0,
                                    replicasWrite1, clientsWrite3,
                                    outsideWrite0, spinRead, spinLocal0,
                                    putResp, replicasWrite2, replicasWrite3,
                                    clientsRead0, clientsWrite4, clientsWrite5,
                                    lockedWrite2, outsideWrite1, spinRead0,
                                    msg_D, j_D, clientIdRead13, lockedRead1,
                                    clientIdRead14, clientIdRead15,
                                    clockWrite2, clockWrite3, replicasWrite4,
                                    replicasWrite5, spinLocal1, continue, j,
                                    msg, clientIdRead16, clockRead5,
                                    clientIdRead17, clockRead6, clientIdRead18,
                                    clockWrite4, clientIdRead19,
                                    clientIdRead20, clockRead7, replicasWrite6,
                                    replicasWrite7, spinRead1 >>

putBroadcast(self) == /\ pc[self] = "putBroadcast"
                      /\ IF (j_[self]) <= ((NUM_REPLICAS) - (1))
                            THEN /\ (Len(replicasNetwork[j_[self]])) < (BUFFER_SIZE)
                                 /\ replicasWrite2' = [replicasWrite2 EXCEPT ![self] = [replicasNetwork EXCEPT ![j_[self]] = Append(replicasNetwork[j_[self]], putReq[self])]]
                                 /\ j_' = [j_ EXCEPT ![self] = (j_[self]) + (1)]
                                 /\ replicasWrite3' = [replicasWrite3 EXCEPT ![self] = replicasWrite2'[self]]
                                 /\ replicasNetwork' = replicasWrite3'[self]
                                 /\ pc' = [pc EXCEPT ![self] = "putBroadcast"]
                            ELSE /\ replicasWrite3' = [replicasWrite3 EXCEPT ![self] = replicasNetwork]
                                 /\ replicasNetwork' = replicasWrite3'[self]
                                 /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                 /\ UNCHANGED << j_, replicasWrite2 >>
                      /\ UNCHANGED << clientsNetwork, lock, cid, out, clocks,
                                      kvLocal, liveClients, pendingRequests,
                                      stableMessages, i_, firstPending,
                                      timestamp, nextClient, lowestPending,
                                      chooseMessage, currentClocks, minClock,
                                      continue_, pendingClients, clientsIter,
                                      msg_, ok, key, val, replicasRead,
                                      replicasWrite, kvRead, clientsWrite,
                                      clientsWrite0, kvWrite, kvWrite0,
                                      clientsWrite1, spinLocal, continue_G,
                                      getReq, getResp, clientIdRead,
                                      lockedRead, clientIdRead0, clockRead,
                                      clientIdRead1, lockedWrite,
                                      clientIdRead2, clockRead0, clientIdRead3,
                                      clockWrite, keyRead, clientIdRead4,
                                      clientIdRead5, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, outsideWrite,
                                      lockedWrite0, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      outsideWrite0, spinRead, spinLocal0,
                                      continue_P, i, putReq, putResp,
                                      clientIdRead6, lockedRead0,
                                      clientIdRead7, clockRead2, clientIdRead8,
                                      clockRead3, clientIdRead9, clockWrite1,
                                      keyRead0, valueRead, clientIdRead10,
                                      clientIdRead11, clockRead4,
                                      clientIdRead12, lockedWrite1,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite2,
                                      outsideWrite1, spinRead0, msg_D, j_D,
                                      clientIdRead13, lockedRead1,
                                      clientIdRead14, clientIdRead15,
                                      clockWrite2, clockWrite3, replicasWrite4,
                                      replicasWrite5, spinLocal1, continue, j,
                                      msg, clientIdRead16, clockRead5,
                                      clientIdRead17, clockRead6,
                                      clientIdRead18, clockWrite4,
                                      clientIdRead19, clientIdRead20,
                                      clockRead7, replicasWrite6,
                                      replicasWrite7, spinRead1 >>

putResponse(self) == /\ pc[self] = "putResponse"
                     /\ IF (i[self]) < (Cardinality(ReplicaSet))
                           THEN /\ clientIdRead6' = [clientIdRead6 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                /\ (Len(clientsNetwork[clientIdRead6'[self]])) > (0)
                                /\ LET msg2 == Head(clientsNetwork[clientIdRead6'[self]]) IN
                                     /\ clientsWrite4' = [clientsWrite4 EXCEPT ![self] = [clientsNetwork EXCEPT ![clientIdRead6'[self]] = Tail(clientsNetwork[clientIdRead6'[self]])]]
                                     /\ clientsRead0' = [clientsRead0 EXCEPT ![self] = msg2]
                                /\ putResp' = [putResp EXCEPT ![self] = clientsRead0'[self]]
                                /\ Assert(((putResp'[self]).type) = (PUT_RESPONSE),
                                          "Failure of assertion at line 949, column 37.")
                                /\ i' = [i EXCEPT ![self] = (i[self]) + (1)]
                                /\ clientsWrite5' = [clientsWrite5 EXCEPT ![self] = clientsWrite4'[self]]
                                /\ lockedWrite2' = [lockedWrite2 EXCEPT ![self] = lock]
                                /\ clientsNetwork' = clientsWrite5'[self]
                                /\ lock' = lockedWrite2'[self]
                                /\ pc' = [pc EXCEPT ![self] = "putResponse"]
                                /\ UNCHANGED << clientIdRead7, lockedWrite1 >>
                           ELSE /\ clientIdRead7' = [clientIdRead7 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (PUT_ORDER))]
                                /\ lockedWrite1' = [lockedWrite1 EXCEPT ![self] = [lock EXCEPT ![clientIdRead7'[self]] = FALSE]]
                                /\ clientsWrite5' = [clientsWrite5 EXCEPT ![self] = clientsNetwork]
                                /\ lockedWrite2' = [lockedWrite2 EXCEPT ![self] = lockedWrite1'[self]]
                                /\ clientsNetwork' = clientsWrite5'[self]
                                /\ lock' = lockedWrite2'[self]
                                /\ pc' = [pc EXCEPT ![self] = "putComplete"]
                                /\ UNCHANGED << i, putResp, clientIdRead6,
                                                clientsRead0, clientsWrite4 >>
                     /\ UNCHANGED << replicasNetwork, cid, out, clocks,
                                     kvLocal, liveClients, pendingRequests,
                                     stableMessages, i_, firstPending,
                                     timestamp, nextClient, lowestPending,
                                     chooseMessage, currentClocks, minClock,
                                     continue_, pendingClients, clientsIter,
                                     msg_, ok, key, val, replicasRead,
                                     replicasWrite, kvRead, clientsWrite,
                                     clientsWrite0, kvWrite, kvWrite0,
                                     clientsWrite1, spinLocal, continue_G,
                                     getReq, getResp, clientIdRead, lockedRead,
                                     clientIdRead0, clockRead, clientIdRead1,
                                     lockedWrite, clientIdRead2, clockRead0,
                                     clientIdRead3, clockWrite, keyRead,
                                     clientIdRead4, clientIdRead5, clockRead1,
                                     replicasWrite0, clientsRead,
                                     clientsWrite2, outsideWrite, lockedWrite0,
                                     clockWrite0, replicasWrite1,
                                     clientsWrite3, outsideWrite0, spinRead,
                                     spinLocal0, continue_P, j_, putReq,
                                     lockedRead0, clockRead2, clientIdRead8,
                                     clockRead3, clientIdRead9, clockWrite1,
                                     keyRead0, valueRead, clientIdRead10,
                                     clientIdRead11, clockRead4,
                                     clientIdRead12, replicasWrite2,
                                     replicasWrite3, outsideWrite1, spinRead0,
                                     msg_D, j_D, clientIdRead13, lockedRead1,
                                     clientIdRead14, clientIdRead15,
                                     clockWrite2, clockWrite3, replicasWrite4,
                                     replicasWrite5, spinLocal1, continue, j,
                                     msg, clientIdRead16, clockRead5,
                                     clientIdRead17, clockRead6,
                                     clientIdRead18, clockWrite4,
                                     clientIdRead19, clientIdRead20,
                                     clockRead7, replicasWrite6,
                                     replicasWrite7, spinRead1 >>

putComplete(self) == /\ pc[self] = "putComplete"
                     /\ outsideWrite1' = [outsideWrite1 EXCEPT ![self] = PUT_RESPONSE]
                     /\ out' = outsideWrite1'[self]
                     /\ pc' = [pc EXCEPT ![self] = "putCheckSpin"]
                     /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                     cid, clocks, kvLocal, liveClients,
                                     pendingRequests, stableMessages, i_,
                                     firstPending, timestamp, nextClient,
                                     lowestPending, chooseMessage,
                                     currentClocks, minClock, continue_,
                                     pendingClients, clientsIter, msg_, ok,
                                     key, val, replicasRead, replicasWrite,
                                     kvRead, clientsWrite, clientsWrite0,
                                     kvWrite, kvWrite0, clientsWrite1,
                                     spinLocal, continue_G, getReq, getResp,
                                     clientIdRead, lockedRead, clientIdRead0,
                                     clockRead, clientIdRead1, lockedWrite,
                                     clientIdRead2, clockRead0, clientIdRead3,
                                     clockWrite, keyRead, clientIdRead4,
                                     clientIdRead5, clockRead1, replicasWrite0,
                                     clientsRead, clientsWrite2, outsideWrite,
                                     lockedWrite0, clockWrite0, replicasWrite1,
                                     clientsWrite3, outsideWrite0, spinRead,
                                     spinLocal0, continue_P, i, j_, putReq,
                                     putResp, clientIdRead6, lockedRead0,
                                     clientIdRead7, clockRead2, clientIdRead8,
                                     clockRead3, clientIdRead9, clockWrite1,
                                     keyRead0, valueRead, clientIdRead10,
                                     clientIdRead11, clockRead4,
                                     clientIdRead12, lockedWrite1,
                                     replicasWrite2, replicasWrite3,
                                     clientsRead0, clientsWrite4,
                                     clientsWrite5, lockedWrite2, spinRead0,
                                     msg_D, j_D, clientIdRead13, lockedRead1,
                                     clientIdRead14, clientIdRead15,
                                     clockWrite2, clockWrite3, replicasWrite4,
                                     replicasWrite5, spinLocal1, continue, j,
                                     msg, clientIdRead16, clockRead5,
                                     clientIdRead17, clockRead6,
                                     clientIdRead18, clockWrite4,
                                     clientIdRead19, clientIdRead20,
                                     clockRead7, replicasWrite6,
                                     replicasWrite7, spinRead1 >>

putCheckSpin(self) == /\ pc[self] = "putCheckSpin"
                      /\ spinRead0' = [spinRead0 EXCEPT ![self] = spinLocal0[self]]
                      /\ IF ~(spinRead0'[self])
                            THEN /\ continue_P' = [continue_P EXCEPT ![self] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "putLoop"]
                                 /\ UNCHANGED continue_P
                      /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                      cid, out, clocks, kvLocal, liveClients,
                                      pendingRequests, stableMessages, i_,
                                      firstPending, timestamp, nextClient,
                                      lowestPending, chooseMessage,
                                      currentClocks, minClock, continue_,
                                      pendingClients, clientsIter, msg_, ok,
                                      key, val, replicasRead, replicasWrite,
                                      kvRead, clientsWrite, clientsWrite0,
                                      kvWrite, kvWrite0, clientsWrite1,
                                      spinLocal, continue_G, getReq, getResp,
                                      clientIdRead, lockedRead, clientIdRead0,
                                      clockRead, clientIdRead1, lockedWrite,
                                      clientIdRead2, clockRead0, clientIdRead3,
                                      clockWrite, keyRead, clientIdRead4,
                                      clientIdRead5, clockRead1,
                                      replicasWrite0, clientsRead,
                                      clientsWrite2, outsideWrite,
                                      lockedWrite0, clockWrite0,
                                      replicasWrite1, clientsWrite3,
                                      outsideWrite0, spinRead, spinLocal0, i,
                                      j_, putReq, putResp, clientIdRead6,
                                      lockedRead0, clientIdRead7, clockRead2,
                                      clientIdRead8, clockRead3, clientIdRead9,
                                      clockWrite1, keyRead0, valueRead,
                                      clientIdRead10, clientIdRead11,
                                      clockRead4, clientIdRead12, lockedWrite1,
                                      replicasWrite2, replicasWrite3,
                                      clientsRead0, clientsWrite4,
                                      clientsWrite5, lockedWrite2,
                                      outsideWrite1, msg_D, j_D,
                                      clientIdRead13, lockedRead1,
                                      clientIdRead14, clientIdRead15,
                                      clockWrite2, clockWrite3, replicasWrite4,
                                      replicasWrite5, spinLocal1, continue, j,
                                      msg, clientIdRead16, clockRead5,
                                      clientIdRead17, clockRead6,
                                      clientIdRead18, clockWrite4,
                                      clientIdRead19, clientIdRead20,
                                      clockRead7, replicasWrite6,
                                      replicasWrite7, spinRead1 >>

PutClient(self) == putLoop(self) \/ putRequest(self) \/ putBroadcast(self)
                      \/ putResponse(self) \/ putComplete(self)
                      \/ putCheckSpin(self)

sendDisconnectRequest(self) == /\ pc[self] = "sendDisconnectRequest"
                               /\ clientIdRead13' = [clientIdRead13 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER))]
                               /\ ~(lock[clientIdRead13'[self]])
                               /\ lockedRead1' = [lockedRead1 EXCEPT ![self] = FALSE]
                               /\ IF ~(lockedRead1'[self])
                                     THEN /\ clientIdRead14' = [clientIdRead14 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER))]
                                          /\ msg_D' = [msg_D EXCEPT ![self] = [op |-> DISCONNECT_MSG, client |-> clientIdRead14'[self]]]
                                          /\ clientIdRead15' = [clientIdRead15 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (DISCONNECT_ORDER))]
                                          /\ clockWrite2' = [clockWrite2 EXCEPT ![self] = [clocks EXCEPT ![clientIdRead15'[self]] = -(1)]]
                                          /\ j_D' = [j_D EXCEPT ![self] = 0]
                                          /\ clockWrite3' = [clockWrite3 EXCEPT ![self] = clockWrite2'[self]]
                                          /\ clocks' = clockWrite3'[self]
                                     ELSE /\ clockWrite3' = [clockWrite3 EXCEPT ![self] = clocks]
                                          /\ clocks' = clockWrite3'[self]
                                          /\ UNCHANGED << msg_D, j_D,
                                                          clientIdRead14,
                                                          clientIdRead15,
                                                          clockWrite2 >>
                               /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                               /\ UNCHANGED << replicasNetwork, clientsNetwork,
                                               lock, cid, out, kvLocal,
                                               liveClients, pendingRequests,
                                               stableMessages, i_,
                                               firstPending, timestamp,
                                               nextClient, lowestPending,
                                               chooseMessage, currentClocks,
                                               minClock, continue_,
                                               pendingClients, clientsIter,
                                               msg_, ok, key, val,
                                               replicasRead, replicasWrite,
                                               kvRead, clientsWrite,
                                               clientsWrite0, kvWrite,
                                               kvWrite0, clientsWrite1,
                                               spinLocal, continue_G, getReq,
                                               getResp, clientIdRead,
                                               lockedRead, clientIdRead0,
                                               clockRead, clientIdRead1,
                                               lockedWrite, clientIdRead2,
                                               clockRead0, clientIdRead3,
                                               clockWrite, keyRead,
                                               clientIdRead4, clientIdRead5,
                                               clockRead1, replicasWrite0,
                                               clientsRead, clientsWrite2,
                                               outsideWrite, lockedWrite0,
                                               clockWrite0, replicasWrite1,
                                               clientsWrite3, outsideWrite0,
                                               spinRead, spinLocal0,
                                               continue_P, i, j_, putReq,
                                               putResp, clientIdRead6,
                                               lockedRead0, clientIdRead7,
                                               clockRead2, clientIdRead8,
                                               clockRead3, clientIdRead9,
                                               clockWrite1, keyRead0,
                                               valueRead, clientIdRead10,
                                               clientIdRead11, clockRead4,
                                               clientIdRead12, lockedWrite1,
                                               replicasWrite2, replicasWrite3,
                                               clientsRead0, clientsWrite4,
                                               clientsWrite5, lockedWrite2,
                                               outsideWrite1, spinRead0,
                                               replicasWrite4, replicasWrite5,
                                               spinLocal1, continue, j, msg,
                                               clientIdRead16, clockRead5,
                                               clientIdRead17, clockRead6,
                                               clientIdRead18, clockWrite4,
                                               clientIdRead19, clientIdRead20,
                                               clockRead7, replicasWrite6,
                                               replicasWrite7, spinRead1 >>

disconnectBroadcast(self) == /\ pc[self] = "disconnectBroadcast"
                             /\ IF (j_D[self]) <= ((NUM_REPLICAS) - (1))
                                   THEN /\ (Len(replicasNetwork[j_D[self]])) < (BUFFER_SIZE)
                                        /\ replicasWrite4' = [replicasWrite4 EXCEPT ![self] = [replicasNetwork EXCEPT ![j_D[self]] = Append(replicasNetwork[j_D[self]], msg_D[self])]]
                                        /\ j_D' = [j_D EXCEPT ![self] = (j_D[self]) + (1)]
                                        /\ replicasWrite5' = [replicasWrite5 EXCEPT ![self] = replicasWrite4'[self]]
                                        /\ replicasNetwork' = replicasWrite5'[self]
                                        /\ pc' = [pc EXCEPT ![self] = "disconnectBroadcast"]
                                   ELSE /\ replicasWrite5' = [replicasWrite5 EXCEPT ![self] = replicasNetwork]
                                        /\ replicasNetwork' = replicasWrite5'[self]
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << j_D, replicasWrite4 >>
                             /\ UNCHANGED << clientsNetwork, lock, cid, out,
                                             clocks, kvLocal, liveClients,
                                             pendingRequests, stableMessages,
                                             i_, firstPending, timestamp,
                                             nextClient, lowestPending,
                                             chooseMessage, currentClocks,
                                             minClock, continue_,
                                             pendingClients, clientsIter, msg_,
                                             ok, key, val, replicasRead,
                                             replicasWrite, kvRead,
                                             clientsWrite, clientsWrite0,
                                             kvWrite, kvWrite0, clientsWrite1,
                                             spinLocal, continue_G, getReq,
                                             getResp, clientIdRead, lockedRead,
                                             clientIdRead0, clockRead,
                                             clientIdRead1, lockedWrite,
                                             clientIdRead2, clockRead0,
                                             clientIdRead3, clockWrite,
                                             keyRead, clientIdRead4,
                                             clientIdRead5, clockRead1,
                                             replicasWrite0, clientsRead,
                                             clientsWrite2, outsideWrite,
                                             lockedWrite0, clockWrite0,
                                             replicasWrite1, clientsWrite3,
                                             outsideWrite0, spinRead,
                                             spinLocal0, continue_P, i, j_,
                                             putReq, putResp, clientIdRead6,
                                             lockedRead0, clientIdRead7,
                                             clockRead2, clientIdRead8,
                                             clockRead3, clientIdRead9,
                                             clockWrite1, keyRead0, valueRead,
                                             clientIdRead10, clientIdRead11,
                                             clockRead4, clientIdRead12,
                                             lockedWrite1, replicasWrite2,
                                             replicasWrite3, clientsRead0,
                                             clientsWrite4, clientsWrite5,
                                             lockedWrite2, outsideWrite1,
                                             spinRead0, msg_D, clientIdRead13,
                                             lockedRead1, clientIdRead14,
                                             clientIdRead15, clockWrite2,
                                             clockWrite3, spinLocal1, continue,
                                             j, msg, clientIdRead16,
                                             clockRead5, clientIdRead17,
                                             clockRead6, clientIdRead18,
                                             clockWrite4, clientIdRead19,
                                             clientIdRead20, clockRead7,
                                             replicasWrite6, replicasWrite7,
                                             spinRead1 >>

DisconnectClient(self) == sendDisconnectRequest(self)
                             \/ disconnectBroadcast(self)

clockUpdateLoop(self) == /\ pc[self] = "clockUpdateLoop"
                         /\ IF continue[self]
                               THEN /\ clientIdRead16' = [clientIdRead16 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (NULL_ORDER))]
                                    /\ clockRead5' = [clockRead5 EXCEPT ![self] = clocks[clientIdRead16'[self]]]
                                    /\ IF (clockRead5'[self]) = (-(1))
                                          THEN /\ continue' = [continue EXCEPT ![self] = FALSE]
                                               /\ pc' = [pc EXCEPT ![self] = "nullCheckSpin"]
                                               /\ UNCHANGED << clocks, j, msg,
                                                               clientIdRead17,
                                                               clockRead6,
                                                               clientIdRead18,
                                                               clockWrite4,
                                                               clientIdRead19,
                                                               clientIdRead20,
                                                               clockRead7 >>
                                          ELSE /\ clientIdRead17' = [clientIdRead17 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (NULL_ORDER))]
                                               /\ clockRead6' = [clockRead6 EXCEPT ![self] = clocks[clientIdRead17'[self]]]
                                               /\ clientIdRead18' = [clientIdRead18 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (NULL_ORDER))]
                                               /\ clockWrite4' = [clockWrite4 EXCEPT ![self] = [clocks EXCEPT ![clientIdRead18'[self]] = (clockRead6'[self]) + (1)]]
                                               /\ clientIdRead19' = [clientIdRead19 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (NULL_ORDER))]
                                               /\ clientIdRead20' = [clientIdRead20 EXCEPT ![self] = (self) - ((NUM_CLIENTS) * (NULL_ORDER))]
                                               /\ clockRead7' = [clockRead7 EXCEPT ![self] = clockWrite4'[self][clientIdRead20'[self]]]
                                               /\ msg' = [msg EXCEPT ![self] = [op |-> NULL_MSG, client |-> clientIdRead19'[self], timestamp |-> clockRead7'[self]]]
                                               /\ j' = [j EXCEPT ![self] = 0]
                                               /\ clocks' = clockWrite4'[self]
                                               /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                                               /\ UNCHANGED continue
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << clocks, continue, j, msg,
                                                    clientIdRead16, clockRead5,
                                                    clientIdRead17, clockRead6,
                                                    clientIdRead18,
                                                    clockWrite4,
                                                    clientIdRead19,
                                                    clientIdRead20, clockRead7 >>
                         /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                         cid, out, kvLocal, liveClients,
                                         pendingRequests, stableMessages, i_,
                                         firstPending, timestamp, nextClient,
                                         lowestPending, chooseMessage,
                                         currentClocks, minClock, continue_,
                                         pendingClients, clientsIter, msg_, ok,
                                         key, val, replicasRead, replicasWrite,
                                         kvRead, clientsWrite, clientsWrite0,
                                         kvWrite, kvWrite0, clientsWrite1,
                                         spinLocal, continue_G, getReq,
                                         getResp, clientIdRead, lockedRead,
                                         clientIdRead0, clockRead,
                                         clientIdRead1, lockedWrite,
                                         clientIdRead2, clockRead0,
                                         clientIdRead3, clockWrite, keyRead,
                                         clientIdRead4, clientIdRead5,
                                         clockRead1, replicasWrite0,
                                         clientsRead, clientsWrite2,
                                         outsideWrite, lockedWrite0,
                                         clockWrite0, replicasWrite1,
                                         clientsWrite3, outsideWrite0,
                                         spinRead, spinLocal0, continue_P, i,
                                         j_, putReq, putResp, clientIdRead6,
                                         lockedRead0, clientIdRead7,
                                         clockRead2, clientIdRead8, clockRead3,
                                         clientIdRead9, clockWrite1, keyRead0,
                                         valueRead, clientIdRead10,
                                         clientIdRead11, clockRead4,
                                         clientIdRead12, lockedWrite1,
                                         replicasWrite2, replicasWrite3,
                                         clientsRead0, clientsWrite4,
                                         clientsWrite5, lockedWrite2,
                                         outsideWrite1, spinRead0, msg_D, j_D,
                                         clientIdRead13, lockedRead1,
                                         clientIdRead14, clientIdRead15,
                                         clockWrite2, clockWrite3,
                                         replicasWrite4, replicasWrite5,
                                         spinLocal1, replicasWrite6,
                                         replicasWrite7, spinRead1 >>

nullCheckSpin(self) == /\ pc[self] = "nullCheckSpin"
                       /\ spinRead1' = [spinRead1 EXCEPT ![self] = spinLocal1[self]]
                       /\ IF ~(spinRead1'[self])
                             THEN /\ continue' = [continue EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "clockUpdateLoop"]
                                  /\ UNCHANGED continue
                       /\ UNCHANGED << replicasNetwork, clientsNetwork, lock,
                                       cid, out, clocks, kvLocal, liveClients,
                                       pendingRequests, stableMessages, i_,
                                       firstPending, timestamp, nextClient,
                                       lowestPending, chooseMessage,
                                       currentClocks, minClock, continue_,
                                       pendingClients, clientsIter, msg_, ok,
                                       key, val, replicasRead, replicasWrite,
                                       kvRead, clientsWrite, clientsWrite0,
                                       kvWrite, kvWrite0, clientsWrite1,
                                       spinLocal, continue_G, getReq, getResp,
                                       clientIdRead, lockedRead, clientIdRead0,
                                       clockRead, clientIdRead1, lockedWrite,
                                       clientIdRead2, clockRead0,
                                       clientIdRead3, clockWrite, keyRead,
                                       clientIdRead4, clientIdRead5,
                                       clockRead1, replicasWrite0, clientsRead,
                                       clientsWrite2, outsideWrite,
                                       lockedWrite0, clockWrite0,
                                       replicasWrite1, clientsWrite3,
                                       outsideWrite0, spinRead, spinLocal0,
                                       continue_P, i, j_, putReq, putResp,
                                       clientIdRead6, lockedRead0,
                                       clientIdRead7, clockRead2,
                                       clientIdRead8, clockRead3,
                                       clientIdRead9, clockWrite1, keyRead0,
                                       valueRead, clientIdRead10,
                                       clientIdRead11, clockRead4,
                                       clientIdRead12, lockedWrite1,
                                       replicasWrite2, replicasWrite3,
                                       clientsRead0, clientsWrite4,
                                       clientsWrite5, lockedWrite2,
                                       outsideWrite1, spinRead0, msg_D, j_D,
                                       clientIdRead13, lockedRead1,
                                       clientIdRead14, clientIdRead15,
                                       clockWrite2, clockWrite3,
                                       replicasWrite4, replicasWrite5,
                                       spinLocal1, j, msg, clientIdRead16,
                                       clockRead5, clientIdRead17, clockRead6,
                                       clientIdRead18, clockWrite4,
                                       clientIdRead19, clientIdRead20,
                                       clockRead7, replicasWrite6,
                                       replicasWrite7 >>

nullBroadcast(self) == /\ pc[self] = "nullBroadcast"
                       /\ IF (j[self]) <= ((NUM_REPLICAS) - (1))
                             THEN /\ (Len(replicasNetwork[j[self]])) < (BUFFER_SIZE)
                                  /\ replicasWrite6' = [replicasWrite6 EXCEPT ![self] = [replicasNetwork EXCEPT ![j[self]] = Append(replicasNetwork[j[self]], msg[self])]]
                                  /\ j' = [j EXCEPT ![self] = (j[self]) + (1)]
                                  /\ replicasWrite7' = [replicasWrite7 EXCEPT ![self] = replicasWrite6'[self]]
                                  /\ replicasNetwork' = replicasWrite7'[self]
                                  /\ pc' = [pc EXCEPT ![self] = "nullBroadcast"]
                             ELSE /\ replicasWrite7' = [replicasWrite7 EXCEPT ![self] = replicasNetwork]
                                  /\ replicasNetwork' = replicasWrite7'[self]
                                  /\ pc' = [pc EXCEPT ![self] = "nullCheckSpin"]
                                  /\ UNCHANGED << j, replicasWrite6 >>
                       /\ UNCHANGED << clientsNetwork, lock, cid, out, clocks,
                                       kvLocal, liveClients, pendingRequests,
                                       stableMessages, i_, firstPending,
                                       timestamp, nextClient, lowestPending,
                                       chooseMessage, currentClocks, minClock,
                                       continue_, pendingClients, clientsIter,
                                       msg_, ok, key, val, replicasRead,
                                       replicasWrite, kvRead, clientsWrite,
                                       clientsWrite0, kvWrite, kvWrite0,
                                       clientsWrite1, spinLocal, continue_G,
                                       getReq, getResp, clientIdRead,
                                       lockedRead, clientIdRead0, clockRead,
                                       clientIdRead1, lockedWrite,
                                       clientIdRead2, clockRead0,
                                       clientIdRead3, clockWrite, keyRead,
                                       clientIdRead4, clientIdRead5,
                                       clockRead1, replicasWrite0, clientsRead,
                                       clientsWrite2, outsideWrite,
                                       lockedWrite0, clockWrite0,
                                       replicasWrite1, clientsWrite3,
                                       outsideWrite0, spinRead, spinLocal0,
                                       continue_P, i, j_, putReq, putResp,
                                       clientIdRead6, lockedRead0,
                                       clientIdRead7, clockRead2,
                                       clientIdRead8, clockRead3,
                                       clientIdRead9, clockWrite1, keyRead0,
                                       valueRead, clientIdRead10,
                                       clientIdRead11, clockRead4,
                                       clientIdRead12, lockedWrite1,
                                       replicasWrite2, replicasWrite3,
                                       clientsRead0, clientsWrite4,
                                       clientsWrite5, lockedWrite2,
                                       outsideWrite1, spinRead0, msg_D, j_D,
                                       clientIdRead13, lockedRead1,
                                       clientIdRead14, clientIdRead15,
                                       clockWrite2, clockWrite3,
                                       replicasWrite4, replicasWrite5,
                                       spinLocal1, continue, msg,
                                       clientIdRead16, clockRead5,
                                       clientIdRead17, clockRead6,
                                       clientIdRead18, clockWrite4,
                                       clientIdRead19, clientIdRead20,
                                       clockRead7, spinRead1 >>

ClockUpdateClient(self) == clockUpdateLoop(self) \/ nullCheckSpin(self)
                              \/ nullBroadcast(self)

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
                            alive == { c \in ClientSet : clocks[c] > 0 }
                        IN
                            Len(stable) > 0 =>
                                \A m_id \in DOMAIN stable :
                                    \A client \in alive : stable[m_id].timestamp < clocks[client]


\* Put semantics: once a client has been notified that a Put request was succesful
\* every replica must have the updated value.
PersistentPut == \A client \in PutSet :
                     pc[client] = "putComplete" => \A replica \in ReplicaSet : kvLocal[replica][PUT_KEY] = PUT_VALUE


\* Properties
\* **********

\* Logical clocks are monotonically increasing. This property checks that in every state,
\* pending messages in the replicas have increasing timestamps (or the process disconnected)
ClockIncreased == clocks' /= clocks =>
                 \E c \in ClientSet : clocks'[c] = clocks[c]+1 \/ clocks'[c] = -1

MonotonicallyIncreasingClocks == [][ClockIncreased]_<<clocks>>


\* Safety of disconnection: once a client has disconnected (and sent a message to all replicas
\* informing of that event), then the logical clock of that client should remain
\* unchanced -- i.e., no more messages from that client should be seen in the system.
DisconnectionSafe == \A client \in ClientSet : <>[](clocks[client] = -1)

=============================================================================
\* Modification History
\* Last modified Mon Apr 01 14:41:36 PDT 2019 by rmc
\* Last modified Wed Feb 27 12:42:52 PST 2019 by minh
