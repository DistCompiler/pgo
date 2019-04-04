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

  mapping macro IsUnlocked {
      read {
          await ~$variable;
          yield TRUE;
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
  archetype Get(clientId, ref replicas, clients, key, ref unlocked, ref clock, spin, ref outside)
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
      mapping lock[_] via IsUnlocked
      mapping clocks[_] via Identity;

  fair process (PutClient \in PutSet) == instance Put(cid, ref replicasNetwork, clientsNetwork, PUT_KEY, PUT_VALUE, ref lock, ref clocks, TRUE, ref out)
      mapping cid via PutClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clientsNetwork[_] via FIFOChannel
      mapping lock[_] via IsUnlocked
      mapping clocks[_] via Identity;

  fair process (DisconnectClient \in DisconnectSet) == instance Disconnect(cid, ref replicasNetwork, lock, ref clocks)
      mapping cid via DisconnectClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping lock[_] via IsUnlocked
      mapping clocks[_] via Identity;

  fair process (ClockUpdateClient \in NullSet) == instance ClockUpdate(cid, ref replicasNetwork, ref clocks, TRUE)
      mapping cid via NullClientId
      mapping replicasNetwork[_] via FIFOChannel
      mapping clocks[_] via Identity;
}
