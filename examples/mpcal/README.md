# Raft MPCal Spec
## Model Checking Values
* Slots - a bound on the number of values to decide on
* N - the number of nodes
* NULL - default value (should not be anything that could appear in the spec)
* Terms - a bound on the number of terms
* BUFFER_SIZE - a bound on the number of in-flight messages (per mailbox)
* Follower - uniquely identifies the follower state
* Leader - uniquely identifies the leader state
* Candidate - uniquely identifies the candidate state
* Steps - how often to send heartbeats

Reccomended values are: [Slots <- 2, N <- 3, NULL <- -1, Terms <- 3, BUFFER_SIZE <- 3, Follower <- 0, Leader <- 2, Candidate <- 1, Steps <- 2].

There are two mapping macros for the network, FIFOQueues, which guarantees all messages are reliably delivered in order (for model checking correctness, termination, and liveness under perfect network conditions), and UnstableFIFOQueues, where messages can be dropped, duplicated, or reordered (for model checking correctness in the presence of failures).

The following State Constraint ensures no errors and proper timeout behavior:
`((\E s \in Servers: state[s] = Leader) \/ timeoutRead = TRUE \/ timeoutRead = defaultInitValue) /\ (\A s \in Servers: Len(mailboxes[s])<BUFFER_SIZE /\ Len(log[s]) < Slots /\ currentTerm[s] < Terms)`.

The invariants you want to check are:
* `Election Safety`: at most one leader can be elected in a given term.
* `Leader Append-Only`: a leader never overwrites or deletes entries in its log; it only appends new entries.
* `Log Matching`: if two logs contain an entry with the same index and term, then the logs are identical in all entries up through the given index.
* `Leader Completeness`: if a log entry is committed in a given term, then that entry will be present in the logs of the leaders for all higher-numbered terms.
* `State Machine Safety`: if a server has applied a log entry at a given index to its state machine, no other server will ever apply a different log entry for the same index.

## Spec Details
The spec is largely based on figure 5 of the raft paper: https://www.usenix.org/system/files/conference/atc14/atc14-paper-ongaro.pdf. Nodes should behave and handle messages as described in that behavior.

# Paxos Key-Value Store MPCal Spec

There are six model checking constants at present:

* **NUM_NODES**: number of nodes in the system. Each node consists of a
  proposer, acceptor, learner, and key-value layer.

* **BUFFER_SIZE**: network buffer size.

* **NULL**: Non-natural constant. `-1` is a valid choice.

* **GetSet**, **PutSet**: set of keys for which Get and Put requests will be
  made, respectively.

* **MAX_FAILURES**: maximum number of failures (triggering leader election)
  that will be simulated.

Under advanced options, put the following as a state constraint:

```
\E kv1, kv2 \in KVRequests, k \in PutSet : database[kv1, k] = NULL \/ database[kv2, k] = NULL
```

This bounds state exploration to states where at least one entry in one
key-value store has not been set yet. If the spec is correct, eventually all
entries in all nodes will be non-NULL.

Invariants:

* `ConsistentDatabase`

## Spec Details

There are three archetypes based off the thee node roles in Paxos Made Simple.

* Proposers - try to become elected leader by acquiring promises from a
  majority of acceptors, propose values to be accepted once they are leader

* Acceptors - respond to valid prepare messages with promises and inform nodes
  about the highest accepted values for each slot. Accept valid proposed values
  by adding it to list of highest accepted values and sending accept messages
  to the proposer who proposed the value and every learner.

* Learners - listen for accept messages, apply values to state machine (log
  archetype parameter) when chosen (majority of acceptors have agreed)
