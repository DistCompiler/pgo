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
