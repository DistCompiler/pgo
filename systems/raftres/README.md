# raftres

raftres is a modular composition of the pure Raft protocol and a naive
distributed key-value store. This system demonstrates the modular verification
and composition of PGo-based systems.

## Model

raftres is composed of two models: `raft` and `kv`. `raft` is a pure Raft
protocol without any client interaction semantics. `kv` is a distributed
key-value store that assumes it has access on an abstract consensus layer.

In the composition, `raft` and `kv` communicate using accept and propose
channels. Each `raft` server accepts new request through its accept channel and
broadcasts committed log entries through its propose channel. `kv` leverages these
channels and implements a key-value store using them.

### Assumptions

Both `raft` and `kv` make the same assumptions as the [raftkvs](/systems/raftkvs/) systems.

### Properties

`raft` only has the five properties from the Raft protocol.