# Systems

This directory contains the systems built using PGo.
Each system has the MPCal model, generated Go code and handwritten Go code for bootstrapping the system.

Here is the list of systems and a short description of each:

- `dqueue` demonstrates a simple distributed queue, where producers and consumers communicate through the queue.
- `gcounter` is a grow-only counter CRDT.
- `loadbalancer` has a load balancer node that distributes incoming client requests to backend servers.
- `locksvc` is a simple lock service system.
- `nestedcrdtimpl` is generic CRDT-based system where the CRDT resource is built using PGo and MPCal. This system demonstrates the idea of verified resources.
- `proxy` is fault-tolerant proxy server. It sends the incoming requests to backend servers, and it can tolerate back-end servers failures.
- `raftkvs` is a monolithic key-value store based on the Raft consensus protocol.
- `raftres` is a modular composition of the pure Raft protocol and a naive distributed key-value store. This system demonstrates the modular verification and composition of PGo-based systems.
- `replicatedkv` is a legacy replicated key-value store.
- `shcounter` is a shared counter that shows the usage of 2PC-based shared resource.
- `shopcart` is a CRDT-based set.