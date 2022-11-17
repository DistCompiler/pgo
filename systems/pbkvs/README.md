# pvkvs

A key-value store that uses primary-backup replication. We used the following
document as the reference:
http://www.sc.ehu.es/acwlaalm/sdi/replication-schemas.pdf

Assumptions:
- Crash-stop failure model
- Having access to a perfect failure detector

In each step of the execution, we consider a replica as the primary that has the
lowest ID amongst all alive replicas. Primary synchronously replicates requests
to the backup nodes. Clients must send write requests only to the primary
replica. The primary always has the same state as backups or the primary is one
step ahead.  Therefore, reading from a backup might return an old value. In this
spec, read requests are sent only to the primary.

If the primary node fails while processing a write request, the client won't
receive any response back. If the primary replicated the write request to at
least one backup node, the request will be applied to the system, otherwise, it
won't. Therefore, the system provides no guarantee when a client don't receive a
response for its write request. However, it's fine since the client retries and
all operations are idempotent.

We define consistency property for this system as: when primary node sends a
response back to a client, all replicas (including primary) have a same state.
