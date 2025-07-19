---- MODULE MCStorageValidate ----
EXTENDS TLC, IOUtils, Sequences, Integers

\* FIXME: put this all back how it was, this variation doesn't even fix the issue!

CONSTANTS Node, RC
VARIABLES mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs

VARIABLES __pc, __viable_pids, __action

NoValue == -1

__traces == IODeserialize(Print("load", "StorageValidateData.bin"), FALSE)

Timestamps == {} \* stub, we don't use it

Keys == UNION UNION { {
    LET __rec == __traces[t][i]
    IN  Print("key", IF "k" \in DOMAIN __rec.operation
        THEN {__rec.operation.k}
        ELSE {})
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }

MTxId == UNION UNION { {
    LET __rec == __traces[t][i]
    IN  Print("txid", IF "tid" \in DOMAIN __rec.operation
        THEN {__rec.operation.tid}
        ELSE {})
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }

INSTANCE StorageValidate

DebugAlias == __TraceOps!DebugAlias

====