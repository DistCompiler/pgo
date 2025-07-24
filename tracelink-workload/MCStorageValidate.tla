---- MODULE MCStorageValidate ----
EXTENDS StorageValidate, TLC, TLCExt

TimestampsImpl == {} \* stub, we don't use it
SymmetryImpl == {} \* also stub

KeysImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  IF "k" \in DOMAIN __rec.operation
        THEN {__rec.operation.k}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"KeysImpl"})

MTxIdImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  IF "tid" \in DOMAIN __rec.operation
        THEN {__rec.operation.tid}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"MtxIdImpl"})

NoValueImpl == -1

DebugAlias == __TraceOps!DebugAlias

====