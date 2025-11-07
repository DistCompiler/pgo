---- MODULE MCRefLockingValidate ----
EXTENDS RefLockingValidate, Sequences, TLC, TLCExt, FiniteSets

\* OwnersImpl == TLCCache(UNION UNION { {
\*     LET __rec == __traces[t][i]
\*     IN  IF "owner" \in DOMAIN __rec.operation
\*         THEN {__rec.operation.owner}
\*         ELSE {}
\*     : i \in DOMAIN __traces[t] }
\*     : t \in DOMAIN __traces }, {})

\* LocksImpl == TLCCache(UNION UNION { {
\*     LET __rec == __traces[t][i]
\*     IN  IF "lock" \in DOMAIN __rec.operation
\*         THEN {__rec.operation.lock}
\*         ELSE {}
\*     : i \in DOMAIN __traces[t] }
\*     : t \in DOMAIN __traces }, {})

OwnersImpl == {} \* unused
LocksImpl == {} \* unused

\* ASSUME PrintT([
\*     owners |-> Cardinality(Owners),
\*     locks |-> Cardinality(Locks),
\*     traceLens |-> [pid \in DOMAIN __TraceOps!traces |-> Len(__TraceOps!traces[pid])]
\* ])

PostCondition == __TraceOps!PostCondition

====