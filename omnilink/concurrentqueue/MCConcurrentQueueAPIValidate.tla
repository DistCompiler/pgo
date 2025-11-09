---- MODULE MCConcurrentQueueAPIValidate ----
EXTENDS ConcurrentQueueAPIValidate, TLC, TLCExt, Sequences, FiniteSets

ElementsImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  IF "element" \in DOMAIN __rec.operation
        THEN {__rec.operation.element}
        ELSE IF "elements" \in DOMAIN __rec.operation
        THEN {__rec.operation.elements[j] : j \in DOMAIN __rec.operation.elements}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"ElementsImpl"})

ThreadsImpl == TLCCache(
  UNION UNION {
    {
      LET __rec == __traces[t][i]
          __op == __rec.operation
          __threads ==
            (IF "thread" \in DOMAIN __op
             THEN IF __op.thread \in Int THEN {__op.thread} ELSE {} ELSE {}) \cup
            (IF "prodToken" \in DOMAIN __op
             THEN IF __op.prodToken \in Int THEN {__op.prodToken} ELSE {} ELSE {}) \cup
            (IF "consToken" \in DOMAIN __op
             THEN IF __op.consToken \in Int THEN {__op.consToken} ELSE {} ELSE {})
            \* (IF "producer_threads" \in DOMAIN __op._meta
            \*  THEN LET __producers == __op._meta["producer_threads"]
            \*       IN IF __producers \in Seq(Int)
            \*          THEN { __producers[k] : k \in DOMAIN __producers }
            \*          ELSE {}
            \*  ELSE {})
      IN __threads
    : i \in DOMAIN __traces[t] }
  : t \in DOMAIN __traces }, {"ThreadsImpl"})


DebugAlias == __TraceOps!DebugAlias
PostCondition == __TraceOps!PostCondition

TypeOK == __Spec!TypeOK
QueueInvariant == __Spec!QueueInvariant
NoLostElements == __Spec!NoLostElements

(* PragmaticView ==
    [
        __pc |-> __pc,
        queue_len |-> Len(queue)
    ]
*)

====

