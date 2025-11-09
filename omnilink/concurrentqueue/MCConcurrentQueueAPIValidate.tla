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

ThreadsImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
        __op == __rec.operation
        __threads ==
            (IF "thread" \in DOMAIN __op /\ __op.thread # "null" /\ __op.thread \in Int
             THEN {__op.thread}
             ELSE {}) \cup
            (IF "prodToken" \in DOMAIN __op /\ __op.prodToken # "null" /\ __op.prodToken \in Int
             THEN {__op.prodToken}
             ELSE {}) \cup
            (IF "consToken" \in DOMAIN __op /\ __op.consToken # "null" /\ __op.consToken \in Int
             THEN {__op.consToken}
             ELSE {})
    IN  __threads
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

