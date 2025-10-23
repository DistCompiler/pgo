---- MODULE MCConcurrentQueueAPI ----
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
    IN  IF "prodToken" \in DOMAIN __rec.operation
        THEN {__rec.operation.prodToken}
        ELSE IF "consToken" \in DOMAIN __rec.operation
        THEN {__rec.operation.consToken}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"ThreadsImpl"})


DebugAlias == __TraceOps!DebugAlias

TypeOK == __Spec!TypeOK
QueueInvariant == __Spec!QueueInvariant
NoLostElements == __Spec!NoLostElements

PragmaticView ==
    [
        __pc |-> __pc,                          
        queue_len |-> Len(queue)
    ]

====

