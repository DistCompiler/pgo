---- MODULE MCConcurrentQueueValidate ----
EXTENDS ConcurrentQueueValidate, TLC, TLCExt

ProducersImpl == TLCCache(
  UNION UNION {
    {
      LET __rec == __traces[t][i]
          __op == __rec.operation
      IN  IF "producer" \in DOMAIN __op
          THEN { __op.producer }
          ELSE {}
    : i \in DOMAIN __traces[t] }
  : t \in DOMAIN __traces }, {})
        
DebugAlias == __TraceOps!DebugAlias @@ [
    Producers |-> Producers
]
PostCondition == __TraceOps!PostCondition

StopAtLevel ==
    TLCGet("level") # 64

PragmaticView == [
    __pc |-> __pc,
    queues |-> queues,
    \* Don't need to remember the actual sizeApproxMax structure, just
    \* when its max changes.
    SizeApproxMax |-> __Spec!SizeApproxMax
]

====

