---- MODULE MCSetBenchValidate ----
EXTENDS SetBenchValidate, TLC, TLCExt

KeysImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  CASE "key" \in DOMAIN __rec.operation -> {__rec.operation.key}
          [] {"lo", "hi"} \subseteq DOMAIN __rec.operation -> {__rec.operation.lo, __rec.operation.hi}
          [] OTHER -> {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"KeysImpl"})

ValuesImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  CASE "value" \in DOMAIN __rec.operation -> {__rec.operation.value}
          [] OTHER -> {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"KeysImpl"})

CountsImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  CASE "count" \in DOMAIN __rec.operation -> {__rec.operation.count}
          [] OTHER -> {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"KeysImpl"})

DebugAlias == __TraceOps!DebugAlias
PostCondition == __TraceOps!PostCondition

__TAG_WrongRangeQueryCount(pid, op) ==
    /\ op.operation_name = "KVRangeQuery"
    /\ \lnot __Spec!KVRangeQuery(op.operation.lo, op.operation.hi, op.operation.count)

====