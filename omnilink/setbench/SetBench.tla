---- MODULE SetBench ----
EXTENDS FiniteSets, Integers

CONSTANTS Keys, Values, Counts, NoValue

Dicts == UNION { [ks -> Values] : ks \in SUBSET Keys }

VARIABLES dict

vars == <<dict>>

TypeOK ==
    /\ dict \in Dicts

KVContains(key, result) ==
    /\ IF   key \in DOMAIN dict
       THEN result = TRUE
       ELSE result = FALSE
    /\ UNCHANGED vars

KVInsert(key, value, result) ==
    /\ IF   key \in DOMAIN dict
       THEN result = dict[key]
       ELSE result = NoValue
    /\ dict' = [k \in DOMAIN dict \cup {key} |->
                IF k = key
                THEN value
                ELSE dict[k]]

KVInsertIfAbsent(key, value, result) ==
    IF   key \notin DOMAIN dict
    THEN KVInsert(key, value, result)
    ELSE /\ result = dict[key]
         /\ UNCHANGED vars

KVErase(key, result) ==
    /\ IF   key \in DOMAIN dict
       THEN result = dict[key]
       ELSE result = NoValue
    /\ dict' = [k \in DOMAIN dict \ {key} |-> dict[k] ]

KVRangeQuery(lo, hi, count) ==
    /\ count = Cardinality({ k \in DOMAIN dict :
            /\ lo <= k
            /\ k <= hi
       })
    /\ UNCHANGED vars

Init ==
    /\ dict = <<>>

Next ==
    \/ \E key \in Keys, result \in BOOLEAN :
        KVContains(key, result)
    \/ \E key \in Keys, value \in Values, result \in Values \cup {NoValue} :
        \/ KVInsert(key, value, result)
        \/ KVInsertIfAbsent(key, value, result)
    \/ \E key \in Keys, result \in Values \cup {NoValue} :
        KVErase(key, result)
    \/ \E lo, hi \in Keys, count \in Counts :
        KVRangeQuery(lo, hi, count)

====