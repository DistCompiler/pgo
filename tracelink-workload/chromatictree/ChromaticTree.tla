---- MODULE ChromaticTree ----
EXTENDS FiniteSets, Integers

CONSTANTS Keys, Values, Counts

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

KVInsert(key, value) ==
    dict' = [k \in DOMAIN dict \cup {key} |->
                IF k = key
                THEN value
                ELSE dict[k]]

KVInsertIfAbsent(key, value) ==
    IF   key \notin DOMAIN dict
    THEN KVInsert(key, value)
    ELSE UNCHANGED vars

KVErase(key) ==
    dict' = [k \in DOMAIN dict \ {key} |-> dict[k] ]

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
    \/ \E key \in Keys, value \in Values :
        \/ KVInsert(key, value)
        \/ KVInsertIfAbsent(key, value)
    \/ \E key \in Keys :
        KVErase(key)
    \/ \E lo, hi \in Keys, count \in Counts :
        KVRangeQuery(lo, hi, count)

====