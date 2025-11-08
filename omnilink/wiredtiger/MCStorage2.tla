---- MODULE MCStorage2 ----
EXTENDS Storage2

Storage == INSTANCE Storage

IsRefinedByStorage ==
    [][Next]_vars

RefinementSpec ==
    Storage!Init /\ [][Storage!Next]_vars

StateConstraint ==
    /\ Len(mlog["n"]) <= 3

====
