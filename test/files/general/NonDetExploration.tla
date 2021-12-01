---- MODULE NonDetExploration ----

(*

--mpcal NonDetExploration {

define {
    TheSet == {1, 2}
}

archetype ACoverage() {
l1:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 1;
    };
l2:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 2;
    };
l3:
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 1;
    };
l4:
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 2;
    };
}

archetype ACoincidence() {
lbl:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 1;
    };
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 2;
    };
}

process (Coverage = 1) == instance ACoverage();

process (Coincidence = 2) == instance ACoincidence();

}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====