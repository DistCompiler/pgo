---- MODULE MPCalInstanceClauseSelf ----
EXTENDS Sequences, TLC, FiniteSets

(*
--mpcal MPCalInstanceClauseSelf {
    archetype Foo(x) {
        lbl: skip;
    }

    process (Bar = 42) == instance Foo(Bar);
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION

====