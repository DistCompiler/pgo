-------------------------------- MODULE aworset --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(*

--mpcal aworset {

variables v;

\* this is a test of multi-assignment, specifically compound expressions

process (P = 1) {
lbl:
    v[0] := 1;
    if(TRUE) {
        v[1] := 2;
        v[2] := 3;
    };
    if(TRUE) {
        v[3] := 4;
        v[4] := 5;
        v[5] := 6;
    };
}

}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION

====
