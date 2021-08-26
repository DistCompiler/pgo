---- MODULE MPCalScopeBleed ----
EXTENDS TLC, Integers

(* --mpcal MPCalScopeBleed {

archetype Arch() {
    lbl3: skip;
}

procedure P1(x)
    variables y;
{
    lbl1:
        x := y + z;
}

process (P2 = 1)
    variables z;
{
    lbl2:
        x := y + z;
}

} *)

(*

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)


\* BEGIN TRANSLATION
====