---- MODULE MPCalKindMatching ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MPCalKindMatching {
    procedure Proc(ref a[_]) {
        l2: call Proc(a);
    }

    archetype Arch(ref a[_]) {
        l1: skip;
    }

    variables myVar;

    process (A = 42) == instance Arch(myVar[_]);

    process (B = 43) == instance Arch(ref myVar);

    process (C = 44) == instance Arch(myVar);
}
*)
\* BEGIN TRANSLATION
====