---- MODULE MPCalKindMatching ----
EXTENDS Sequences, FiniteSets, Integers
(*
--mpcal MPCalKindMatching {
    procedure Proc(ref a[_]) {
        l2: call Proc((*:: expectedError: MPCalKindMismatchError *) a);
        l4: call Proc2(ref a[_]);
        l5: a[2] := 3;
        l3: (*:: expectedError: MPCalKindMismatchError *) a := 3;
        l6: a[5][6] := 3;
    }

    procedure Proc2(ref b[_][_]) {
        l3: skip;
    }

    archetype Arch(ref a[_]) {
        l1: skip;
    }

    variables myVar;

    process (A = 42) == instance Arch((*:: expectedError: MPCalKindMismatchError *) myVar[_]);

    process (B = 43) == instance Arch((*:: expectedError: MPCalKindMismatchError *) ref myVar);

    process (C = 44) == instance Arch((*:: expectedError: MPCalKindMismatchError *) myVar);

    process (D = 45) == instance Arch((*:: expectedError: MPCalKindMismatchError *) ref myVar[_][_]);
}
*)
\* BEGIN TRANSLATION
====