---- MODULE UnsupportedOps ----
EXTENDS Sequences, FiniteSets, Integers, Bags

MyOperator == (*:: expectedError: UnsupportedOperationError *) SetToBag({})

(*
--mpcal NoFirstLabel {
    define {
        MyOperator2 == (*:: expectedError: UnsupportedOperationError *) SetToBag({})
    }

    procedure MPCalProc(a) {
        lbl: a := (*:: expectedError: UnsupportedOperationError *) SetToBag({});
    }
    archetype MyArchetype(ref a) {
        lbl: a := (*:: expectedError: UnsupportedOperationError *) SetToBag({});
    }
    procedure PCalProc(a) {
        lbl: a := SetToBag({});
    }

    process (Proc = 1)
    variable a;
    {
        lbl: a := SetToBag({});
    }
}
*)
\* BEGIN TRANSLATION
====