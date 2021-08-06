---- MODULE InvalidAssignment ----
EXTENDS Integers, Sequences, TLC, FiniteSets, Peano

(* --mpcal InvalidAssignment {
    archetype Ping() {
        lbl: (*:: expectedError: PCalInvalidAssignment *) FALSE := TRUE;
    }

    procedure Bar() {
        lbl: (*:: expectedError: PCalInvalidAssignment *) TRUE := FALSE;
    }

    process (Foo = 0) {
        lbl: (*:: expectedError: PCalInvalidAssignment *) BOOLEAN := TRUE;
    }
}
*)

\* BEGIN TRANSLATION
====