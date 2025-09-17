---- MODULE bug3_127 ----
EXTENDS TLC, Naturals

CONSTANT NUM_NODES

(* --mpcal bug3 {
    macro mayFail() {
        if ((*:: expectedError: UnboundFreeVariableError *) EXPLORE_FAIL) {
            either {
                skip;
            } or {
                goto fail;
            };
        };
    };

    archetype AFoo() {
        start:
            mayFail();

        program:
            print("program");
            goto start;

        fail:
            print("fail");
    }

    fair process (Foo \in 1..NUM_NODES) == instance AFoo();
} *)

\* BEGIN TRANSLATION

====