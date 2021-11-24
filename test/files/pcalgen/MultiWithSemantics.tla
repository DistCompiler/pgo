---- MODULE MultiWithSemantics ----
EXTENDS TLC, Integers, Sequences

(* --mpcal MultiWithSemantics {

mapping macro Inc {
    read {
        with(v = $variable) {
            $variable := $variable + 1;
            yield v;
        };
    }
    write {
        assert FALSE;
    }
}

archetype AnExample(ref foo) {
lbl:
    with(x = foo, y = foo + x) {
        print y;
    };
}

variables gFoo = 0;

fair process (Example = 1) == instance AnExample(ref gFoo)
    mapping gFoo via Inc;

} *)

(*

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====