---- MODULE StringBracketBug ----

(*

--mpcal StringBracketBug {
    archetype Foo() {
        lbl: print "a string (with brackets)";
    }

    process (Bar = 1) == instance Foo();
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====