---- MODULE ModuleWithoutExtends ----

Foo == 1

(* --mpcal ModuleWithoutExtends {

process (Nil = 0) {
    lbl: skip;
}
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====