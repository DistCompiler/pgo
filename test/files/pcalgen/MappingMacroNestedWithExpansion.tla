---- MODULE MappingMacroNestedWithExpansion ----
EXTENDS Sequences, FiniteSets, Integers

(* --mpcal MappingMacroNestedWithExpansion {

mapping macro IdentityWith {
    read {
        with (x = $variable) {
            yield x;
        }
    }
    write {
        with (y = $value) {
            yield y;
        }
    }
}

archetype Arch(ref foo) {
    lbl:
    foo := foo + 1;
    foo := 2 + foo;
}

variable bar;

process (Proc = 1) == instance Arch(ref bar)
    mapping bar via IdentityWith;

} *)

(*
\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION

====