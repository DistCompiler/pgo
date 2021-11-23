---- MODULE ResourceAccessBoundByWith ----
EXTENDS TLC, Integers

(*
--mpcal ResourceAccessBoundByWith {

mapping macro MM {
    read {
        with (foo = $variable + 1) {
            yield foo;
        };
    }
    write {
        yield $value;
    }
}

archetype AFoo(ref x)
    variables z;
{
lbl:
    either {
        with(y = x) {
            print y;
        };
    } or {
        skip;
    };
    goto lbl;
}

variables x;

process (Foo = 1) == instance AFoo(ref x)
    mapping x via MM;
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION
*)

\* BEGIN TRANSLATION
====
