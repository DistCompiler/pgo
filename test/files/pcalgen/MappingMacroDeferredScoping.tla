---- MODULE MappingMacroDeferredScoping ----
EXTENDS TLC, Integers

(* --mpcal MappingMacroDeferredScoping {

mapping macro M {
    read {
        \* it isn't a breaking issue that the error points to the end of the name... (sigh)
        yield $variable + (*:: expectedError+1: ParseFailureError *) N;
    }
    write {
        yield $value - N;
    }
}

archetype Arch(ref p) {
    lbl: p := p + 1;
}

variables pp = 1;

process (Proc = 1) == instance Arch(ref pp)
    mapping pp via M;
}

\* BEGIN PLUSCAL TRANSLATION

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====