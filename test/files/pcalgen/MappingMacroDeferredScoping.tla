---- MODULE MappingMacroDeferredScoping ----
EXTENDS TLC, Integers

(* --mpcal MappingMacroDeferredScoping {

mapping macro M {
    read {
        yield $variable + (*:: expectedError: DefinitionLookupError *) N;
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