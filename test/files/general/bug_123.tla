---- MODULE bug_123 ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NUM_NODES

(*****************
--mpcal bug_123 {
    mapping macro MyMappingMacro {
        read {
            yield $variable;
        }

        write {
            yield $value;
        }
    }

    archetype AServer(ref mp) {
        op:
            mp[self] := 1;
    }

    variables
        mymp = [id \in 1..NUM_NODES |-> 0];

    fair process (Server \in 1..NUM_NODES) == instance AServer()
        mapping (*:: expectedError: MappingLookupError *) mymp[_] via MyMappingMacro;
} *)

\* BEGIN TRANSLATION
====