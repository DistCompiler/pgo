------------------------------- MODULE func -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(********************

--mpcal func {

    mapping macro MP {
        read {
            yield $variable;
        }

        write {
            yield $value;
        }
    }

    archetype ANode(ref arr[_]) {
    lbl1:
        (* this has the "wrong" number of indices, and implies:
            - read arr[1] (call it x)
            - write [x EXCEPT ![2] = "a"] to arr[1]

          this is hard to keep track of, so it's forbidden instead *)
        (*:: expectedError: MPCalReadWriteAssignmentForbidden *) arr[1][2] := "a";

    lbl2:
        print arr[1][2];
    }

    variable
        arr = [d1 \in {1} |-> [d2 \in {2} |-> ""]];

    fair process (Node \in {1}) == instance ANode(ref arr[_])
        mapping arr[_] via MP;
}

********************)

\* BEGIN TRANSLATION

=============================================================================
