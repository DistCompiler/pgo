------------------------------- MODULE my_hello -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(********************

--mpcal my_hello {
    archetype AMyHello() {
        lbl: print("Hello");
    }

    fair process (MyHello = 1) == instance AMyHello();
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm my_hello {
  
  fair process (MyHello = 1)
  {
    lbl:
      print "Hello";
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "6aa9bd30" /\ chksum(tla) = "af59b94f")
VARIABLE pc

vars == << pc >>

ProcSet == {1}

Init == /\ pc = [self \in ProcSet |-> "lbl"]

lbl == /\ pc[1] = "lbl"
       /\ PrintT("Hello")
       /\ pc' = [pc EXCEPT ![1] = "Done"]

MyHello == lbl

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == MyHello
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(MyHello)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
