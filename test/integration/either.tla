---- MODULE either ----
EXTENDS Integers, Sequences, TLC

(*
--algorithm either {
  process (P \in 1..3)
  variables a = 1, b = 2;
  {
    l1: either {
              a := 10;
              await b = 30;
        } or {
              b := 30;
          l2: await a = 1;
        };
    l3: print <<a, b>>;
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES pc, a, b

vars == << pc, a, b >>

ProcSet == (1..3)

Init == (* Process P *)
        /\ a = [self \in 1..3 |-> 1]
        /\ b = [self \in 1..3 |-> 2]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ \/ /\ a' = [a EXCEPT ![self] = 10]
                  /\ b[self] = 30
                  /\ pc' = [pc EXCEPT ![self] = "l3"]
                  /\ b' = b
               \/ /\ b' = [b EXCEPT ![self] = 30]
                  /\ pc' = [pc EXCEPT ![self] = "l2"]
                  /\ a' = a

l2(self) == /\ pc[self] = "l2"
            /\ a[self] = 1
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << a, b >>

l3(self) == /\ pc[self] = "l3"
            /\ PrintT(<<a[self], b[self]>>)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << a, b >>

P(self) == l1(self) \/ l2(self) \/ l3(self)

Next == (\E self \in 1..3: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
