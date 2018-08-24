---- MODULE EitherRepeatedExec ----
EXTENDS Integers, Sequences, TLC

(*
--algorithm EitherRepeatedExec {
  process (P = "P")
  variable a = 0;
  {
    l1: while (TRUE) {
          either {
            await a >= 3;
            goto l2;
          } or {
            await a < 3;
            a := a + 1;
          };
        };
    l2: print a;
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES pc, a

vars == << pc, a >>

ProcSet == {"P"}

Init == (* Process P *)
        /\ a = 0
        /\ pc = [self \in ProcSet |-> "l1"]

l1 == /\ pc["P"] = "l1"
      /\ \/ /\ a >= 3
            /\ pc' = [pc EXCEPT !["P"] = "l2"]
            /\ a' = a
         \/ /\ a < 3
            /\ a' = a + 1
            /\ pc' = [pc EXCEPT !["P"] = "l1"]

l2 == /\ pc["P"] = "l2"
      /\ PrintT(a)
      /\ pc' = [pc EXCEPT !["P"] = "Done"]
      /\ a' = a

P == l1 \/ l2

Next == P
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
