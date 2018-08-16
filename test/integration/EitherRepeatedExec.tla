---- MODULE EitherRepeatedExec ----
EXTENDS Integers, Sequences, TLC

(*
--algorithm EitherRepeatedExec {
  variables a = 0, b = 0;
  process (P \in 1..2)
  {
    l1: while (a < 3 \/ b < 3) {
          either {
            await self = 1 /\ a < 3;
            a := a + 1;
          } or {
            await self = 2 /\ b < 3;
            b := b + 1;
          } or {
            skip;
          };
        };
    l2: await a + b = 6;
    l3: print <<a, b>>;
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES a, b, pc

vars == << a, b, pc >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ a = 0
        /\ b = 0
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF a < 3 \/ b < 3
                  THEN /\ \/ /\ self = 1 /\ a < 3
                             /\ a' = a + 1
                             /\ b' = b
                          \/ /\ self = 2 /\ b < 3
                             /\ b' = b + 1
                             /\ a' = a
                          \/ /\ TRUE
                             /\ UNCHANGED <<a, b>>
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
                       /\ UNCHANGED << a, b >>

l2(self) == /\ pc[self] = "l2"
            /\ a + b = 6
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << a, b >>

l3(self) == /\ pc[self] = "l3"
            /\ PrintT(<<a, b>>)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << a, b >>

P(self) == l1(self) \/ l2(self) \/ l3(self)

Next == (\E self \in 1..2: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
