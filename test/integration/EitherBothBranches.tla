---- MODULE EitherBothBranches ----
EXTENDS Integers, Sequences, TLC

(*
--algorithm EitherBothBranches {
  variables a = 1, b = 2, count = 0;
  process (P \in 1..2)
  {
    l2: either {
              a := 10;
              await self = 1;
          l3: count := count + 1;
        } or {
              b := 20;
              await self = 2;
          l4: count := count + 1;
        };
    l5: await count = 2;
    l6: print <<a, b>>;
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES a, b, count, pc

vars == << a, b, count, pc >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ a = 1
        /\ b = 2
        /\ count = 0
        /\ pc = [self \in ProcSet |-> "l2"]

l2(self) == /\ pc[self] = "l2"
            /\ \/ /\ a' = 10
                  /\ self = 1
                  /\ pc' = [pc EXCEPT ![self] = "l3"]
                  /\ b' = b
               \/ /\ b' = 20
                  /\ self = 2
                  /\ pc' = [pc EXCEPT ![self] = "l4"]
                  /\ a' = a
            /\ count' = count

l3(self) == /\ pc[self] = "l3"
            /\ count' = count + 1
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << a, b >>

l4(self) == /\ pc[self] = "l4"
            /\ count' = count + 1
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << a, b >>

l5(self) == /\ pc[self] = "l5"
            /\ count = 2
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << a, b, count >>

l6(self) == /\ pc[self] = "l6"
            /\ PrintT(<<a, b>>)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << a, b, count >>

P(self) == l2(self) \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)

Next == (\E self \in 1..2: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
