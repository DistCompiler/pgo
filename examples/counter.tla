--------------------------- MODULE counter ---------------------------

EXTENDS Integers, TLC

CONSTANT procs, iters

(*

--algorithm counter {
  variables counter = 0;

  fair process (P \in 0..procs-1)
  variables i = 0;
  {
      w: while (i < iters) {
          incCounter: counter := counter + 1;
                      print counter;
          nextIter:   i := i + 1;
      }
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES counter, pc, i

vars == << counter, pc, i >>

ProcSet == (0..procs-1)

Init == (* Global variables *)
        /\ counter = 0
        (* Process P *)
        /\ i = [self \in 0..procs-1 |-> 0]
        /\ pc = [self \in ProcSet |-> "w"]

w(self) == /\ pc[self] = "w"
           /\ IF i[self] < iters
                 THEN /\ pc' = [pc EXCEPT ![self] = "incCounter"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << counter, i >>

incCounter(self) == /\ pc[self] = "incCounter"
                    /\ counter' = counter + 1
                    /\ PrintT(counter')
                    /\ pc' = [pc EXCEPT ![self] = "nextIter"]
                    /\ i' = i

nextIter(self) == /\ pc[self] = "nextIter"
                  /\ i' = [i EXCEPT ![self] = i[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "w"]
                  /\ UNCHANGED counter

P(self) == w(self) \/ incCounter(self) \/ nextIter(self)

Next == (\E self \in 0..procs-1: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..procs-1 : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* If all processes are done, the counter should be equal the
   number of processes times the number of iterations each performed *)
CounterConverges ==
    (\A self \in ProcSet: pc[self] = "Done") => (counter = procs * iters)

======================================================================
