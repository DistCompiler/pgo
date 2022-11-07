--------------------------- MODULE round_robin ---------------------------

EXTENDS Integers, TLC

CONSTANT procs, iters

(*

--algorithm round_robin {
  variables counter = 0,
            token = -1;

  fair process (P \in 0..procs-1)
  variables i = 0;
  {
      w: while (i < iters) {
          waitToken:  await token = -1 \/ token = self;
          incCounter: counter := counter + 1;
                      token := (self + 1) % procs;
                      print counter;
          nextIter:   i := i + 1;
      }
  }
}
*)

\* BEGIN TRANSLATION
VARIABLES counter, token, pc, i

vars == << counter, token, pc, i >>

ProcSet == (0..procs-1)

Init == (* Global variables *)
        /\ counter = 0
        /\ token = -1
        (* Process P *)
        /\ i = [self \in 0..procs-1 |-> 0]
        /\ pc = [self \in ProcSet |-> "w"]

w(self) == /\ pc[self] = "w"
           /\ IF i[self] < iters
                 THEN /\ pc' = [pc EXCEPT ![self] = "waitToken"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << counter, token, i >>

waitToken(self) == /\ pc[self] = "waitToken"
                   /\ token = -1 \/ token = self
                   /\ pc' = [pc EXCEPT ![self] = "incCounter"]
                   /\ UNCHANGED << counter, token, i >>

incCounter(self) == /\ pc[self] = "incCounter"
                    /\ counter' = counter + 1
                    /\ token' = (self + 1) % procs
                    /\ pc' = [pc EXCEPT ![self] = "nextIter"]
                    /\ i' = i

nextIter(self) == /\ pc[self] = "nextIter"
                  /\ i' = [i EXCEPT ![self] = i[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "w"]
                  /\ UNCHANGED << counter, token >>

P(self) == w(self) \/ waitToken(self) \/ incCounter(self) \/ nextIter(self)

Next == (\E self \in 0..procs-1: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..procs-1 : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


TokenWithinBounds == 
  token = -1 \/ token \in 0..procs-1

CounterConverges ==
    (\A self \in ProcSet: pc[self] = "Done") => (counter = procs * iters)

ProcessesGetToken ==
    \A self \in ProcSet : <>(token = self)

=============================================================================
\* Modification History
\* Last modified Fri Jun 08 13:09:07 PDT 2018 by rmc
\* Created Thu May 03 23:02:12 PDT 2018 by rmc
