--------------------------- MODULE counter ---------------------------

EXTENDS Integers, TLC

CONSTANT procs, iters

(*

--algorithm counter {
  (** @PGo{ arg procs int }@PGo
      @PGo{ arg iters int }@PGo
   **)
  variables counter = 0,
            token = 0;

  fair process (P \in 1..procs)
  variables i = 0;
  {
      w: while (i < iters) {
          inc: await token = 0 \/ token = self;
               counter := counter + 1;
               print counter;
               token := (self + 1) % procs;
               i := i + 1;
      }
  }
}
*)

\* BEGIN TRANSLATION
VARIABLES counter, token, pc, i

vars == << counter, token, pc, i >>

ProcSet == (1..procs)

Init == (* Global variables *)
        /\ counter = 0
        /\ token = 0
        (* Process P *)
        /\ i = [self \in 1..procs |-> 0]
        /\ pc = [self \in ProcSet |-> "w"]

w(self) == /\ pc[self] = "w"
           /\ IF i[self] < iters
                 THEN /\ pc' = [pc EXCEPT ![self] = "inc"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << counter, token, i >>

inc(self) == /\ pc[self] = "inc"
             /\ token = 0 \/ token = self
             /\ counter' = counter + 1
             /\ PrintT(counter')
             /\ token' = (self + 1) % procs
             /\ i' = [i EXCEPT ![self] = i[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "w"]

P(self) == w(self) \/ inc(self)

Next == (\E self \in 1..procs: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..procs : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


TokenWithinBounds ==
  token = -1 \/ token \in 0..procs-1

CounterConverges ==
    Termination => (counter = procs * iters)

ProcessesGetToken ==
    \A self \in ProcSet : <>(token = self)

=============================================================================
\* Modification History
\* Last modified Tue Jun 05 08:07:56 EDT 2018 by osboxes
\* Last modified Fri May 04 01:45:09 PDT 2018 by rmc
\* Created Thu May 03 23:02:12 PDT 2018 by rmc
