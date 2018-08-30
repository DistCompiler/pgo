---------------------- MODULE dqueue ------------------------
EXTENDS Integers, Sequences, TLC

(*

--algorithm DistributedQueue {
    \* Globals
    variables
      queue = <<>>;

    process (Producer = 2)
    { p: while (TRUE) {
      p1:  if (Len(queue) < 3) {
                 queue := Append(queue, "resource");
               }}}

    process (Consumer \in {0,1})
      variables resource;
    { c: while (TRUE) {
      c1:  if (Len(queue) # 0) {
              resource := Head(queue);
              queue := Tail(queue);
              assert (resource = "resource");
              print(resource);
              }}}


}
end algorithm *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queue, pc, resource

vars == << queue, pc, resource >>

ProcSet == {2} \cup ({0,1})

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process Consumer *)
        /\ resource = [self \in {0,1} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = 2 -> "p"
                                        [] self \in {0,1} -> "c"]

p == /\ pc[2] = "p"
     /\ pc' = [pc EXCEPT ![2] = "p1"]
     /\ UNCHANGED << queue, resource >>

p1 == /\ pc[2] = "p1"
      /\ IF Len(queue) < 3
            THEN /\ queue' = Append(queue, "resource")
            ELSE /\ TRUE
                 /\ queue' = queue
      /\ pc' = [pc EXCEPT ![2] = "p"]
      /\ UNCHANGED resource

Producer == p \/ p1

c(self) == /\ pc[self] = "c"
           /\ pc' = [pc EXCEPT ![self] = "c1"]
           /\ UNCHANGED << queue, resource >>

c1(self) == /\ pc[self] = "c1"
            /\ IF Len(queue) # 0
                  THEN /\ resource' = [resource EXCEPT ![self] = Head(queue)]
                       /\ queue' = Tail(queue)
                       /\ Assert((resource'[self] = "resource"), 
                                 "Failure of assertion at line 26, column 15.")
                       /\ PrintT((resource'[self]))
                  ELSE /\ TRUE
                       /\ UNCHANGED << queue, resource >>
            /\ pc' = [pc EXCEPT ![self] = "c"]

Consumer(self) == c(self) \/ c1(self)

Next == Producer
           \/ (\E self \in {0,1}: Consumer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)
        /\ \A self \in {0,1} : WF_vars(Consumer(self))

\* END TRANSLATION

\*Verification
\*Commented out invariants are due to the critical section issue with while loop labels
\* Mutual exclusion
\*MutualExclusion == ~ (pc[0] = "c2" /\ pc[1] = "c2")

\* No deadlock
\*NoDeadlockC == (\A proc1 \in {0,1} : pc[proc1] = "c1") ~> (\E proc2 \in {0,1} : pc[proc2] = "c2")

\* No starvation
NoStarvationC == \A proc \in {0,1} : (pc[proc] = "c1") ~> (pc[proc] = "c")
NoStarvationP == (pc[2] = "p1") ~> (pc[2] = "p")

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

======================================================================
