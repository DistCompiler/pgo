
---------------------- MODULE dqueue ------------------------
EXTENDS Integers, Sequences, TLC

(*

--algorithm DistributedQueue {
    \* Globals
    variables
    \** @PGo{ var queue []string }@PGo
    queue = <<>>;

    process (Producer = 2)
    { p: while (TRUE) {
        p1: if (Len(queue) < 3) {
        p2:    queue := Append(queue, "resource");
               }}}

    process (Consumer \in {0,1})
        \** @PGo{ var resource string }@PGo
        variables resource;
    { c: while (TRUE) {
          if (Len(queue) # 0)
              {
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
            THEN /\ pc' = [pc EXCEPT ![2] = "p2"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "p"]
      /\ UNCHANGED << queue, resource >>

p2 == /\ pc[2] = "p2"
      /\ queue' = Append(queue, "resource")
      /\ pc' = [pc EXCEPT ![2] = "p"]
      /\ UNCHANGED resource

Producer == p \/ p1 \/ p2

c(self) == /\ pc[self] = "c"
           /\ pc' = [pc EXCEPT ![self] = "c1"]
           /\ UNCHANGED << queue, resource >>

c1(self) == /\ pc[self] = "c1"
            /\ IF queue # <<>>
                  THEN /\ resource' = [resource EXCEPT ![self] = Head(queue)]
                       /\ queue' = Tail(queue)
                       /\ Assert((resource'[self] = "resource"),
                                 "Failure of assertion at line 32, column 15.")
                       /\ pc' = [pc EXCEPT ![self] = "c"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "c"]
                       /\ UNCHANGED << queue, resource >>

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
NoStarvationP == (pc[2] = "p1") ~> (pc[2] = "p2")

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

======================================================================
