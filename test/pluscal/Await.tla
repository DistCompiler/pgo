---------------------------- MODULE Await ----------------------------
EXTENDS Integers
CONSTANT Procs

(***************************************************************************
--algorithm Await
	{
		variable x = 0;
		process (p = 0)
		{
			p0: while (TRUE)
			{
				p1: await x = 0;
				    x := 1;
			}
		}
		process (q = 1)
		{
			q0: while (TRUE)
			{
				q1: await x = 1;
				    x := 0;
			}
		}
	}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "p0"
                                        [] self = 1 -> "q0"]

p0 == /\ pc[0] = "p0"
      /\ pc' = [pc EXCEPT ![0] = "p1"]
      /\ x' = x

p1 == /\ pc[0] = "p1"
      /\ x = 0
      /\ x' = 1
      /\ pc' = [pc EXCEPT ![0] = "p0"]

p == p0 \/ p1

q0 == /\ pc[1] = "q0"
      /\ pc' = [pc EXCEPT ![1] = "q1"]
      /\ x' = x

q1 == /\ pc[1] = "q1"
      /\ x = 1
      /\ x' = 0
      /\ pc' = [pc EXCEPT ![1] = "q0"]

q == q0 \/ q1

Next == p \/ q

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
