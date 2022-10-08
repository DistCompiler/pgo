----------------------------- MODULE shcounter -----------------------------

(********************
Specification of a simple system that uses a strongly-consistent shared 
counter. Note that the mapping macro for the counter is omitted since it's
trivial and the same as default semantics of read/write in the MPCal.
********************)

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_NODES

(********************

--mpcal shcounter {
    define {
        NODE_SET == 1..NUM_NODES
    }

    archetype ANode(ref cntr) {
    update:
        cntr := cntr + 1;
    wait:
        await cntr = NUM_NODES;
    }

    variables
        cntr = 0;

    fair process (Node \in NODE_SET) == instance ANode(ref cntr);
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm shcounter {
  variables cntr = 0;
  define{
    NODE_SET == (1) .. (NUM_NODES)
  }
  
  fair process (Node \in NODE_SET)
  {
    update:
      cntr := (cntr) + (1);
      goto wait;
    wait:
      await (cntr) = (NUM_NODES);
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "60ddcc05" /\ chksum(tla) = "6889ea91")
VARIABLES cntr, pc

(* define statement *)
NODE_SET == (1) .. (NUM_NODES)


vars == << cntr, pc >>

ProcSet == (NODE_SET)

Init == (* Global variables *)
        /\ cntr = 0
        /\ pc = [self \in ProcSet |-> "update"]

update(self) == /\ pc[self] = "update"
                /\ cntr' = (cntr) + (1)
                /\ pc' = [pc EXCEPT ![self] = "wait"]

wait(self) == /\ pc[self] = "wait"
              /\ (cntr) = (NUM_NODES)
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ cntr' = cntr

Node(self) == update(self) \/ wait(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NODE_SET: Node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NODE_SET : WF_vars(Node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

CntrValueOK == <>[](cntr = NUM_NODES)

=============================================================================
\* Modification History
\* Last modified Tue Nov 02 17:13:56 PDT 2021 by shayan
\* Created Fri Oct 22 19:13:21 PDT 2021 by shayan
