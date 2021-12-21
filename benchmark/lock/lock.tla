------------------------------- MODULE lock -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumNodes

(********************

--mpcal lock {

    define {
        NodeSet == 1..NumNodes
    }

    archetype ANode(ref lock) {
    aquireLock:
        await \lnot lock;
        lock := TRUE;
    criticalSection:
        \* print <<"in critical section: ", self>>;
        lock := FALSE;
    }

    variable lock = FALSE;

    fair process (node \in NodeSet) == instance ANode(ref lock);
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm lock {
  variables lock = FALSE;
  define{
    NodeSet == (1) .. (NumNodes)
  }
  
  fair process (node \in NodeSet)
  {
    aquireLock:
      await ~ (lock);
      lock := TRUE;
      goto criticalSection;
    criticalSection:
      lock := FALSE;
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "e053aae6" /\ chksum(tla) = "dba84918")
VARIABLES lock, pc

(* define statement *)
NodeSet == (1) .. (NumNodes)


vars == << lock, pc >>

ProcSet == (NodeSet)

Init == (* Global variables *)
        /\ lock = FALSE
        /\ pc = [self \in ProcSet |-> "aquireLock"]

aquireLock(self) == /\ pc[self] = "aquireLock"
                    /\ ~ (lock)
                    /\ lock' = TRUE
                    /\ pc' = [pc EXCEPT ![self] = "criticalSection"]

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ lock' = FALSE
                         /\ pc' = [pc EXCEPT ![self] = "Done"]

node(self) == aquireLock(self) \/ criticalSection(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NodeSet: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NodeSet : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Invariants

Safety == \lnot (\A i, j \in NodeSet:
                            /\ i /= j
                            /\ pc[i] = "criticalSection"
                            /\ pc[j] = "criticalSection")

\* Properties

ProgressOK(i) == pc[i] = "aquireLock" ~> pc[i] = "criticalSection" 
Liveness == \A i \in NodeSet: ProgressOK(i)

=============================================================================
