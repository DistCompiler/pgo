------------------------------- MODULE IndexingLocals -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

(********************

--mpcal IndexingLocals {
    define {
        NodeSet== 1..1
    }

    archetype ANode()
    variables log = <<>>, p;
    {
    logWrite:
        log := Append(log, 68);
        log := Append(log, 5);
        log[2] := 21;
        log := Append(log, 999);
        log := Append(log, [foo |-> 42]);
    logUpdate:
        log[1] := 3;
    logRead:
        p := log[1];
    multiWrite:
        log[4].foo := 43;
    }

    fair process (node \in NodeSet) == instance ANode();
}


\* BEGIN PLUSCAL TRANSLATION
--algorithm bench {
  define{
    NodeSet == (1) .. (1)
  }

  fair process (node \in NodeSet)
    variables log = <<>>;
  {
    logWrite:
      log := Append(log, 1);
      goto logUpdate;
    logUpdate:
      log := [log EXCEPT ![1] = 3];
      goto logRead;
    logRead:
      print (log)[1];
      goto Done;
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "2b263db7" /\ chksum(tla) = "44744de")
VARIABLE pc

(* define statement *)
NodeSet == (1) .. (1)

VARIABLE log

vars == << pc, log >>

ProcSet == (NodeSet)

Init == (* Process node *)
        /\ log = [self \in NodeSet |-> <<>>]
        /\ pc = [self \in ProcSet |-> "logWrite"]

logWrite(self) == /\ pc[self] = "logWrite"
                  /\ log' = [log EXCEPT ![self] = Append(log[self], 1)]
                  /\ pc' = [pc EXCEPT ![self] = "logUpdate"]

logUpdate(self) == /\ pc[self] = "logUpdate"
                   /\ log' = [log EXCEPT ![self] = [log[self] EXCEPT ![1] = 3]]
                   /\ pc' = [pc EXCEPT ![self] = "logRead"]

logRead(self) == /\ pc[self] = "logRead"
                 /\ PrintT((log[self])[1])
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ log' = log

node(self) == logWrite(self) \/ logUpdate(self) \/ logRead(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NodeSet: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NodeSet : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Nov 25 11:28:00 PST 2021 by shayan
\* Created Thu Oct 21 11:00:36 PDT 2021 by shayan