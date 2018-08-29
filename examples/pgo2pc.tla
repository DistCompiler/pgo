----------------------------- MODULE pgo2pc -----------------------------
EXTENDS Integers,Sequences,FiniteSets,TLC
CONSTANTS RM,                  \* The number of resource managers.
          BTM,                 \* Whether have backupTM.
          RMMAYFAIL,           \* Whether RM could fail.
          TMMAYFAIL            \* Whether TM could fail.


canCommit(rmStateL) ==
    \A rm \in RM : rmStateL[rm] \in {"prepared","committed"} \*If some rm are commited or all rm are commited,

(** might fail due to \A predicate **)
canAbort(rmStateL) ==
    \A rm \in RM : rmStateL[rm] # "committed"  \*if no rm are committed, we don't know the state of tmState,


(* --algorithm TransactionCommit { (*** for pgo arg RM int done ***)
  variable rmState = [rm \in RM |-> "working"],
           tmState = "init";                            \* tmState's init state.
           btmState = "init";                           \* backupTM's init state.

                                               \*if tmState is not "commit", we cannot commit.

  (**
  macro Prepare(p){
    \*@@PGODEV does this await break?
    await rmState[p] = "working";  \*if rmState[p] is working, then it will be prepared
      rmState[p] :="prepared";
    }
    **)
   (** Is This equivalent to the prior macro if placed in a for loop? Must all state transfers be idempotent?  **)

  macro Prepare(p) {
    if (rmState[p] = "working") {
        rmState[p] := "prepared";
    };
  }


  (**
  macro Decide(p){
    either {await rmState[p] = "prepared" /\ canCommit(rmState) /\ (tmState = "commit" \/ btmState = "commit");     \*If rmState[p] is prepared, some rm is committed and
                                                                                                           \*if we have backupTM, either tmState or btmState is "commit",
                                                                                                           \*then we can change rmState to "commit".
            rmState[p] := "committed";
           }
    or     {await rmState[p] \in {"working","prepared"} /\ canAbort(rmState);                                      \*If not all rmState is committed, we can abort at any time.
            rmState[p] := "abort"
           }
  }**)

  (** Do the functions canCommit require arguments to pass to them, or does pgo translate that?
  Is not performing a decide the same as letting TLC hit a wall on either or? **)
  macro Decide(p) {
    if ( rmState[p] = "prepared" /\ canCommit(rmState) /\ (tmState = "commit" \/ btmState = "commit") ){
        rmState[p] := "committed";
    };
    else if ( rmState[p] \in {"working", "prepared"} /\ canAbort(rmState) ) {
        rmState[p] := "abort";
    };
  }

  macro Fail(p){
     if(RMMAYFAIL)  rmState[p] := "crash"                                \*If RMMAYFAIL, rmState[p] could be "crash"
  }

  process(RManager \in RM){                                          \*If rmState is working or prepared, it should execute until abort or commit if we
    RS:while(rmState[self] \in {"working","prepared"}){                   \*set up backupTM. Otherwise termination might be violated.
         either Prepare(self) or Decide(self) or Fail(self)}
  }

  process(TManager = 0){                                              \*If all rm are prepared, it's time to commit, so set tmState to commit.
  TS:either{await canCommit(rmState);
         TC:tmState := "commit";
            if(BTM) btmState := "commit";                                  \*If we set backupTM, change the btmState just the same as tmState.
         F1:if(TMMAYFAIL) tmState := "hidden";}

     or{await canAbort(rmState);                                                    \*Abort can appear any time unless all rmState are committed.
       TA:tmState := "abort";
            if(BTM) btmState := "abort";                                   \*If we set backupTM, change the btmState just the same as tmState.
       F2:if(TMMAYFAIL) tmState := "hidden";}
   }
}
*)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, btmState, pc

vars == << rmState, tmState, btmState, pc >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |->"working"]
        /\ tmState = "init"
        /\ btmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working","prepared"}
                  THEN /\ \/ /\ IF rmState[self] = "working"
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                          \/ /\ IF rmState[self] = "prepared" /\ canCommit(rmState) /\ (tmState = "commit" \/ btmState = "commit")
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                   ELSE /\ IF rmState[self] \in {"working", "prepared"} /\ canAbort(rmState)
                                              THEN /\ rmState' = "abort"
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED rmState
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "crash"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED << tmState, btmState >>

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit(rmState)
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort(rmState)
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState, btmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ IF BTM
            THEN /\ btmState' = "commit"
            ELSE /\ TRUE
                 /\ UNCHANGED btmState
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, btmState >>

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ IF BTM
            THEN /\ btmState' = "abort"
            ELSE /\ TRUE
                 /\ UNCHANGED btmState
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, btmState >>

TManager == TS \/ TC \/ F1 \/ TA \/ F2

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

consistency == tmState = "commit" => \A i \in RM : rmState[i] # "abort"
            /\ tmState = "abort" => \A j \in RM : rmState[j] # "committed"
            /\ tmState = "hidden" => \A k \in RM : rmState[k] # "committed"
terminate == <>(\A i \in RM : rmState[i] \in {"committed","abort","crash"})

=============================================================================
\*1.2 TMMAYFAIL is true and RMMAYFAIL is false means tmState could be "hidden" and rmState cannot be
\*hidden. In this situation, termination will be violated. For example, when TM is "commit" and some
\*RM are committed, then TM crashed while some other RM is prepared, but they can never be "commit" or abort
\*because TM is "hidden" now. That's why we get result when RM equals 3 that <<"committed","prepared","committed">>.
\*It will never been terminated because "prepared" has no way to "commit".

\*1.3 Termination and comsistency remain true. The states cancommit and canabort is owned by both BTM and TM.
\* So when TM crashes, the RMs can still consult the BTM and make their decision.
\*If an RM crashed, then all other RMs can only abort. So all other uncrashed RMs remain consistent.

\* Modification History
\* Last modified Wed Feb 28 17:01:19 PST 2018 by stewartgrant
\* Last modified Tue Dec 05 19:55:47 EST 2017 by lenovo
\* Created Wed Nov 29 17:13:20 EST 2017 by lenovo



\*Group Members xhu7:xhu7@buffalo.edu
\*Haowei Zhou  haoweizh@buffalo.edu

