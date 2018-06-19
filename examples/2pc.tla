----------------------------- MODULE PTwoPhase -----------------------------
(***************************************************************************)
(* Changes from the original TwoPhase spec, obtained at:                   *)
(*     http://lamport.azurewebsites.net/tla/two-phase.html                 *)
(*                                                                         *)
(*   - Removal of CHOOSE to choose a transaction manager identifier        *)
(*     (not supported by PGo). Use a regular constant and ASSUME they are  *)
(*     not the same.                                                       *)
(*   - 'tmState' and 'tmPrepared' variables move from being (unnecessarily *)
(*     global to being local to the 'TManager''process                     *)
(*   - Addition of the "Propose" message, sent by transaction managers to  *)
(*     resource managers when a transaction is initiated.                  *)
(*   - Addition of an "Abort" message from resource managers to the        *)
(*     transaction manager, instead of having the manager spontaneously    *)
(*     deciding to abort. That makes the spec closer to an implementation. *)
(***************************************************************************)

CONSTANT RM \* The set of resource managers
CONSTANT TM \* The transaction manager

CONSTANT data

(* ASSUME TM \notin RM *)

(***************************************************************************
--algorithm TwoPhaseCommit {
  variables rmState = [rm \in RM |-> "working"],
            msgs = {} ;
  macro SendMsg(m) { msgs := msgs \cup {m} }
  macro RcvMsg(m) { await m \in msgs }
  macro TMRcvPrepared() {
    (***********************************************************************)
    (* The TM receives a "Prepared" message from some resource manager.    *)
    (***********************************************************************)
    await tmState = "init";
    with (rm \in RM) {
      RcvMsg([type |-> "Prepared", rm |-> rm]);
      tmPrepared := tmPrepared \cup {rm}
     }
   }

  macro TMPropose() {
    SendMsg([type |-> "Propose", data |-> data])
  }

  macro TMCommit() {
    (***********************************************************************)
    (* The TM commits the transaction; enabled iff the TM is in its        *)
    (* initial state and every RM has sent a "Prepared" message.           *)
    (***********************************************************************)
    await /\ tmState = "init"
          /\ tmPrepared = RM ;
    tmState := "committed" ;
    SendMsg([type |-> "Commit"])
   }
  macro TMAbort() {
    (***********************************************************************)
    (* The TM spontaneously aborts the transaction.                        *)
    (***********************************************************************)
    await tmState = "init" /\ ([type |-> "RMAborted"] \in msgs);
    tmState := "aborted" ;
    SendMsg([type |-> "Abort"])
   }
  macro RMPrepare(rm) {
    (***********************************************************************)
    (* Resource manager rm prepares.                                       *)
    (***********************************************************************)
    await rmState[rm] = "working" /\ ([type |-> "Propose", data |-> data] \in msgs);
    rmState[rm] := "prepared" ;
    SendMsg([type |-> "RMPrepared", rm |-> rm])
   }
  macro RMChooseToAbort(rm) {
    (***********************************************************************)
    (* Resource manager rm spontaneously decides to abort.  As noted       *)
    (* above, rm does not send any message in our simplified spec.         *)
    (***********************************************************************)
    await rmState[rm] = "working" ;
    rmState[rm] := "aborted";
    SendMsg([type |-> "RMAborted"]);
   }
  macro RMRcvCommitMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to commit.                    *)
    (***********************************************************************)
    RcvMsg([type |-> "Commit"]) ;
    rmState[rm] := "committed"
   }
  macro RMRcvAbortMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to abort.                     *)
    (***********************************************************************)
    RcvMsg ([type |-> "Abort"]) ;
    rmState[rm] := "aborted"
  }

  process (TManager = TM)
  variables tmState = "init",
            tmPrepared = {};
  {
    tmstart: while (TRUE) {
               either { TMPropose() }
               or     { TMCommit() }
               or     { TMAbort() }
               or     { TMRcvPrepared() }
             }
   }
  process (RManager \in RM) {
    rmstart: while (TRUE) {
               either { RMPrepare(self) }
               or     { RMChooseToAbort(self) }
               or     { RMRcvCommitMsg(self) }
               or     { RMRcvAbortMsg(self) }
             }
   }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES rmState, msgs, tmState, tmPrepared

vars == << rmState, msgs, tmState, tmPrepared >>

ProcSet == {TM} \cup (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ msgs = {}
        (* Process TManager *)
        /\ tmState = "init"
        /\ tmPrepared = {}

TManager == /\ \/ /\ msgs' = (msgs \cup {([type |-> "Propose", data |-> data])})
                  /\ UNCHANGED <<tmState, tmPrepared>>
               \/ /\ /\ tmState = "init"
                     /\ tmPrepared = RM
                  /\ tmState' = "committed"
                  /\ msgs' = (msgs \cup {([type |-> "Commit"])})
                  /\ UNCHANGED tmPrepared
               \/ /\ tmState = "init" /\ ([type |-> "RMAborted"] \in msgs)
                  /\ tmState' = "aborted"
                  /\ msgs' = (msgs \cup {([type |-> "Abort"])})
                  /\ UNCHANGED tmPrepared
               \/ /\ tmState = "init"
                  /\ \E rm \in RM:
                       /\ ([type |-> "Prepared", rm |-> rm]) \in msgs
                       /\ tmPrepared' = (tmPrepared \cup {rm})
                  /\ UNCHANGED <<msgs, tmState>>
            /\ UNCHANGED rmState

RManager(self) == /\ \/ /\ rmState[self] = "working" /\ ([type |-> "Propose", data |-> data] \in msgs)
                        /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                        /\ msgs' = (msgs \cup {([type |-> "RMPrepared", rm |-> self])})
                     \/ /\ rmState[self] = "working"
                        /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                        /\ msgs' = (msgs \cup {([type |-> "RMAborted"])})
                     \/ /\ ([type |-> "Commit"]) \in msgs
                        /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                        /\ msgs' = msgs
                     \/ /\ ([type |-> "Abort"]) \in msgs
                        /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                        /\ msgs' = msgs
                  /\ UNCHANGED << tmState, tmPrepared >>

Next == TManager
           \/ (\E self \in RM: RManager(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Message ==
  [type : {"RMPrepared"}, rm : RM]  \cup  [type : {"RMAborted", "Commit", "Abort"}] \cup [type: {"Propose"}, data: {data}]

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM  \* \in SUBSET RM
  /\ msgs \subseteq Message   \* \in SUBSET Message


(* invariant for the transaction manager *)
TMInv == /\ (tmState = "committed") => (tmPrepared = RM)
         /\ ([type |-> "Commit"] \in msgs) => (tmState = "committed")
         /\ ([type |-> "Abort"] \in msgs) => (tmState = "aborted")

(* invariant for the resource managers *)
RMInv(rm) ==
  /\ (rm \in tmPrepared) => ([type |-> "Prepared", rm |-> rm] \in msgs)
  /\ ([type |-> "Prepared", rm |-> rm] \in msgs) =>
         /\ rmState[rm] # "working"
         /\ (rmState[rm] = "aborted") => ([type |-> "Abort"] \in msgs)
  /\ (rmState[rm]= "committed") => ([type |-> "Commit"] \in msgs)

Inv == TypeOK /\ TMInv /\ (\A rm \in RM : RMInv(rm))

=============================================================================
\* Modification History
\* Last modified Tue Jun 19 14:29:09 PDT 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
