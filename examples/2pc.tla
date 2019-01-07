----------------------------- MODULE TwoPC -----------------------------
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

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT RM \* The set of resource managers
CONSTANT TM \* The transaction manager
CONSTANT data

ASSUME TM \notin RM
ASSUME IsFiniteSet(RM)

NumProcs == Cardinality(RM) + 1

(***************************************************************************
--algorithm TwoPC {
  variable network = [from \in 1..NumProcs |-> [to \in 1..NumProcs |-> <<>>]];

  define {
    send(from, to, msg) == [network EXCEPT ![from][to] = Append(@, msg)]
    broadcast(from, msg) == [network EXCEPT ![from] = [to \in 1..NumProcs |-> IF from = to THEN network[from][to] ELSE Append(network[from][to], msg)]]
  }

  macro rcv(dst, buf) {
    with (src \in { s \in 1..NumProcs : Len(network[s][dst]) > 0 }) {
      buf := Head(network[src][dst]);
      network[src] := Tail(network[src])
    }
  }

  macro TMPropose() {
    tmState := "init";
    network := broadcast(TM, [type |-> "Prepare", data |-> data]);
  }

  macro TMCommit() {
    tmState := "committed";
    network := broadcast(TM, [type |-> "Commit"]);
    rmState := [ rm \in RM |-> "committed" ];
  }

  macro TMAbort() {
    tmState := "aborted";
    network := broadcast(TM, [type |-> "Abort"]);
  }

  (* PGo: func CheckQuery() *)
  macro CheckQuery(data) {
    either {
      state := "prepared";
    } or {
      state := "aborted"
    };
  }

  macro RMPrepare(rm, data) {
    CheckQuery(data);
    network := send(rm, TM, [type |-> state, rm |-> rm]);
  }

  macro RMRcvCommitMsg(rm) {
    state := "committed"
  }

  macro RMRcvAbortMsg(rm) {
    state := "aborted"
  }

  process (TManager = TM)
  variables tmState = "init",
            rmState = [rm \in RM |-> "working"],
            received = 0,
            tmsg = "";
  {
               propose: TMPropose();

               loop: while (received < NumProcs - 1) {
                 tmRcv: rcv(TM, tmsg);

                 tmPrep: if (tmsg.type = "prepared") {
                       rmState[tmsg.rm] := "prepared";
                     };

                 tmAbort: if (tmsg.type = "aborted") {
                        rmState[tmsg.rm] := "aborted";
                      };

                 incReceived: received := received +1;
              };

              checkResult: if (\A rm \in RM : rmState[rm] = "prepared") {
                             TMCommit();
                           } else {
                             TMAbort();
                           }
   }
  process (RManager \in RM)
  variables rmsg = "",
            state = "working";
  {
         rcvPrepare: rcv(self, rmsg);

         rmPrep: assert(rmsg.type = "Prepare");
                 RMPrepare(self, rmsg.data);

         rcvDecision: rcv(self, rmsg);

         rmUpdate: if (rmsg.type = "Commit") {
                     RMRcvCommitMsg(self);
                   } else {
                     assert(rmsg.type = "Abort");
                     RMRcvAbortMsg(self);
                   }
   }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES network, pc

VARIABLES tmState, rmState, received, tmsg, rmsg, state

vars == << network, pc, tmState, rmState, received, tmsg, rmsg, state >>

ProcSet == {TM} \cup (RM)

Init == (* Global variables *)
        /\ network = [from \in 1..NumProcs |-> [to \in 1..NumProcs |-> <<>>]]
        (* Process TManager *)
        /\ tmState = "init"
        /\ rmState = [rm \in RM |-> "working"]
        /\ received = 0
        /\ tmsg = ""
        (* Process RManager *)
        /\ rmsg = [self \in RM |-> ""]
        /\ state = [self \in RM |-> "working"]
        /\ pc = [self \in ProcSet |-> CASE self = TM -> "propose"
                                        [] self \in RM -> "rcvPrepare"]

propose == /\ pc[TM] = "propose"
           /\ tmState' = "init"
           /\ network' = broadcast(TM, [type |-> "Prepare", data |-> data])
           /\ pc' = [pc EXCEPT ![TM] = "loop"]
           /\ UNCHANGED << rmState, received, tmsg, rmsg, state >>

loop == /\ pc[TM] = "loop"
        /\ IF received < NumProcs - 1
              THEN /\ pc' = [pc EXCEPT ![TM] = "tmRcv"]
              ELSE /\ pc' = [pc EXCEPT ![TM] = "checkResult"]
        /\ UNCHANGED << network, tmState, rmState, received, tmsg, rmsg, state >>

tmRcv == /\ pc[TM] = "tmRcv"
         /\ \E src \in { s \in 1..NumProcs : Len(network[s][TM]) > 0 }:
              /\ tmsg' = Head(network[src][TM])
              /\ network' = [network EXCEPT ![src][TM] = Tail(@)]
         /\ pc' = [pc EXCEPT ![TM] = "tmPrep"]
         /\ UNCHANGED << tmState, rmState, received, rmsg, state >>

tmPrep == /\ pc[TM] = "tmPrep"
          /\ IF tmsg.type = "prepared"
                THEN /\ rmState' = [rmState EXCEPT ![tmsg.rm] = "prepared"]
                ELSE /\ TRUE
                     /\ UNCHANGED rmState
          /\ pc' = [pc EXCEPT ![TM] = "tmAbort"]
          /\ UNCHANGED << network, tmState, received, tmsg, rmsg, state >>

tmAbort == /\ pc[TM] = "tmAbort"
           /\ IF tmsg.type = "aborted"
                 THEN /\ rmState' = [rmState EXCEPT ![tmsg.rm] = "aborted"]
                 ELSE /\ TRUE
                      /\ UNCHANGED rmState
           /\ pc' = [pc EXCEPT ![TM] = "incReceived"]
           /\ UNCHANGED << network, tmState, received, tmsg, rmsg, state >>

incReceived == /\ pc[TM] = "incReceived"
               /\ received' = received +1
               /\ pc' = [pc EXCEPT ![TM] = "loop"]
               /\ UNCHANGED << network, tmState, rmState, tmsg, rmsg, state >>

checkResult == /\ pc[TM] = "checkResult"
               /\ IF \A rm \in RM : rmState[rm] = "prepared"
                     THEN /\ tmState' = "committed"
                          /\ network' = broadcast(TM, [type |-> "Commit"])
                          /\ rmState' = [ rm \in RM |-> "committed" ]
                     ELSE /\ tmState' = "aborted"
                          /\ network' = broadcast(TM, [type |-> "Abort"])
                          /\ UNCHANGED rmState
               /\ pc' = [pc EXCEPT ![TM] = "Done"]
               /\ UNCHANGED << received, tmsg, rmsg, state >>

TManager == propose \/ loop \/ tmRcv \/ tmPrep \/ tmAbort \/ incReceived
               \/ checkResult

rcvPrepare(self) == /\ pc[self] = "rcvPrepare"
                    /\ \E src \in { s \in 1..NumProcs : Len(network[s][self]) > 0 }:
                         /\ rmsg' = [rmsg EXCEPT ![self] = Head(network[src][self])]
                         /\ network' = [network EXCEPT ![src][self] = Tail(@)]
                    /\ pc' = [pc EXCEPT ![self] = "rmPrep"]
                    /\ UNCHANGED << tmState, rmState, received, tmsg, state >>

rmPrep(self) == /\ pc[self] = "rmPrep"
                /\ Assert((rmsg[self].type = "Prepare"),
                          "Failure of assertion at line 117, column 18.")
                /\ \/ /\ state' = [state EXCEPT ![self] = "prepared"]
                   \/ /\ state' = [state EXCEPT ![self] = "aborted"]
                /\ network' = send(self, TM, [type |-> state'[self], rm |-> self])
                /\ pc' = [pc EXCEPT ![self] = "rcvDecision"]
                /\ UNCHANGED << tmState, rmState, received, tmsg, rmsg >>

rcvDecision(self) == /\ pc[self] = "rcvDecision"
                     /\ \E src \in { s \in 1..NumProcs : Len(network[s][self]) > 0 }:
                          /\ rmsg' = [rmsg EXCEPT ![self] = Head(network[src][self])]
                          /\ network' = [network EXCEPT ![src][self] = Tail(@)]
                     /\ pc' = [pc EXCEPT ![self] = "rmUpdate"]
                     /\ UNCHANGED << tmState, rmState, received, tmsg, state >>

rmUpdate(self) == /\ pc[self] = "rmUpdate"
                  /\ IF rmsg[self].type = "Commit"
                        THEN /\ state' = [state EXCEPT ![self] = "committed"]
                        ELSE /\ Assert((rmsg[self].type = "Abort"),
                                       "Failure of assertion at line 125, column 22.")
                             /\ state' = [state EXCEPT ![self] = "aborted"]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << network, tmState, rmState, received, tmsg,
                                  rmsg >>

RManager(self) == rcvPrepare(self) \/ rmPrep(self) \/ rcvDecision(self)
                     \/ rmUpdate(self)

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Message ==
  {[type |-> "Prepare", data |-> data]} \cup
  [type : {"Commit", "Abort"}]          \cup
  [type : {"prepared", "aborted"}, rm : RM]

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ \A src \in 1..NumProcs, dst \in 1..NumProcs : (\A i \in 1..Len(network[src][dst]) : network[src][dst][i] \in Message)


(* invariant for the transaction manager *)
TMInv == /\ (tmState = "committed") => (\A rm \in RM : rmState[rm] = "prepared" \/ rmState[rm] = "committed")
         /\ (tmState = "aborted") => (\E rm \in RM : rmState[rm] = "aborted")
         /\ (\E dst \in 1..NumProcs : (\E i \in 1..Len(network[TM][dst]) : network[TM][dst][i] = [type |-> "Commit"])) => (tmState =  "committed")
         /\ (\E dst \in 1..NumProcs : (\E i \in 1..Len(network[TM][dst]) : network[TM][dst][i] = [type |-> "Abort"])) => (tmState = "aborted")

(* invariant for the resource managers *)
RMInv(rm) ==
  /\ (\E i \in 1..Len(network[rm][TM]) : network[rm][TM][i] = [type |-> "prepared", rm |-> rm]) => (state[rm] = "prepared")
  /\ (tmState = "committed") => (state[rm] # "aborted")
  /\ (\E i \in 1..Len(network[rm][TM]) : network[rm][TM][i] = [type |-> "aborted", rm |-> rm]) => (state[rm] =  "aborted")

Inv == TypeOK /\ TMInv /\ (\A rm \in RM : RMInv(rm))

=============================================================================
\* Modification History
\* Last modified Fri Jun 22 10:29:27 PDT 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
