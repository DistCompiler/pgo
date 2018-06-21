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

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT RM \* The set of resource managers
CONSTANT TM \* The transaction manager
CONSTANT data

ASSUME TM \notin RM
ASSUME IsFiniteSet(RM)

NumProcs == Cardinality(RM) + 1

(***************************************************************************
--algorithm TwoPhaseCommit {
  variable network = [from \in 1..NumProcs |-> [to \in 1..NumProcs |-> <<>>]];

  define {
    send(from, to, msg) == [network EXCEPT ![from][to] = Append(@, msg)]
    broadcast(from, msg) == [network EXCEPT ![from] = [to \in 1..NumProcs |-> IF from = to THEN network[from][to] ELSE Append(network[from][to], msg)]]
  }

  macro rcv(to, buf) {
    with (from \in { j \in 1..NumProcs : Len(network[j][to]) > 0 }) {
      buf := Head(network[from][to]);
      network[from][to] := Tail(@)
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

  macro RMPrepare(rm, decision) {
    await state = "working";

    (* PGo: func CheckQuery() string *)
    either {
      decision := "prepared"
    } or {
      decision := "aborted"
    };

    state := decision;
    network := send(rm, TM, [type |-> decision, rm |-> rm]);
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
            decision = "",
            state = "working",
            consensus = 0;
  {
    rmstart: while (consensus = 0) {
               rcvLbl: rcv(self, rmsg);

               rmPrep: if (rmsg.type = "Prepare") {
                 RMPrepare(self, decision);
               };

               rmCommit: if (rmsg.type = "Commit") {
                 consensus := 1;
                 RMRcvCommitMsg(self);
               };

               rmAbort: if (rmsg.type = "Abort") {
                 consensus := 1;
                 RMRcvAbortMsg(self);
               }
             }
   }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES network, pc

(* define statement *)
send(from, to, msg) == [network EXCEPT ![from][to] = Append(@, msg)]
broadcast(from, msg) == [network EXCEPT ![from] = [to \in 1..NumProcs |-> IF from = to THEN network[from][to] ELSE Append(network[from][to], msg)]]

VARIABLES tmState, rmState, received, tmsg, rmsg, decision, state, consensus

vars == << network, pc, tmState, rmState, received, tmsg, rmsg, decision,
           state, consensus >>

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
        /\ decision = [self \in RM |-> ""]
        /\ state = [self \in RM |-> "working"]
        /\ consensus = [self \in RM |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = TM -> "propose"
                                        [] self \in RM -> "rmstart"]

propose == /\ pc[TM] = "propose"
           /\ tmState' = "init"
           /\ network' = broadcast(TM, [type |-> "Prepare", data |-> data])
           /\ pc' = [pc EXCEPT ![TM] = "loop"]
           /\ UNCHANGED << rmState, received, tmsg, rmsg, decision, state,
                           consensus >>

loop == /\ pc[TM] = "loop"
        /\ IF received < NumProcs - 1
              THEN /\ pc' = [pc EXCEPT ![TM] = "tmRcv"]
              ELSE /\ pc' = [pc EXCEPT ![TM] = "checkResult"]
        /\ UNCHANGED << network, tmState, rmState, received, tmsg, rmsg,
                        decision, state, consensus >>

tmRcv == /\ pc[TM] = "tmRcv"
         /\ \E from \in { j \in 1..NumProcs : Len(network[j][TM]) > 0 }:
              /\ tmsg' = Head(network[from][TM])
              /\ network' = [network EXCEPT ![from][TM] = Tail(@)]
         /\ pc' = [pc EXCEPT ![TM] = "tmPrep"]
         /\ UNCHANGED << tmState, rmState, received, rmsg, decision, state,
                         consensus >>

tmPrep == /\ pc[TM] = "tmPrep"
          /\ IF tmsg.type = "prepared"
                THEN /\ rmState' = [rmState EXCEPT ![tmsg.rm] = "prepared"]
                ELSE /\ TRUE
                     /\ UNCHANGED rmState
          /\ pc' = [pc EXCEPT ![TM] = "tmAbort"]
          /\ UNCHANGED << network, tmState, received, tmsg, rmsg, decision,
                          state, consensus >>

tmAbort == /\ pc[TM] = "tmAbort"
           /\ IF tmsg.type = "aborted"
                 THEN /\ rmState' = [rmState EXCEPT ![tmsg.rm] = "aborted"]
                 ELSE /\ TRUE
                      /\ UNCHANGED rmState
           /\ pc' = [pc EXCEPT ![TM] = "incReceived"]
           /\ UNCHANGED << network, tmState, received, tmsg, rmsg, decision,
                           state, consensus >>

incReceived == /\ pc[TM] = "incReceived"
               /\ received' = received +1
               /\ pc' = [pc EXCEPT ![TM] = "loop"]
               /\ UNCHANGED << network, tmState, rmState, tmsg, rmsg, decision,
                               state, consensus >>

checkResult == /\ pc[TM] = "checkResult"
               /\ IF \A rm \in RM : rmState[rm] = "prepared"
                     THEN /\ tmState' = "committed"
                          /\ network' = broadcast(TM, [type |-> "Commit"])
                          /\ rmState' = [ rm \in RM |-> "committed" ]
                     ELSE /\ tmState' = "aborted"
                          /\ network' = broadcast(TM, [type |-> "Abort"])
                          /\ UNCHANGED rmState
               /\ pc' = [pc EXCEPT ![TM] = "Done"]
               /\ UNCHANGED << received, tmsg, rmsg, decision, state,
                               consensus >>

TManager == propose \/ loop \/ tmRcv \/ tmPrep \/ tmAbort \/ incReceived
               \/ checkResult

rmstart(self) == /\ pc[self] = "rmstart"
                 /\ IF consensus[self] = 0
                       THEN /\ pc' = [pc EXCEPT ![self] = "rcvLbl"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << network, tmState, rmState, received, tmsg,
                                 rmsg, decision, state, consensus >>

rcvLbl(self) == /\ pc[self] = "rcvLbl"
                /\ \E from \in { j \in 1..NumProcs : Len(network[j][self]) > 0 }:
                     /\ rmsg' = [rmsg EXCEPT ![self] = Head(network[from][self])]
                     /\ network' = [network EXCEPT ![from][self] = Tail(@)]
                /\ pc' = [pc EXCEPT ![self] = "rmPrep"]
                /\ UNCHANGED << tmState, rmState, received, tmsg, decision,
                                state, consensus >>

rmPrep(self) == /\ pc[self] = "rmPrep"
                /\ IF rmsg[self].type = "Prepare"
                      THEN /\ state[self] = "working"
                           /\ \/ /\ decision' = [decision EXCEPT ![self] = "prepared"]
                              \/ /\ decision' = [decision EXCEPT ![self] = "aborted"]
                           /\ state' = [state EXCEPT ![self] = decision'[self]]
                           /\ network' = send(self, TM, [type |-> decision'[self], rm |-> self])
                      ELSE /\ TRUE
                           /\ UNCHANGED << network, decision, state >>
                /\ pc' = [pc EXCEPT ![self] = "rmCommit"]
                /\ UNCHANGED << tmState, rmState, received, tmsg, rmsg,
                                consensus >>

rmCommit(self) == /\ pc[self] = "rmCommit"
                  /\ IF rmsg[self].type = "Commit"
                        THEN /\ consensus' = [consensus EXCEPT ![self] = 1]
                             /\ state' = [state EXCEPT ![self] = "committed"]
                        ELSE /\ TRUE
                             /\ UNCHANGED << state, consensus >>
                  /\ pc' = [pc EXCEPT ![self] = "rmAbort"]
                  /\ UNCHANGED << network, tmState, rmState, received, tmsg,
                                  rmsg, decision >>

rmAbort(self) == /\ pc[self] = "rmAbort"
                 /\ IF rmsg[self].type = "Abort"
                       THEN /\ consensus' = [consensus EXCEPT ![self] = 1]
                            /\ state' = [state EXCEPT ![self] = "aborted"]
                       ELSE /\ TRUE
                            /\ UNCHANGED << state, consensus >>
                 /\ pc' = [pc EXCEPT ![self] = "rmstart"]
                 /\ UNCHANGED << network, tmState, rmState, received, tmsg,
                                 rmsg, decision >>

RManager(self) == rmstart(self) \/ rcvLbl(self) \/ rmPrep(self)
                     \/ rmCommit(self) \/ rmAbort(self)

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
TMInv == /\ (tmState = "committed") => (\A rm \in RM : rmState[rm] = "prepared")
         /\ (tmState = "aborted") => (\E rm \in RM : rmState[rm] = "aborted")
         /\ (\E dst \in 1..NumProcs : (\E i \in 1..Len(network[TM][dst]) : network[TM][dst][i] = [type |-> "Commit"])) => (tmState =  "committed")
         /\ (\E dst \in 1..NumProcs : (\E i \in 1..Len(network[TM][dst]) : network[TM][dst][i] = [type |-> "Abort"])) => (tmState = "aborted")

(* invariant for the resource managers *)
RMInv(rm) ==
  /\ (\E i \in 1..Len(network[rm][TM]) : network[rm][TM][i] = [type |-> "prepared", rm |-> rm]) => (state[rm] = "prepared")
  /\ (state[rm]= "committed") => (tmState = "committed")
  /\ (state[rm]= "aborted") => (tmState = "aborted")

Inv == TypeOK /\ TMInv /\ (\A rm \in RM : RMInv(rm))

=============================================================================
\* Modification History
\* Last modified Thu Jun 21 14:59:52 PDT 2018 by rmc
\* Last modified Wed Oct 12 02:41:48 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
