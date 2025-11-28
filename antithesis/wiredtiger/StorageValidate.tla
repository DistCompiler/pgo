---- MODULE StorageValidate ----
EXTENDS Integers

CONSTANTS Keys, MTxId, Timestamps, NoValue, Node, RC
VARIABLES mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs

__Spec == INSTANCE Storage

VARIABLES __pc, __viable_pids, __action

__Spec_vars == <<mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs>>
__vars == <<__Spec_vars, __pc, __viable_pids, __action>>
__state == [mlog |-> mlog, mcommitIndex |-> mcommitIndex, mtxnSnapshots |-> mtxnSnapshots, txnStatus |-> txnStatus, stableTs |-> stableTs, oldestTs |-> oldestTs, allDurableTs |-> allDurableTs, __pc |-> __pc, __viable_pids |-> __viable_pids, __action |-> __action]

__tracefile_name == "StorageValidateData.bin"

__TraceOps == INSTANCE __TraceOps

__efficientView == __TraceOps!efficientView

__AtEndOfTracePC == __TraceOps!AtEndOfTracePC

__TerminateAtEnd == __TraceOps!TerminateAtEnd

__traces == __TraceOps!traces

Init ==
    /\ __Spec!Init
    /\ __TraceOps!Init

__AbortBehavior ==
    UNCHANGED __Spec_vars

__Action_StartTransaction == TRUE

__Action_TransactionWrite == TRUE

__Action_TransactionRead == TRUE

__Action_TransactionRemove == TRUE

__Action_PrepareTransaction == TRUE

__Action_CommitTransaction == TRUE

__Action_CommitPreparedTransaction == TRUE

__Action_AbortTransaction == TRUE

__Action_SetStableTimestamp == TRUE

__Action_SetOldestTimestamp == TRUE

__Action_RollbackToStable == TRUE

Next ==
    \E __pid \in __viable_pids :
      LET __event == __traces[__pid][__pc[__pid]]
          __op_name == __event.operation_name
             __op == __event.operation
      IN  \/ /\ __op._did_abort
             /\ __action' = __event
             /\ __pc' = [__pc EXCEPT ![__pid] = @ + 1]
             /\ __viable_pids' = __TraceOps!ViablePIDs'
             /\ __AbortBehavior
          \/ /\ \lnot __op._did_abort
             /\ __action' = __event
             /\ CASE __op_name = "StartTransaction" -> __Spec!StartTransaction(__op.n, __op.tid, __op.readTs, __op.rc, __op.ignorePrepare) /\ __Action_StartTransaction
                  [] __op_name = "TransactionWrite" -> __Spec!TransactionWrite(__op.n, __op.tid, __op.k, __op.v, __op.ignoreWriteConflicts) /\ __Action_TransactionWrite
                  [] __op_name = "TransactionRead" -> __Spec!TransactionRead(__op.n, __op.tid, __op.k, __op.v) /\ __Action_TransactionRead
                  [] __op_name = "TransactionRemove" -> __Spec!TransactionRemove(__op.n, __op.tid, __op.k) /\ __Action_TransactionRemove
                  [] __op_name = "PrepareTransaction" -> __Spec!PrepareTransaction(__op.n, __op.tid, __op.prepareTs) /\ __Action_PrepareTransaction
                  [] __op_name = "CommitTransaction" -> __Spec!CommitTransaction(__op.n, __op.tid, __op.commitTs) /\ __Action_CommitTransaction
                  [] __op_name = "CommitPreparedTransaction" -> __Spec!CommitPreparedTransaction(__op.n, __op.tid, __op.commitTs, __op.durableTs) /\ __Action_CommitPreparedTransaction
                  [] __op_name = "AbortTransaction" -> __Spec!AbortTransaction(__op.n, __op.tid) /\ __Action_AbortTransaction
                  [] __op_name = "SetStableTimestamp" -> __Spec!SetStableTimestamp(__op.n, __op.ts) /\ __Action_SetStableTimestamp
                  [] __op_name = "SetOldestTimestamp" -> __Spec!SetOldestTimestamp(__op.n, __op.ts) /\ __Action_SetOldestTimestamp
                  [] __op_name = "RollbackToStable" -> __Spec!RollbackToStable(__op.n) /\ __Action_RollbackToStable
             /\ __pc' = [__pc EXCEPT ![__pid] = @ + 1]
             /\ __viable_pids' = __TraceOps!ViablePIDs'
====
      