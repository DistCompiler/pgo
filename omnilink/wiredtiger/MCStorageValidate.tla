---- MODULE MCStorageValidate ----
EXTENDS StorageValidate, TLC, TLCExt, Bags, Sequences

WT_ROLLBACK == -31800
WT_NOTFOUND == -31803
WT_PREPARE_CONFLICT == -31808

TimestampsImpl == {} \* stub, we don't use it
SymmetryImpl == {} \* also stub

KeysImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  IF "k" \in DOMAIN __rec.operation
        THEN {__rec.operation.k}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"KeysImpl"})

MTxIdImpl == TLCCache(UNION UNION { {
    LET __rec == __traces[t][i]
    IN  IF "tid" \in DOMAIN __rec.operation
        THEN {__rec.operation.tid}
        ELSE {}
    : i \in DOMAIN __traces[t] }
    : t \in DOMAIN __traces }, {"MtxIdImpl"})

NoValueImpl == -1

DebugAlias == __TraceOps!DebugAlias

ResultCodeToTxnStatus == (
    (WT_ROLLBACK :> __Spec!STATUS_ROLLBACK)
    @@ (WT_NOTFOUND :> __Spec!STATUS_NOTFOUND)
    @@ (WT_PREPARE_CONFLICT :> __Spec!STATUS_PREPARE_CONFLICT) 
)

__AbortBehaviorImpl ==
    CASE __action'.operation_name = "TransactionWrite" ->
            /\ __action'.operation._meta.result_code # 0
            /\ __Spec!TransactionWrite(__action'.operation.n, __action'.operation.tid, __action'.operation.k, __action'.operation.v, __action'.operation.ignoreWriteConflicts)
            /\ txnStatus'["n"][__action'.operation.tid] = ResultCodeToTxnStatus[__action'.operation._meta.result_code]
      [] __action'.operation_name = "TransactionRead" ->
            /\ __action'.operation._meta.result_code # 0
            /\ __Spec!TransactionRead(__action'.operation.n, __action'.operation.tid, __action'.operation.k, __action'.operation.v)
            /\ txnStatus'["n"][__action'.operation.tid] = ResultCodeToTxnStatus[__action'.operation._meta.result_code]
      [] __action'.operation_name = "TransactionRemove" ->
            /\ __action'.operation._meta.result_code # 0
            /\ __Spec!TransactionRemove(__action'.operation.n, __action'.operation.tid, __action'.operation.k)
            /\ txnStatus'["n"][__action'.operation.tid] = ResultCodeToTxnStatus[__action'.operation._meta.result_code]
      [] OTHER -> UNCHANGED __Spec_vars

__Action_TransactionWriteImpl ==
    /\ __action'.operation._meta.result_code = 0
    /\ txnStatus'["n"][__action'.operation.tid] = "OK"

__Action_TransactionReadImpl ==
    /\ __action'.operation._meta.result_code = 0
    /\ txnStatus'["n"][__action'.operation.tid] = "OK"

__Action_TransactionRemoveImpl ==
    /\ __action'.operation._meta.result_code = 0
    /\ txnStatus'["n"][__action'.operation.tid] = "OK"

mlogNoOrder ==
    BagUnion({
        SetToBag({mlog[idx]})
        : idx \in DOMAIN mlog
    })

mtxnSnapshotsView ==
    [n \in DOMAIN mtxnSnapshots |->
        [tid \in DOMAIN mtxnSnapshots[n] |->
            LET snap == mtxnSnapshots[n][tid]
            IN  IF   \lnot snap.active
                THEN [snap EXCEPT !.data = <<>>]
                ELSE snap
        ]
    ]

PragmaticView ==
    __pc
    \* [
    \*     __action |-> <<>>,
    \*     __viable__pids |-> {},
    \*     mlog |-> <<>>,
    \*     mtxnSnapshots |-> <<>>,
    \*     txnStatus |-> <<>>,
    \*     allDurableTs |-> <<>>
    \* ] @@ __state

TAG_HasTransactionConflict(op) ==
    \E tid \in DOMAIN mtxnSnapshots["n"] \ {op.operation.tid} :
        /\ mtxnSnapshots["n"][tid].active
        /\ \/ op.operation.k \in mtxnSnapshots["n"][tid].readSet
            \/ op.operation.k \in mtxnSnapshots["n"][tid].writeSet

__TAG_ConflictsWithOtherTransaction(pid, op) ==
    /\ op.operation_name \in {"TransactionRemove", "TransactionWrite"}
    /\ op.operation._meta.result_code \in {WT_NOTFOUND, 0}
    /\ TAG_HasTransactionConflict(op)

__TAG_FailedRemoveDoesntConflict(pid, op) ==
    /\ op.operation_name = "TransactionRemove"
    /\ op.operation._meta.result_code = WT_NOTFOUND
    /\ TAG_HasTransactionConflict(op)

====