---- MODULE MCStorage2 ----
EXTENDS Storage, Functions, TLCExt

mtxnSnapshots2 == TLCCache([n \in Node |->
    Restrict(mtxnSnapshots[n], { tid \in DOMAIN mtxnSnapshots[n] :
        \lnot \/ /\ \lnot mtxnSnapshots[n][tid].active
                 /\ \lnot mtxnSnapshots[n][tid].committed
                 /\ \lnot mtxnSnapshots[n][tid].aborted
              \/ /\ \lnot mtxnSnapshots[n][tid].active
                 /\ mtxnSnapshots[n][tid].aborted
              \/ /\ \lnot mtxnSnapshots[n][tid].active
                 /\ mtxnSnapshots[n][tid].committed
                 /\ "ts" \in DOMAIN mtxnSnapshots[n][tid]
                 /\ \E tid2 \in DOMAIN mtxnSnapshots[n] :
                        /\ tid2 # tid
                        /\ mtxnSnapshots[n][tid2].committed
                        /\ "ts" \in DOMAIN mtxnSnapshots[n][tid2]
                        /\ mtxnSnapshots[n][tid].ts < mtxnSnapshots[n][tid2].ts
    })
], {})

txnStatus2 == TLCCache([n \in Node |->
    Restrict(txnStatus[n], { tid \in DOMAIN txnStatus[n] :
        /\ tid \in DOMAIN mtxnSnapshots2[n]
        /\ mtxnSnapshots2[n][tid].active
    })
], {})

Storage2 == INSTANCE Storage2 WITH
    mtxnSnapshots <- mtxnSnapshots2,
    txnStatus <- txnStatus2

StorageRefinesStorage2 ==
    Storage2!Init /\ [][Storage2!Next]_(Storage2!vars)

StateConstraint ==
    /\ Len(mlog["n"]) <= 3

MCStorage2Init == Init

MCStorage2Next == Next

DebugAlias == [
    mlog |-> mlog,
    mtxnSnapshots |-> mtxnSnapshots,
    txnStatus |-> txnStatus,
    stableTs |-> stableTs,
    oldestTs |-> oldestTs,
    allDurableTs |-> allDurableTs,

    mtxnSnapshots2 |-> mtxnSnapshots2,
    txnStatus2 |-> txnStatus2,

    ActiveTransactions |-> [n \in Node |-> ActiveTransactions(n)],
    PreparedTransactions |-> [n \in Node |-> PreparedTransactions(n)],
    AllDurableTs |-> [n \in Node |-> AllDurableTs(n)],
    
    ActiveTransactions2 |-> [n \in Node |-> Storage2!ActiveTransactions(n)],
    PreparedTransactions2 |-> [n \in Node |-> Storage2!PreparedTransactions(n)],
    AllDurableTs2 |-> [n \in Node |-> Storage2!AllDurableTs(n)]

    \* branches |-> UNION {
    \*     LET EN(str, action) ==
    \*         IF ENABLED (action)
    \*         THEN {str}
    \*         ELSE {}
    \*     IN
    \*     UNION {
    \*         EN("StartTransaction", StartTransaction(n, tid, readTs, RC, ignorePrepare)),
    \*         EN("TransactionWrite", TransactionWrite(n, tid, k, v, "false")),
    \*         EN("TransactionRead", TransactionRead(n, tid, k, v)),
    \*         EN("TransactionRemove", TransactionRemove(n, tid, k)),
    \*         EN("CommitTransaction", CommitTransaction(n, tid, commitTs)),
    \*         EN("CommitPreparedTransaction", CommitPreparedTransaction(n, tid, commitTs, durableTs)),
    \*         EN("AbortTransaction", AbortTransaction(n, tid)),
    \*         EN("SetStableTimestamp", SetStableTimestamp(n, ts)),
    \*         EN("SetStableTimestamp", SetStableTimestamp(n, ts)),
    \*         EN("SetOldestTimestamp", SetOldestTimestamp(n, ts)),
    \*         EN("RollbackToStable", RollbackToStable(n))
    \*     }
    \*     :
    \*     n \in Node,
    \*     tid \in MTxId,
    \*     readTs \in Timestamps,
    \*     ignorePrepare \in IgnorePrepareOptions,
    \*     k \in Keys,
    \*     v \in (Values \cup {NoValue}),
    \*     prepareTs \in Timestamps,
    \*     commitTs \in Timestamps,
    \*     durableTs \in Timestamps,
    \*     ts \in Timestamps
    \* },

    \* branches2 |-> UNION {
    \*     LET EN(str, action) ==
    \*         IF ENABLED (Next /\ action)
    \*         THEN {str}
    \*         ELSE {}
    \*     IN
    \*     UNION {
    \*         EN("StartTransaction", Storage2!StartTransaction(n, tid, readTs, RC, ignorePrepare)),
    \*         EN("TransactionWrite", Storage2!TransactionWrite(n, tid, k, v, "false")),
    \*         EN("TransactionRead", Storage2!TransactionRead(n, tid, k, v)),
    \*         EN("TransactionRemove", Storage2!TransactionRemove(n, tid, k)),
    \*         EN("CommitTransaction", Storage2!CommitTransaction(n, tid, commitTs)),
    \*         EN("CommitPreparedTransaction", Storage2!CommitPreparedTransaction(n, tid, commitTs, durableTs)),
    \*         EN("AbortTransaction", Storage2!AbortTransaction(n, tid)),
    \*         EN("SetStableTimestamp", Storage2!SetStableTimestamp(n, ts)),
    \*         EN("SetStableTimestamp", Storage2!SetStableTimestamp(n, ts)),
    \*         EN("SetOldestTimestamp", Storage2!SetOldestTimestamp(n, ts)),
    \*         EN("RollbackToStable", Storage2!RollbackToStable(n))
    \*     }
    \*     :
    \*     n \in Node,
    \*     tid \in MTxId,
    \*     readTs \in Timestamps,
    \*     ignorePrepare \in IgnorePrepareOptions,
    \*     k \in Keys,
    \*     v \in (Values \cup {NoValue}),
    \*     prepareTs \in Timestamps,
    \*     commitTs \in Timestamps,
    \*     durableTs \in Timestamps,
    \*     ts \in Timestamps
    \* }
]

====
