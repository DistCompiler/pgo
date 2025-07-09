---- MODULE Storage ----
EXTENDS Sequences, Naturals, Integers, Util, TLC

\* 
\* Abstract model of single MongoDB node using WiredTiger storage instance.
\* 
\* This should more or less be the abstract transaction interface each shard
\* needs to consider when executing transactions that are part of distributed,
\* cross-shard transaction.
\* 
\* Status of each transaction operation can be "returned"/checked by a client
\* by checking the value of the 'txnStatus' variable after the execution of
\* an action/transition. This is a simple way to emulate the notion of
\* return/status codes in a standard programming-oriented API.
\* 


CONSTANT Keys 
CONSTANT MTxId
CONSTANT Timestamps

CONSTANT NoValue

CONSTANT Node
CONSTANT RC \* read concern.

VARIABLE mlog

VARIABLE mcommitIndex

\* Stores snapshots for running transactions on the underlying MongoDB instance.
VARIABLE mtxnSnapshots

\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

\* Tracks the global "stable timestamp" within the storage layer.
VARIABLE stableTs

\* Tracks the global "oldest timestamp" within the storage layer.
VARIABLE oldestTs

\* Tracks the global "all durable timestamp" within the storage layer.
VARIABLE allDurableTs

vars == <<mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs>>


\* Status codes for transaction operations.
STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"
STATUS_NOTFOUND == "WT_NOTFOUND"
STATUS_PREPARE_CONFLICT == "WT_PREPARE_CONFLICT"

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

\* Make values the same as transaction IDs.
Values == MTxId

\* The result a read will have if no value can be found.
NotFoundReadResult == [
    mlogIndex |-> 0,
    value |-> NoValue
]

\* Log entries contain one key-value pair each, modeled as a record
LogEntries ==
    [
        key: Keys,
        value: Values
    ]

Logs == Seq(LogEntries)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

--------------------------------------------------------

PrepareOrCommitTimestamps(n) == {IF "ts" \in DOMAIN e THEN e.ts ELSE  0 : e \in Range(mlog[n])}
CommitEntries(n, lg) == {e \in Range(lg[n]) : ("ts" \in DOMAIN e) /\ ("prepare" \notin DOMAIN e)}
CommitOnlyTimestamps(n, lg) == {e.ts : e \in CommitEntries(n, lg)}
CommitTimestamps(n) == {mlog[n][i].ts : i \in DOMAIN mlog[n]}

ActiveReadTimestamps(n) == { IF ~mtxnSnapshots[n][tx]["active"] THEN 0 ELSE mtxnSnapshots[n][tx].ts : tx \in DOMAIN mtxnSnapshots[n]}

\* Next timestamp to use for a transaction operation.
NextTs(n) == Max(PrepareOrCommitTimestamps(n) \cup ActiveReadTimestamps(n)) + 1

ActiveTransactions(n) == {tid \in MTxId : mtxnSnapshots[n][tid]["active"]}
PreparedTransactions(n) == {tid \in ActiveTransactions(n) : mtxnSnapshots[n][tid].prepared}

CommittedTransactions(n, txnSnapshots) == {tid \in MTxId : txnSnapshots[n][tid]["committed"]}

\* Currently in this model, where transactions don't set timestamps while they're in progress,
\* the all_durable will just be the same as the newest committed timestamp.
AllDurableTs(n) == IF CommittedTransactions(n, mtxnSnapshots') = {} THEN 0 ELSE Max(CommitOnlyTimestamps(n, mlog'))

\* 
\* Perform a snapshot read of a given key at timestamp.
\* 
\* That is, return the latest value associated with the key 
\* that was written at ts <= index. If no value was yet written
\* to the key, then return NotFoundReadResult.
\* 
SnapshotRead(n, key, ts) == 
    LET snapshotKeyWrites == 
        { i \in DOMAIN mlog[n] :
            /\ "data" \in DOMAIN mlog[n][i] \* exclude 'prepare' entries.
            /\ \E k \in DOMAIN mlog[n][i].data : k = key
            \* Determine read visibility based on commit timestamp.
            /\ mlog[n][i].ts <= ts } IN
        IF snapshotKeyWrites = {}
            THEN NotFoundReadResult
            ELSE [mlogIndex |-> Max(snapshotKeyWrites), value |-> mlog[n][Max(snapshotKeyWrites)].data[key]]

\* Snapshot of the full KV store at a given index/timestamp.
SnapshotKV(n, ts, rc, ignorePrepare) == 
    \* Local reads just read at the latest timestamp in the log.
    LET txnReadTs == IF rc = "snapshot" THEN ts ELSE Len(mlog[n]) IN
    [
        ts |-> txnReadTs,
        data |-> [k \in Keys |-> SnapshotRead(n, k, txnReadTs).value],
        prepared |-> FALSE,
        prepareTs |-> 0,
        aborted |-> FALSE,
        committed |-> FALSE,
        readSet |-> {},
        writeSet |-> {},
        active |-> TRUE,
        ignorePrepare |-> ignorePrepare
    ]
    

\* Not currently used but could be considered in future.
WriteReadConflictExists(n, tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running. 
        \/ /\ tid \in ActiveTransactions(n)
           /\ tOther \in ActiveTransactions(n)
           \* The other transaction is on the same snapshot and read this value.
           /\ mtxnSnapshots[tOther].ts = mtxnSnapshots[tOther].ts
           /\ k \in mtxnSnapshots[tOther].readSet

\* Does a write conflict exist for this transaction's write to a given key.
WriteConflictExists(n, tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in MTxId \ {tid}:
        \* Transaction is running concurrently. 
        \/ /\ tid \in ActiveTransactions(n)
           /\ tOther \in ActiveTransactions(n)
           /\ k \in mtxnSnapshots[n][tOther].writeSet
        \* If there exists another transaction that has written to this key and
        \* committed at a timestamp newer than your snapshot, this also should
        \* manifest as a conflict, since it implies this transaction may have
        \* overlapped with you (in timestamp order).
        \/ \E ind \in DOMAIN mlog[n] :
            /\ "data" \in DOMAIN mlog[n][ind]
            /\ mlog[n][ind].ts > mtxnSnapshots[n][tid].ts
            /\ k \in (DOMAIN mlog[n][ind].data)


TxnRead(n, tid, k) == 
    \* If a prepared transaction has committed behind our snapshot read timestamp
    \* while we were running, then we must observe the effects of its writes.
    IF  \E tOther \in MTxId \ {tid}:
        \E pmind \in DOMAIN mlog[n] :
        \E cmind \in DOMAIN mlog[n] :
            \* Prepare log entry exists.
            /\ "prepare" \in DOMAIN mlog[n][pmind]
            /\ mlog[n][pmind].tid = tOther
            \* Commit log entry exists and is at timestamp <= our snapshot.
            /\ "data" \in DOMAIN mlog[n][cmind]
            /\ mlog[n][cmind].tid = tOther
            /\ mlog[n][cmind].ts <= mtxnSnapshots[n][tid].ts
            /\ k \in DOMAIN mlog[n][cmind].data
            \* If we wrote to this key within our transaction, then we will always read our latest write.
            /\ k \notin mtxnSnapshots[n][tid].writeSet
        \* Snapshot read directly from the log.
        THEN SnapshotRead(n, k, mtxnSnapshots[n][tid].ts).value 
        \* Just read from your stored snapshot.
        ELSE mtxnSnapshots[n][tid].data[k]

UpdateSnapshot(tid, k, v) == [mtxnSnapshots EXCEPT ![tid].data[k] = v]

SnapshotUpdatedKeys(n, tid) == {
    k \in Keys : 
        /\ tid \in ActiveTransactions(n)
        /\ k \in mtxnSnapshots[n][tid]["writeSet"]
}

CommitLogEntry(n, tid, commitTs) == [
    data |-> [key \in SnapshotUpdatedKeys(n, tid) |-> mtxnSnapshots[n][tid].data[key]],
    ts |-> commitTs, 
    tid |-> tid
]

CommitTxnToLog(n, tid, commitTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog[n], CommitLogEntry(n, tid, commitTs))

CommitTxnToLogWithDurable(n, tid, commitTs, durableTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog[n], CommitLogEntry(n, tid, commitTs) @@ [durableTs |-> durableTs])


PrepareTxnToLog(n, tid, prepareTs) ==
    Append(mlog[n], [prepare |-> TRUE, ts |-> prepareTs, tid |-> tid])

TxnCanStart(n, tid, readTs) ==
    \* Cannot start a transaction at a timestamp T if there is another 
    \* currently prepared transaction at timestamp < T.
    ~\E tother \in MTxId :
        /\ tother \in ActiveTransactions(n)
        /\ mtxnSnapshots[tother].prepared 
        /\ mtxnSnapshots[tother].ts < readTs 

\* TODO/Question: If a transaction T1 starts at ts > P, and another transaction
\* then prepares after this at P, it appears that reads in WiredTiger from T1
\* don't actually encounter prepare conflicts (?) In MongoDB, is it ever
\* possible to prepare at a timestamp higher than an existing read timestamp? I
\* don't think so?

PrepareConflict(n, tid, k) ==
    \* Is there another transaction prepared at T <= readTs that has modified this key?
    \E tother \in MTxId :
        /\ tother # tid
        /\ tother \in ActiveTransactions(n)
        /\ mtxnSnapshots[n][tother].prepared
        /\ k \in SnapshotUpdatedKeys(n, tother)
        /\ mtxnSnapshots[n][tother].prepareTs <= mtxnSnapshots[n][tid].ts

---------------------------------------------------------------------

\* Checks the status of a transaction is OK after it has executed some enabled action.
TransactionPostOpStatus(n, tid) == txnStatus'[n][tid]

StartTransaction(n, tid, readTs, rc, ignorePrepare) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ tid \notin ActiveTransactions(n)
    \* Only run transactions for a given transactionid once.
    /\ ~mtxnSnapshots[n][tid]["committed"]
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Don't re-use transaction ids.
    /\ ~\E i \in DOMAIN (mlog[n]) : mlog[n][i].tid = tid
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid] = SnapshotKV(n, readTs, rc, ignorePrepare)]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs, oldestTs>>
    /\ allDurableTs' = [allDurableTs EXCEPT ![n] = AllDurableTs(n)]

\* Writes to the local KV store of a shard.
TransactionWrite(n, tid, k, v, ignoreWriteConflicts) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Transactions that ignore prepare cannot perform updates, though those with "force" can.
    /\ mtxnSnapshots[n][tid]["ignorePrepare"] # "true"
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(n, tid, k) \/ ignoreWriteConflicts = "true"
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["writeSet"] = @ \cup {k}, 
                                                    ![n][tid].data[k] = tid]
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
       \/ /\ WriteConflictExists(n, tid, k)
          /\ ignoreWriteConflicts = "false"
          \* If there is a write conflict, the transaction must roll back (i.e. it is aborted).
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs, oldestTs, allDurableTs>>

\* Reads from the local KV store of a shard.
TransactionRead(n, tid, k, v) ==
    /\ tid \in ActiveTransactions(n)    
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    /\ v = TxnRead(n, tid, k)
    /\ \/ /\ ~PrepareConflict(n, tid, k) \/ mtxnSnapshots[n][tid]["ignorePrepare"] \in {"true", "force"}
          /\ v # NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["readSet"] = @ \cup {k}]
       \* Key does not exist.
       \/ /\ ~PrepareConflict(n, tid, k) \/ mtxnSnapshots[n][tid]["ignorePrepare"] \in {"true", "force"}
          /\ v = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
      \* Prepare conflict (transaction is not aborted).
       \/ /\ PrepareConflict(n, tid, k)
          /\ mtxnSnapshots[n][tid]["ignorePrepare"] = "false"
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_PREPARE_CONFLICT]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs, oldestTs, allDurableTs>>

\* Delete a key.
TransactionRemove(n, tid, k) ==
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    /\ mtxnSnapshots[n][tid]["ignorePrepare"] = "false"
    /\ \/ /\ ~WriteConflictExists(n, tid, k)
          /\ TxnRead(n, tid, k) # NoValue 
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["writeSet"] = @ \cup {k}, 
                                                    ![n][tid].data[k] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
       \* If key does not exist in your snapshot then you can't remove it.
       \/ /\ ~WriteConflictExists(n, tid, k)
          /\ TxnRead(n, tid, k) = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
       \/ /\ WriteConflictExists(n, tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs, oldestTs, allDurableTs>>

CommitTransaction(n, tid, commitTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ commitTs > stableTs[n] 
    /\ tid \in ActiveTransactions(n)
    /\ tid \notin PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Must be greater than the newest known commit timestamp.
    /\ (ActiveReadTimestamps(n) \cup CommitTimestamps(n)) # {} => commitTs > Max(ActiveReadTimestamps(n) \cup CommitTimestamps(n))
    \* Commit the transaction on the KV store and write all updated keys back to the log.
    /\ mlog' = [mlog EXCEPT ![n] = CommitTxnToLog(n, tid, commitTs)]
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["committed"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ allDurableTs' = [allDurableTs EXCEPT ![n] = AllDurableTs(n)]
    /\ UNCHANGED <<mcommitIndex, stableTs, oldestTs>>

CommitPreparedTransaction(n, tid, commitTs, durableTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ commitTs = durableTs \* for now force these equal.
    /\ commitTs > stableTs[n] 
    /\ tid \in ActiveTransactions(n)
    /\ tid \in PreparedTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Commit timestamp must be at least as new as the prepare timestamp. Note
    \* that for prepared (i.e. distributed) transactions, though, commit
    \* timestamps may be chosen older than active read timestamps.
    /\ commitTs >= mtxnSnapshots[n][tid].prepareTs
    /\ mlog' = [mlog EXCEPT ![n] = CommitTxnToLogWithDurable(n, tid, commitTs, durableTs)]
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["committed"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ allDurableTs' = [allDurableTs EXCEPT ![n] = AllDurableTs(n)]
    /\ UNCHANGED <<mcommitIndex, stableTs, oldestTs>>

PrepareTransaction(n, tid, prepareTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ prepareTs > stableTs[n]
    /\ tid \in ActiveTransactions(n)
    /\ ~mtxnSnapshots[n][tid]["prepared"]
    /\ ~mtxnSnapshots[n][tid]["aborted"]
    \* Prepare timestamp mustn't be less than any active read timestamp
    \* (includes our own). For now, in this model, we impose the condition that
    \* prepare timesatmps are strictly greater than any read timestamp. This
    \* doesn't appear to be a strict requirement of the underlying WiredTiger
    \* API, but we enforce it for now since we expect MongoDB distributed
    \* transactions to obey this same contract.
    /\ prepareTs > Max(ActiveReadTimestamps(n))
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["prepared"] = TRUE, ![n][tid]["prepareTs"] = prepareTs]
    /\ mlog' = [mlog EXCEPT ![n] = PrepareTxnToLog(n,tid, prepareTs)]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mcommitIndex, stableTs, oldestTs, allDurableTs>>

AbortTransaction(n, tid) == 
    /\ tid \in ActiveTransactions(n)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![n][tid]["active"] = FALSE, ![n][tid]["aborted"] = TRUE]
    /\ txnStatus' = [txnStatus EXCEPT ![n][tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, mcommitIndex, stableTs, oldestTs, allDurableTs>>

SetStableTimestamp(n, ts) == 
    /\ ts > stableTs[n]
    /\ stableTs' = [stableTs EXCEPT ![n] = ts]
    /\ UNCHANGED <<mlog, mcommitIndex, mtxnSnapshots, txnStatus, oldestTs, allDurableTs>>

SetOldestTimestamp(n, ts) ==
    /\ ts > oldestTs[n]
    /\ ts <= stableTs[n]
    /\ oldestTs' = [oldestTs EXCEPT ![n] = ts]
    /\ UNCHANGED <<mlog, mcommitIndex, mtxnSnapshots, txnStatus, stableTs, allDurableTs>>

\* Roll back storage state to the stable timestamp.
RollbackToStable(n) == 
    \* Mustn't initiate a RTS call if there are any open transactions.
    /\ ActiveTransactions(n) = {}
    /\ stableTs[n] > 0 \* Stable timestamp has been set.
    \* Truncate all log operations at timestamps in front of the stable timestamp.
    /\ mlog' = [mlog EXCEPT ![n] = SelectSeq(mlog[n], LAMBDA op : op.ts <= stableTs[n])]
    /\ stableTs' = stableTs
    /\ UNCHANGED <<mtxnSnapshots, txnStatus, mcommitIndex, oldestTs, allDurableTs>>

\* Explicit initialization for each state variable.
Init_mlog == <<>>
Init_mcommitIndex == 0
Init_mtxnSnapshots == [t \in MTxId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]

Init == 
    /\ mlog = [n \in Node |-> <<>>]
    /\ mcommitIndex = [n \in Node |-> 0]
    /\ mtxnSnapshots = [n \in Node |-> [t \in MTxId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]]
    /\ txnStatus = [n \in Node |-> [t \in MTxId |-> STATUS_OK]]
    /\ stableTs = [n \in Node |-> -1]
    /\ oldestTs = [n \in Node |-> -1]
    /\ allDurableTs = [n \in Node |-> 0]

\* All ignore_prepare options. Can optionally be overwritten in configuration.
\* IgnorePrepareOptions == {"false", "true", "force"}
IgnorePrepareOptions == {"false"}

Next == 
    \/ \E n \in Node : \E tid \in MTxId, readTs \in Timestamps, ignorePrepare \in IgnorePrepareOptions : StartTransaction(n, tid, readTs, RC, ignorePrepare)
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys, v \in Values : TransactionWrite(n, tid, k, v, "false")
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys, v \in (Values \cup {NoValue}) : TransactionRead(n, tid, k, v)
    \/ \E n \in Node : \E tid \in MTxId, k \in Keys : TransactionRemove(n, tid, k)
    \/ \E n \in Node : \E tid \in MTxId, prepareTs \in Timestamps : PrepareTransaction(n, tid, prepareTs)
    \/ \E n \in Node : \E tid \in MTxId, commitTs \in Timestamps : CommitTransaction(n, tid, commitTs)
    \/ \E n \in Node : \E tid \in MTxId, commitTs, durableTs \in Timestamps : CommitPreparedTransaction(n, tid, commitTs, durableTs)
    \/ \E n \in Node : \E tid \in MTxId : AbortTransaction(n, tid)
    \/ \E n \in Node : \E ts \in Timestamps : SetStableTimestamp(n, ts)
    \/ \E n \in Node : \E ts \in Timestamps : SetOldestTimestamp(n, ts)
    \/ \E n \in Node : RollbackToStable(n)


---------------------------------------------------------------------

Symmetry == Permutations(MTxId) \cup Permutations(Keys)

===============================================================================