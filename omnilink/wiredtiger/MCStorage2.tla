---- MODULE MCStorage2 ----
EXTENDS Storage, Functions

VARIABLE mtxnSnapshots2

txnStatus2 == [n \in Node |-> [tid \in ActiveTransactions(n) |->
    txnStatus[n][tid]
]]

Storage2 == INSTANCE Storage2 WITH
    mtxnSnapshots <- mtxnSnapshots2,
    txnStatus <- txnStatus2

StorageRefinesStorage2 ==
    Storage2!Init /\ [][Storage2!Next]_(Storage2!vars)

SnapshotsMatchWhenOverlapping ==
    \A s \in (DOMAIN mtxnSnapshots["n"] \cap DOMAIN mtxnSnapshots2["n"]) :
        mtxnSnapshots["n"][s] = mtxnSnapshots2["n"][s]

StateConstraint ==
    /\ Len(mlog["n"]) <= 3

MCStorage2Init ==
    /\ Init
    /\ mtxnSnapshots2 = [n \in Node |-> <<>>]

MCStorage2Next ==
    /\ Next
    /\ mtxnSnapshots2' = Storage2!updateMtxnSnapshots(mtxnSnapshots')

DebugAlias == [
    mlog |-> mlog,
    mtxnSnapshots |-> mtxnSnapshots,
    txnStatus |-> txnStatus,
    stableTs |-> stableTs,
    oldestTs |-> oldestTs,
    allDurableTs |-> allDurableTs,

    mtxnSnapshots2 |-> mtxnSnapshots2,
    txnStatus2 |-> txnStatus2
]

====
