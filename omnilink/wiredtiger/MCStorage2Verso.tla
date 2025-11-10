---- MODULE MCStorage2Verso ----
EXTENDS Storage2, Functions, TLCExt

VARIABLE mtxnSnapshots1
\* mtxnSnapshots1 == [n \in Node |->
\*     [tid \in MTxId |->
\*         IF   tid \in DOMAIN mtxnSnapshots[n]
\*         THEN mtxnSnapshots[n][tid]
\*         ELSE [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]
\*     ]
\* ]

txnStatus1 == [n \in Node |->
    [tid \in MTxId |->
        IF   tid \in DOMAIN txnStatus[n]
        THEN txnStatus[n][tid]
        ELSE STATUS_OK
    ]
]

Storage == INSTANCE Storage WITH
    mtxnSnapshots <- mtxnSnapshots1,
    txnStatus <- txnStatus1

Storage2RefinesStorage ==
    Storage!Init /\ [][Storage!Next]_(Storage!vars)

StateConstraint ==
    /\ Len(mlog["n"]) <= 3

DontUnabort ==
    \A n \in Node, tid \in MTxId :
        mtxnSnapshots1[n][tid].aborted => mtxnSnapshots1'[n][tid].aborted
DontUncommit ==
    \A n \in Node, tid \in MTxId :
        mtxnSnapshots1[n][tid].committed => mtxnSnapshots1'[n][tid].committed

SnapshotsMatch ==
    \A n \in Node : \A tid \in DOMAIN mtxnSnapshots[n] :
        mtxnSnapshots1[n][tid] = mtxnSnapshots[n][tid]

MCStorage2VersoInit ==
    /\ Init
    /\ mtxnSnapshots1 = [n \in Node |-> [t \in MTxId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]]

MCStorage2VersoNext ==
    /\ Next
    /\ mtxnSnapshots1' = [n \in Node |->
          [tid \in DOMAIN mtxnSnapshots1[n] |->
             IF   /\ tid \in DOMAIN mtxnSnapshots[n]
                  /\ tid \notin DOMAIN mtxnSnapshots'[n]
             THEN CASE /\ mtxnSnapshots[n][tid].active
                       /\ mlog'[n] # <<>>
                       /\ Last(mlog'[n]).tid = tid
                       /\ "data" \in DOMAIN Last(mlog'[n]) ->
                        [mtxnSnapshots1[n][tid] EXCEPT
                            !.committed = TRUE,
                            !.active = FALSE
                        ]
                    [] mtxnSnapshots[n][tid].active ->
                        [mtxnSnapshots1[n][tid] EXCEPT
                            !.aborted = TRUE,
                            !.active = FALSE
                        ]
                    [] OTHER ->
                        mtxnSnapshots[n][tid]
             ELSE IF   tid \in DOMAIN mtxnSnapshots'[n]
                  THEN mtxnSnapshots'[n][tid]
                  ELSE mtxnSnapshots1[n][tid]
          ]
       ]
    \* Disallow rerunning an old transaction.
    \* It's possible because our model is "forgetful",
    \* but otherwise benign. Our runner should not be
    \* doing this.
    /\ DontUnabort
    /\ DontUncommit

DebugAlias == [
    mlog |-> mlog,
    mtxnSnapshots |-> mtxnSnapshots,
    txnStatus |-> txnStatus,
    stableTs |-> stableTs,
    oldestTs |-> oldestTs,
    allDurableTs |-> allDurableTs,

    mtxnSnapshots1 |-> mtxnSnapshots1,
    txnStatus1 |-> txnStatus1,

    ActiveTransactions |-> [n \in Node |-> ActiveTransactions(n)],
    PreparedTransactions |-> [n \in Node |-> PreparedTransactions(n)],
    AllDurableTs |-> [n \in Node |-> AllDurableTs(n)],
    
    ActiveTransactions1 |-> [n \in Node |-> Storage!ActiveTransactions(n)],
    PreparedTransactions1 |-> [n \in Node |-> Storage!PreparedTransactions(n)],
    AllDurableTs1 |-> [n \in Node |-> Storage!AllDurableTs(n)]
]

====
