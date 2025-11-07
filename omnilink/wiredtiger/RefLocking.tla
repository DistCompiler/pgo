---- MODULE RefLocking ----
EXTENDS TLC

CONSTANTS Owners, Locks

CONSTANT NoOwner

ASSUME NoOwner \notin Owners

VARIABLES lockInfo

OwnerOf(lock) ==
    IF   lock \in DOMAIN lockInfo
    THEN lockInfo[lock]
    ELSE NoOwner

Lock(owner, lock) ==
    /\ OwnerOf(lock) = NoOwner
    /\ lockInfo' = lockInfo @@ (lock :> owner)

Unlock(owner, lock) ==
    /\ OwnerOf(lock) = owner
    /\ lockInfo' = [l \in DOMAIN lockInfo \ {lock} |-> lockInfo[l] ]

Init ==
    /\ lockInfo = <<>>

Next ==
    \E owner \in Owners, lock \in Locks :
        \/ Lock(owner, lock)
        \/ Unlock(owner, lock) 

====