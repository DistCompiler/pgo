---- MODULE RefLocking ----

CONSTANTS Owners, Locks

CONSTANT NoOwner

ASSUME NoOwner \notin Owners

VARIABLES lockInfo

Lock(owner, lock) ==
    /\ lockInfo[lock] = NoOwner
    /\ lockInfo' = [lockInfo EXCEPT ![lock] = owner]

Unlock(owner, lock) ==
    /\ lockInfo[lock] = owner
    /\ lockInfo' = [lockInfo EXCEPT ![lock] = NoOwner]

Init ==
    /\ lockInfo = [l \in Locks |-> NoOwner]

Next ==
    \E owner \in Owners, lock \in Locks :
        \/ Lock(owner, lock)
        \/ Unlock(owner, lock) 

====