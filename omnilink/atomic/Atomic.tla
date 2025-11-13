---- MODULE Atomic ----
EXTENDS Integers

VARIABLE x

Inc(prev_x) ==
    /\ prev_x = x
    /\ x' = x + 1

Init ==
    x = 1

Next ==
    Inc(x)

====