---- MODULE simple ----
EXTENDS Naturals, TLC

VARIABLE x, y

Inc ==
    /\ x ' = x + 1
    /\ UNCHANGED y

UseTLC == TLCGet("level") < 2

\* after UseTLC is ignored #251 *\

List == /\ x = 1
        /\ x = 2

Init == x = 1

====