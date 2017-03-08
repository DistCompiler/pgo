----------------------- MODULE FastMutex -------------------------
EXTENDS Naturals, TLC
CONSTANT N

(*
--algorithm FastMutex {
  variables x,
            y = 0,
            b = [i \in 1..N |-> FALSE];
  process (Proc \in 1..N)
    variable j;
  {
      ncs: while (TRUE) {
             skip; \* the noncritical section

    start:   b[self] := TRUE;
      s01:   x := self;
       
      s02:   if (y # 0) {
      s03:     b[self] := FALSE;
      s04:     await y = 0; 
               goto start;
             };
             
      s05:   y := self;
      s06:   if (x # self) {
      s07:     b[self] := FALSE; 
               j := 1;
               
      s08:     while (j <= N) {
                 await ~b[j];
                 j := j+1; \* change to j+2 to see a violation of the assertion below
               };
               
      s09:     if (y # self) {  
      s10:       await y = 0; 
                 goto start;
               };
             };
       
       cs:   assert \A idx \in 1..N : (idx # self) => (pc[idx] # "cs"); \* critical section
      s11:   y := 0;
      s12:   b[self] := FALSE;       
           } \* end outer while
                 
  } \* end process block
} \* end algorithm
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ j = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "s01"]
               /\ UNCHANGED << x, y, j >>

s01(self) == /\ pc[self] = "s01"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "s02"]
             /\ UNCHANGED << y, b, j >>

s02(self) == /\ pc[self] = "s02"
             /\ IF y # 0
                   THEN /\ pc' = [pc EXCEPT ![self] = "s03"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s05"]
             /\ UNCHANGED << x, y, b, j >>

s03(self) == /\ pc[self] = "s03"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "s04"]
             /\ UNCHANGED << x, y, j >>

s04(self) == /\ pc[self] = "s04"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

s05(self) == /\ pc[self] = "s05"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "s06"]
             /\ UNCHANGED << x, b, j >>

s06(self) == /\ pc[self] = "s06"
             /\ IF x # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "s07"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j >>

s07(self) == /\ pc[self] = "s07"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j' = [j EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "s08"]
             /\ UNCHANGED << x, y >>

s08(self) == /\ pc[self] = "s08"
             /\ IF j[self] <= N
                   THEN /\ ~b[j[self]]
                        /\ j' = [j EXCEPT ![self] = j[self]+2]
                        /\ pc' = [pc EXCEPT ![self] = "s08"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s09"]
                        /\ j' = j
             /\ UNCHANGED << x, y, b >>

s09(self) == /\ pc[self] = "s09"
             /\ IF y # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "s10"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j >>

s10(self) == /\ pc[self] = "s10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ Assert(\A idx \in 1..N : (idx # self) => (pc[idx] # "cs"), 
                      "Failure of assertion at line 41, column 14.")
            /\ pc' = [pc EXCEPT ![self] = "s11"]
            /\ UNCHANGED << x, y, b, j >>

s11(self) == /\ pc[self] = "s11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "s12"]
             /\ UNCHANGED << x, b, j >>

s12(self) == /\ pc[self] = "s12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ s01(self) \/ s02(self)
                 \/ s03(self) \/ s04(self) \/ s05(self) \/ s06(self)
                 \/ s07(self) \/ s08(self) \/ s09(self) \/ s10(self)
                 \/ cs(self) \/ s11(self) \/ s12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

===================================================================
