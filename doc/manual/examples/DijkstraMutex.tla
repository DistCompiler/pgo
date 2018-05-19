--------------------------- MODULE DijkstraMutex ---------------------------
EXTENDS Integers
(***************************************************************************)
(* There is no reason why the processes need to be numbered from 1 to N.   *)
(* So, we assume an arbitrary set Proc of process names.                   *)
(***************************************************************************)
CONSTANT Proc 

(*********
Here is the PlusCal version of this algorithm.
The algorithm was modified from the original by adding the variable temp2,
to avoid a type consistency conflict when temp changes type at Li4a.
(* @PGo{ def Proc == 1 .. 10 }@PGo
   @PGo{ lock false }@PGo
*)

 --algorithm Mutex 
 { variables b = [i \in Proc |-> TRUE], c = [i \in Proc |-> TRUE], k \in Proc;
   process (P \in Proc)
     variable temp, temp2 ;
     { Li0: while (TRUE)
             {      b[self] := FALSE;
               Li1: if (k # self) { Li2: c[self] := TRUE;
                                   Li3a: temp := k;
                                   Li3b: if (b[temp]) { Li3c: k := self } ;
                                   Li3d: goto Li1
                                  };
              Li4a: c[self] := FALSE;
                    temp2 := Proc \ {self};
              Li4b: while (temp2 # {})
                     { with (j \in temp2) 
                        { temp2 := temp2 \ {j};
                          if (~c[j]) { goto Li1 }
                        }
                     };                       
                cs: skip;  \* the critical section
               Li5: c[self] := TRUE;
               Li6: b[self] := TRUE;
               ncs: skip  \* non-critical section ("remainder of cycle")
             }
     }
 }
*********)
=============================================================================
