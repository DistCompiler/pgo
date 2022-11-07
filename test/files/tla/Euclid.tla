------------------------ MODULE Euclid ----------------------------
EXTENDS Naturals, TLC
CONSTANT N

(*
--algorithm Euclid {
  variables u = 24;
            v \in 1 .. N;
            v_init = v;
  {
  a:  while (u # 0) {
      if (u < v) {
          u := v || v := u;
      };
  b:    u := u - v;
    };
    print <<24, v_init, "have gcd", v>>
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES u, v, v_init, pc

vars == << u, v, v_init, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. N
        /\ v_init = v
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ /\ u' = v
                              /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ PrintT(<<24, v_init, "have gcd", v>>)
                /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED v_init

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << v, v_init >>

Next == a \/ b
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
===================================================================
