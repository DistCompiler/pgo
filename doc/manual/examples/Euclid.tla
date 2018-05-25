------------------------ MODULE Euclid ----------------------------
EXTENDS Naturals, TLC
CONSTANT N

(*
--algorithm Euclid {
(* @PGo{ arg N int }@PGo *)
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
===================================================================
