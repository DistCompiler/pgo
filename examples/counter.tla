--------------------------- MODULE round_robin ---------------------------

EXTENDS Integers, TLC

CONSTANT procs, iters

(*

--algorithm round_robin {
  (** @PGo{ arg procs int }@PGo
      @PGo{ arg iters int }@PGo
   **)
  variables counter = 0;

  fair process (P \in 0..procs-1)
  variables i = 0;
  {
      w: while (i < iters) {
          incCounter: counter := counter + 1;
                      print counter;
          nextIter:   i := i + 1;
      }
  }
}
*)

====