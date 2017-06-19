------------------------ MODULE Euclid ----------------------------
EXTENDS Naturals, TLC
CONSTANT N

(*
\** @PGo{ annotation with \** before algorithm }@PGo
(** @PGo{ annotation with (* *) before algorithm !!! <- this end is missing ***)
\** asljl ** a @PGo{ annotation with other string in \* comment }@PGo lkjlkjl * } 
(* asljl ** a @PGo{ annotation with other string in (* *) comment }@PGo lkjlkjl * } *)
\** @PGo not annotation @PGo
\** @PGo{ test }@Pgo }PGo @PGo @PGo} PGo{ } @PGo still part of annotation }@PGo
\** @PGo{no space}@PGo
\** @PGo{              many space          }@PGo
(* @PGo{ many per line1 }@PGo not annotage @PGo{ more annote }@PGo
   @PGo{ multiline }@PGo @PGo{ more multiline }@PGo
   not pgo
   @PGo{ even more lines }@PGo
   not pgo now
*)

--algorithm Annotation {    \** @PGo{ annotation with \** comment on code line }@PGo
  \** @PGo{ annotation with \** on separate line }@PGo
  variables a; \** asljl ** a @PGo{ annotation with other string in \* comment }@PGo lkjlkjl * } 
  {
    print <<a>>
  }
}

\** @PGo{ still part of annotation }@PGo

*)

===================================================================
