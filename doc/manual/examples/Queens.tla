-------------------------- MODULE QueensPluscal -----------------------------
EXTENDS Naturals, Sequences
(***************************************************************************)
(* Formulation of the N-queens problem and an iterative algorithm to solve *)
(* the problem in TLA+. Since there must be exactly one queen in every row *)
(* we represent placements of queens as functions of the form              *)
(*    queens \in [ 1..N -> 1..N ]                                          *)
(* where queens[i] gives the column of the queen in row i. Note that such  *)
(* a function is just a sequence of length N.                              *)
(* We will also consider partial solutions, also represented as sequences  *)
(* of length \leq N.                                                       *)
(***************************************************************************)

CONSTANT N              \** number of queens and size of the board
ASSUME N \in Nat \ {0}

(* The following predicate determines if queens i and j attack each other
   in a placement of queens (represented by a sequence as above). *)
Attacks(queens,i,j) ==
  \/ queens[i] = queens[j]                 \** same column
  \/ queens[i] - queens[j] = i - j         \** first diagonal
  \/ queens[j] - queens[i] = i - j         \** second diagonal

(* A placement represents a (partial) solution if no two different queens
   attack each other in it. *)
IsSolution(queens) ==
  \A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) : 
       ~ Attacks(queens,i,j)

(***************************************************************************)
(* We now describe an algorithm that iteratively computes the set of       *)
(* solutions of the N-queens problem by successively placing queens.       *)
(* The current state of the algorithm is given by two variables:           *)
(* - todo contains a set of partial solutions,                             *)
(* - sols contains the set of full solutions found so far.                 *)
(* At every step, the algorithm picks some partial solution and computes   *)
(* all possible extensions by the next queen. If N queens have been placed *)
(* these extensions are in fact full solutions, otherwise they are added   *)
(* to the set todo.                                                        *)
(***************************************************************************)

(* --algorithm QueensPluscal
     (**  @PGo{ arg N int }@PGo
          @PGo{ var todo set[[]int] }@PGo
          @PGo{ var sols set[[]int] }@PGo
          @PGo{ def Attacks(queens []int,i int,j int) ==
                \/ queens[i] = queens[j]                 \** same column
                \/ queens[i] - queens[j] = i - j         \** first diagonal
                \/ queens[j] - queens[i] = i - j         \** second diagonal }@PGo
          @PGo{ def IsSolution(queens []int) ==
                \A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) : 
                ~ Attacks(queens,i,j) }@PGo **)
     variables
       todo = { << >> };
       sols = {};

     begin
nxtQ:  while todo # {}
       do
         with queens \in todo,
              nxtQ = Len(queens) + 1,
              cols = { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                      Attacks( Append(queens, c), i, nxtQ ) },
              exts = { Append(queens,c) : c \in cols }
         do
           if (nxtQ = N)
           then todo := todo \ {queens}; sols := sols \union exts;
           else todo := (todo \ {queens}) \union exts;
           end if;
         end with;
       end while;
     end algorithm
*)
=============================================================================
