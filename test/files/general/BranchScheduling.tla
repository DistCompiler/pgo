---- MODULE BranchScheduling ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

(*

--mpcal BranchScheduling {

define {
    TheSet == {1, 2}
}

archetype ABranch() 
variable i = 0, j = 2, k= 4, mark = {};
{
loop:
    while (i < 20) {
    branchlabel:
        either {
            i := i + 1;
        } or {
            j := j + 5;
        } or {
            k := j + k;
        };            
    lbl1:
        with (a \in TheSet) {
            mark := mark \cup {a};
        };
    \* lbl2:
    \*     i := i + 1;
    \* };
    };
}

process (Branch = 1) == instance ABranch();

}

\* BEGIN PLUSCAL TRANSLATION
--algorithm BranchScheduling {
  define{
    TheSet == {1, 2}
  }
  
  process (Branch = 1)
    variables i = 0; j = 2; k = 4; mark = {};
  {
    loop:
      if ((i) < (20)) {
        goto branchlabel;
      } else {
        goto Done;
      };
    branchlabel:
      either {
        i := (i) + (1);
        goto lbl1;
      } or {
        j := (j) + (5);
        goto lbl1;
      } or {
        k := (j) + (k);
        goto lbl1;
      };
    lbl1:
      with (a \in TheSet) {
        mark := (mark) \union ({a});
        goto loop;
      };
  }
}

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====
