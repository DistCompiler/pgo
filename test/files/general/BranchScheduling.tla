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
    while (i < 10) {
    branchlabel:
        either {
            i := i + 1;
        } or {
            j := j + 5;
        } or {
            k := i + k;
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

archetype ANestedBranch() 
variable i = 0, j = 2, k= 4, mark = {};
{
loop:
    while (i < 10) {
    branchlabel:
        either {
            either {
                i := i + 1;
            } or {
                i := i + 2;
            } or {
                i := i + 3;
            } or {
                i := i + 4;
            }
        } or {
            either {
                j := j + 5;
            } or {
                j := j + j;
            }
        } or {
            either {
                k := i + k;
            } or {
                k := i + i + k;
            } or {
                k := i + i + i + k;
            }
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
process (Branch = 2) == instance ANestedBranch();

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
      if ((i) < (10)) {
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
        k := (i) + (k);
        goto lbl1;
      };
    lbl1:
      with (a \in TheSet) {
        mark := (mark) \union ({a});
        goto loop;
      };
  }
  
  process (Branch = 2)
    variables i0 = 0; j0 = 2; k0 = 4; mark0 = {};
  {
    loop:
      if ((i0) < (10)) {
        goto branchlabel;
      } else {
        goto Done;
      };
    branchlabel:
      either {
        either {
          i0 := (i0) + (1);
          goto lbl1;
        } or {
          i0 := (i0) + (2);
          goto lbl1;
        } or {
          i0 := (i0) + (3);
          goto lbl1;
        } or {
          i0 := (i0) + (4);
          goto lbl1;
        };
      } or {
        either {
          j0 := (j0) + (5);
          goto lbl1;
        } or {
          j0 := (j0) + (j0);
          goto lbl1;
        };
      } or {
        either {
          k0 := (i0) + (k0);
          goto lbl1;
        } or {
          k0 := ((i0) + (i0)) + (k0);
          goto lbl1;
        } or {
          k0 := (((i0) + (i0)) + (i0)) + (k0);
          goto lbl1;
        };
      };
    lbl1:
      with (a \in TheSet) {
        mark0 := (mark0) \union ({a});
        goto loop;
      };
  }
}

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====
