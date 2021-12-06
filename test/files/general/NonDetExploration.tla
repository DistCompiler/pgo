---- MODULE NonDetExploration ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

(*

--mpcal NonDetExploration {

define {
    TheSet == {1, 2}
}

archetype ACoverage() {
l1:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 1;
    };
l2:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 2;
    };
l3:
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 1;
    };
l4:
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 2;
    };
}

archetype ACoincidence() {
lbl:
    with(a \in TheSet, b \in TheSet) {
        await a = 1 /\ b = 1;
    };
    with(a \in TheSet, b \in TheSet) {
        await a = 2 /\ b = 2;
    };
}

archetype AComplex() 
variable i = 0, mark = {};
{
loop:
    while (i < 20) {
    lbl1:
        with (a \in TheSet) {
            mark := mark \cup {a};
        };
    lbl2:
        i := i + 1;
    };
    \* with high probability (1 - 2 / 2^20) this assertion is true.
    assert \A a \in TheSet: a \in mark;
}

process (Coverage = 1) == instance ACoverage();

process (Coincidence = 2) == instance ACoincidence();

process (Complex = 3) == instance AComplex();

}

\* BEGIN PLUSCAL TRANSLATION
--algorithm NonDetExploration {
  define{
    TheSet == {1, 2}
  }
  
  process (Coverage = 1)
  {
    l1:
      with (
        a \in TheSet, 
        b \in TheSet
      ) {
        await ((a) = (1)) /\ ((b) = (1));
        goto l2;
      };
    l2:
      with (
        a \in TheSet, 
        b \in TheSet
      ) {
        await ((a) = (1)) /\ ((b) = (2));
        goto l3;
      };
    l3:
      with (
        a \in TheSet, 
        b \in TheSet
      ) {
        await ((a) = (2)) /\ ((b) = (1));
        goto l4;
      };
    l4:
      with (
        a \in TheSet, 
        b \in TheSet
      ) {
        await ((a) = (2)) /\ ((b) = (2));
        goto Done;
      };
  }
  
  process (Coincidence = 2)
  {
    lbl:
      with (
        a1 \in TheSet, 
        b1 \in TheSet
      ) {
        await ((a1) = (1)) /\ ((b1) = (1));
        with (
          a \in TheSet, 
          b \in TheSet
        ) {
          await ((a) = (2)) /\ ((b) = (2));
          goto Done;
        };
      };
  }
  
  process (Complex = 3)
    variables i = 0; mark = {};
  {
    loop:
      if ((i) < (20)) {
        goto lbl1;
      } else {
        assert \A a \in TheSet : (a) \in (mark);
        goto Done;
      };
    lbl1:
      with (a \in TheSet) {
        mark := (mark) \union ({a});
        goto lbl2;
      };
    lbl2:
      i := (i) + (1);
      goto loop;
  }
}

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION
====
