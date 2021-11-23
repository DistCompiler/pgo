-------------------------------- MODULE aworset --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_NODES

(********************


--mpcal crdt {
    define {
        NODE_SET == 1..NUM_NODES

        NULL == [n \in NODE_SET |-> 0]

        ELEM1 == "1"
        ELEM2 == "2"
        ELEM3 == "3"

        ELEM_SET == {ELEM1}

        AddCmd == 1
        RemoveCmd == 2

        Max(a, b) == IF a > b THEN a ELSE b
        MergeVectorClock(v1, v2) == [i \in DOMAIN v1 |-> Max(v1[i], v2[i])]

        \* returns TRUE if v1 < v2 otherwise FALSE
        CompareVectorClock(v1, v2) == IF \A i \in DOMAIN v1: v1[i] <= v2[i] THEN TRUE ELSE FALSE

        MergeKeys(a, b) == [k \in DOMAIN a |-> MergeVectorClock(a[k], b[k])]
    }

    macro Add(crdt, self, elem) {
        crdt[self] := [cmd |-> AddCmd, elem |-> elem];
    }

    macro Remove(crdt, self, elem) {
        crdt[self] := [cmd |-> RemoveCmd, elem |-> elem];
    }

    macro Merge(crdt, i1, i2) {
        assert crdt[i1] # crdt[i2];
        with (addk = MergeKeys(crdt[i1].addMap, crdt[i2].addMap), remk = MergeKeys(crdt[i1].remMap, crdt[i2].remMap)) {
            with (add = [i \in DOMAIN addk |-> IF CompareVectorClock(addk[i], remk[i]) THEN NULL ELSE addk[i]]) {
                crdt[i1].addMap := add;
                crdt[i2].addMap := add;
            };
            with (rem = [i \in DOMAIN remk |-> IF CompareVectorClock(addk[i], remk[i]) THEN remk[i] ELSE NULL]) {
                crdt[i1].remMap := rem;
                crdt[i2].remMap := rem;
            };
        };
        assert crdt[i1] = crdt[i2];
    }

    mapping macro AWORSet {
        read {
            yield {elem \in DOMAIN $variable.addMap: ~CompareVectorClock($variable.addMap[elem], $variable.remMap[elem])}
        }

        write {
            if ($value.cmd = AddCmd) {
                if ($variable.addMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem][self] := $variable.addMap[$value.elem][self] + 1;
                    $variable.remMap[$value.elem] := NULL;
                } else if ($variable.remMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem][self] := 1;
                    $variable.remMap[$value.elem] := NULL;
                } else {
                    $variable.addMap[$value.elem][self] := 1;
                };
            } else if ($value.cmd = RemoveCmd) {
                if ($variable.remMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem] := NULL;
                    $variable.remMap[$value.elem][self] := $variable.remMap[$value.elem][self] + 1;
                } else if ($variable.addMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem] := NULL;
                    $variable.remMap[$value.elem][self] := 1;
                } else {
                    $variable.remMap[$value.elem][self] := 1;
                };
            };
        }
    }

    archetype ANode(ref crdt[_]) {
    addItem:
        Add(crdt, self, ELEM1);
    removeItem:
        Remove(crdt, self, ELEM1);
    }

    variable
        crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]];

    fair process (Node \in NODE_SET) == instance ANode(ref crdt[_])
        mapping crdt[_] via AWORSet;

    fair process (UpdateCRDT = 0)
    {
    l1:
        while (TRUE) {
            with (i1 \in NODE_SET; i2 \in {x \in NODE_SET: crdt[x] # crdt[i1]}) {
                Merge(crdt, i1, i2);
            };
        };
    }
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm crdt {
  variables crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]];
  define{
    NODE_SET == (1) .. (NUM_NODES)
    NULL == [n \in NODE_SET |-> 0]
    ELEM1 == "1"
    ELEM2 == "2"
    ELEM3 == "3"
    ELEM_SET == {ELEM1}
    AddCmd == 1
    RemoveCmd == 2
    Max(a, b) == IF (a) > (b) THEN a ELSE b
    MergeVectorClock(v1, v2) == [i \in DOMAIN (v1) |-> Max((v1)[i], (v2)[i])]
    CompareVectorClock(v1, v2) == IF \A i \in DOMAIN (v1) : ((v1)[i]) <= ((v2)[i]) THEN TRUE ELSE FALSE
    MergeKeys(a, b) == [k \in DOMAIN (a) |-> MergeVectorClock((a)[k], (b)[k])]
  }
  
  fair process (UpdateCRDT = 0)
  {
    l1:
      if(TRUE) {
        with (i1 \in NODE_SET, i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}) {
          assert ((crdt)[i1]) # ((crdt)[i2]);
          with (addk0 = MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap), remk0 = MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap)) {
            with (add0 = [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]]) {
              with (crdt0 = [crdt EXCEPT ![i1]["addMap"] = add0]) {
                with (crdt1 = [crdt0 EXCEPT ![i2]["addMap"] = add0]) {
                  with (rem0 = [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL]) {
                    with (crdt2 = [crdt1 EXCEPT ![i1]["remMap"] = rem0]) {
                      crdt := [crdt1 EXCEPT ![i2]["remMap"] = rem0];
                      assert ((crdt)[i1]) = ((crdt)[i2]);
                      goto l1;
                    };
                  };
                };
              };
            };
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (Node \in NODE_SET)
  {
    addItem:
      with (value1 = [cmd |-> AddCmd, elem |-> ELEM1]) {
        if(((value1).cmd) = (AddCmd)) {
          if(((((crdt)[self]).addMap)[(value1).elem]) # (NULL)) {
            with (crdt3 = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)]) {
              crdt := [crdt3 EXCEPT ![self]["remMap"][(value1).elem] = NULL];
              goto removeItem;
            };
          } else {
            if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
              with (crdt4 = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1]) {
                crdt := [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL];
                goto removeItem;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1];
              goto removeItem;
            };
          };
        } else {
          if(((value1).cmd) = (RemoveCmd)) {
            if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
              with (crdt5 = [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL]) {
                crdt := [crdt5 EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt5)[self]).remMap)[(value1).elem])[self]) + (1)];
                goto removeItem;
              };
            } else {
              if(((((crdt)[self]).addMap)[(value1).elem]) # (NULL)) {
                with (crdt6 = [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL]) {
                  crdt := [crdt6 EXCEPT ![self]["remMap"][(value1).elem][self] = 1];
                  goto removeItem;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1];
                goto removeItem;
              };
            };
          } else {
            goto removeItem;
          };
        };
      };
    removeItem:
      with (value00 = [cmd |-> RemoveCmd, elem |-> ELEM1]) {
        if(((value00).cmd) = (AddCmd)) {
          if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
            with (crdt7 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
              crdt := [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
              goto Done;
            };
          } else {
            if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt8 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]) {
                crdt := [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
                goto Done;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1];
              goto Done;
            };
          };
        } else {
          if(((value00).cmd) = (RemoveCmd)) {
            if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt9 = [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL]) {
                crdt := [crdt9 EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt9)[self]).remMap)[(value00).elem])[self]) + (1)];
                goto Done;
              };
            } else {
              if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
                with (crdt10 = [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL]) {
                  crdt := [crdt10 EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                  goto Done;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                goto Done;
              };
            };
          } else {
            goto Done;
          };
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "c496c8ad" /\ chksum(tla) = "e898edae")
VARIABLES crdt, pc

(* define statement *)
NODE_SET == (1) .. (NUM_NODES)
NULL == [n \in NODE_SET |-> 0]
ELEM1 == "1"
ELEM2 == "2"
ELEM3 == "3"
ELEM_SET == {ELEM1}
AddCmd == 1
RemoveCmd == 2
Max(a, b) == IF (a) > (b) THEN a ELSE b
MergeVectorClock(v1, v2) == [i \in DOMAIN (v1) |-> Max((v1)[i], (v2)[i])]
CompareVectorClock(v1, v2) == IF \A i \in DOMAIN (v1) : ((v1)[i]) <= ((v2)[i]) THEN TRUE ELSE FALSE
MergeKeys(a, b) == [k \in DOMAIN (a) |-> MergeVectorClock((a)[k], (b)[k])]


vars == << crdt, pc >>

ProcSet == {0} \cup (NODE_SET)

Init == (* Global variables *)
        /\ crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in NODE_SET -> "addItem"]

l1 == /\ pc[0] = "l1"
      /\ IF TRUE
            THEN /\ \E i1 \in NODE_SET:
                      \E i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}:
                        /\ Assert(((crdt)[i1]) # ((crdt)[i2]),
                                  "Failure of assertion at line 134, column 11.")
                        /\ LET addk0 == MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap) IN
                             LET remk0 == MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap) IN
                               LET add0 == [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]] IN
                                 LET crdt0 == [crdt EXCEPT ![i1]["addMap"] = add0] IN
                                   LET crdt1 == [crdt0 EXCEPT ![i2]["addMap"] = add0] IN
                                     LET rem0 == [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL] IN
                                       LET crdt2 == [crdt1 EXCEPT ![i1]["remMap"] = rem0] IN
                                         /\ crdt' = [crdt1 EXCEPT ![i2]["remMap"] = rem0]
                                         /\ Assert(((crdt')[i1]) = ((crdt')[i2]),
                                                   "Failure of assertion at line 142, column 23.")
                                         /\ pc' = [pc EXCEPT ![0] = "l1"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ crdt' = crdt

UpdateCRDT == l1

addItem(self) == /\ pc[self] = "addItem"
                 /\ LET value1 == [cmd |-> AddCmd, elem |-> ELEM1] IN
                      IF ((value1).cmd) = (AddCmd)
                         THEN /\ IF ((((crdt)[self]).addMap)[(value1).elem]) # (NULL)
                                    THEN /\ LET crdt3 == [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)] IN
                                              /\ crdt' = [crdt3 EXCEPT ![self]["remMap"][(value1).elem] = NULL]
                                              /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                    ELSE /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                               THEN /\ LET crdt4 == [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1] IN
                                                         /\ crdt' = [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL]
                                                         /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                               ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1]
                                                    /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                         ELSE /\ IF ((value1).cmd) = (RemoveCmd)
                                    THEN /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                               THEN /\ LET crdt5 == [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL] IN
                                                         /\ crdt' = [crdt5 EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt5)[self]).remMap)[(value1).elem])[self]) + (1)]
                                                         /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                               ELSE /\ IF ((((crdt)[self]).addMap)[(value1).elem]) # (NULL)
                                                          THEN /\ LET crdt6 == [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL] IN
                                                                    /\ crdt' = [crdt6 EXCEPT ![self]["remMap"][(value1).elem][self] = 1]
                                                                    /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                                          ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                                         /\ crdt' = crdt

removeItem(self) == /\ pc[self] = "removeItem"
                    /\ LET value00 == [cmd |-> RemoveCmd, elem |-> ELEM1] IN
                         IF ((value00).cmd) = (AddCmd)
                            THEN /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                       THEN /\ LET crdt7 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                 /\ crdt' = [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                                       ELSE /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                  THEN /\ LET crdt8 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1] IN
                                                            /\ crdt' = [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]
                                                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                            ELSE /\ IF ((value00).cmd) = (RemoveCmd)
                                       THEN /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                  THEN /\ LET crdt9 == [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL] IN
                                                            /\ crdt' = [crdt9 EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt9)[self]).remMap)[(value00).elem])[self]) + (1)]
                                                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  ELSE /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                                             THEN /\ LET crdt10 == [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL] IN
                                                                       /\ crdt' = [crdt10 EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                             ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                            /\ crdt' = crdt

Node(self) == addItem(self) \/ removeItem(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == UpdateCRDT
           \/ (\E self \in NODE_SET: Node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(UpdateCRDT)
        /\ \A self \in NODE_SET : WF_vars(Node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EventualConvergence == []<>(\A n1, n2 \in NODE_SET: crdt[n1] = crdt[n2])

NodeTermination == <>(\A n \in NODE_SET: pc[n] = "Done")

=============================================================================
