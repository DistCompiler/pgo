-------------------------------- MODULE aworset --------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_NODES

(********************


--mpcal aworset {
    define {
        NODE_SET == 1..NUM_NODES

        NULL == [n \in NODE_SET |-> 0]

        ELEM1 == "1"
        ELEM2 == "2"
        ELEM3 == "3"

        ELEM_SET == {ELEM1, ELEM2}

        AddCmd == 1
        RemoveCmd == 2

        Max(a, b) == IF a > b THEN a ELSE b
        MergeVectorClock(v1, v2) == [i \in DOMAIN v1 |-> Max(v1[i], v2[i])]

        \* returns TRUE if v1 < v2 otherwise FALSE
        CompareVectorClock(v1, v2) == IF \A i \in DOMAIN v1: v1[i] <= v2[i] THEN TRUE ELSE FALSE

        MergeKeys(a, b) == [k \in DOMAIN a |-> MergeVectorClock(a[k], b[k])]

        QUERY(r) == {elem \in DOMAIN r.addMap: ~CompareVectorClock(r.addMap[elem], r.remMap[elem])} 
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
                assert crdt[i1].addMap = crdt[i2].addMap;
            };
            with (rem = [i \in DOMAIN remk |-> IF CompareVectorClock(addk[i], remk[i]) THEN remk[i] ELSE NULL]) {
                crdt[i1].remMap := rem;
                crdt[i2].remMap := rem;
                assert crdt[i1].remMap = crdt[i2].remMap;
            };
        };
        assert crdt[i1] = crdt[i2];
    }

    mapping macro AWORSet {
        read {
            yield QUERY($variable);
        }

        write {
            if ($value.cmd = AddCmd) { 
                if ($variable.addMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem][self] := $variable.addMap[$value.elem][self] + 1;
                    $variable.remMap[$value.elem] := NULL;
                } else if ($variable.remMap[$value.elem] # NULL) {
                    $variable.addMap[$value.elem][self] := $variable.remMap[$value.elem][self] + 1;
                    $variable.remMap[$value.elem] := NULL;
                } else {
                    $variable.addMap[$value.elem][self] := 1;
                };
            } else if ($value.cmd = RemoveCmd) {
                if ($variable.remMap[$value.elem] # NULL) {
                    $variable.remMap[$value.elem][self] := $variable.remMap[$value.elem][self] + 1;
                    $variable.addMap[$value.elem] := NULL;
                } else if ($variable.addMap[$value.elem] # NULL) {
                    $variable.remMap[$value.elem][self] := $variable.addMap[$value.elem][self] + 1;
                    $variable.addMap[$value.elem] := NULL;
                } else {
                    $variable.remMap[$value.elem][self] := 1;
                };
            };
        }
    }

    archetype ANode(ref crdt[_]) {
    addItem1:
        Add(crdt, self, ELEM1);
    removeItem1:
        Remove(crdt, self, ELEM1);
    addItem2:
        Add(crdt, self, ELEM2);
    removeItem2:
        Remove(crdt, self, ELEM2);
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
--algorithm aworset {
  variables crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]];
  define{
    NODE_SET == (1) .. (NUM_NODES)
    NULL == [n \in NODE_SET |-> 0]
    ELEM1 == "1"
    ELEM2 == "2"
    ELEM3 == "3"
    ELEM_SET == {ELEM1, ELEM2}
    AddCmd == 1
    RemoveCmd == 2
    Max(a, b) == IF (a) > (b) THEN a ELSE b
    MergeVectorClock(v1, v2) == [i \in DOMAIN (v1) |-> Max((v1)[i], (v2)[i])]
    CompareVectorClock(v1, v2) == IF \A i \in DOMAIN (v1) : ((v1)[i]) <= ((v2)[i]) THEN TRUE ELSE FALSE
    MergeKeys(a, b) == [k \in DOMAIN (a) |-> MergeVectorClock((a)[k], (b)[k])]
    QUERY(r) == {elem \in DOMAIN ((r).addMap) : ~ (CompareVectorClock(((r).addMap)[elem], ((r).remMap)[elem]))}
  }
  
  fair process (UpdateCRDT = 0)
  {
    l1:
      if (TRUE) {
        with (
          i1 \in NODE_SET, 
          i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}
        ) {
          assert ((crdt)[i1]) # ((crdt)[i2]);
          with (
            addk0 = MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap), 
            remk0 = MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap), 
            add0 = [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]], 
            crdt0 = [crdt EXCEPT ![i1]["addMap"] = add0], 
            crdt1 = [crdt0 EXCEPT ![i2]["addMap"] = add0]
          ) {
            assert (((crdt1)[i1]).addMap) = (((crdt1)[i2]).addMap);
            with (
              rem0 = [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL], 
              crdt2 = [crdt1 EXCEPT ![i1]["remMap"] = rem0]
            ) {
              crdt := [crdt2 EXCEPT ![i2]["remMap"] = rem0];
              assert (((crdt)[i1]).remMap) = (((crdt)[i2]).remMap);
              assert ((crdt)[i1]) = ((crdt)[i2]);
              goto l1;
            };
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (Node \in NODE_SET)
  {
    addItem1:
      with (value3 = [cmd |-> AddCmd, elem |-> ELEM1]) {
        if (((value3).cmd) = (AddCmd)) {
          if (((((crdt)[self]).addMap)[(value3).elem]) # (NULL)) {
            with (crdt3 = [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = (((((crdt)[self]).addMap)[(value3).elem])[self]) + (1)]) {
              crdt := [crdt3 EXCEPT ![self]["remMap"][(value3).elem] = NULL];
              goto removeItem1;
            };
          } else {
            if (((((crdt)[self]).remMap)[(value3).elem]) # (NULL)) {
              with (crdt4 = [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = (((((crdt)[self]).remMap)[(value3).elem])[self]) + (1)]) {
                crdt := [crdt4 EXCEPT ![self]["remMap"][(value3).elem] = NULL];
                goto removeItem1;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = 1];
              goto removeItem1;
            };
          };
        } else {
          if (((value3).cmd) = (RemoveCmd)) {
            if (((((crdt)[self]).remMap)[(value3).elem]) # (NULL)) {
              with (crdt5 = [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = (((((crdt)[self]).remMap)[(value3).elem])[self]) + (1)]) {
                crdt := [crdt5 EXCEPT ![self]["addMap"][(value3).elem] = NULL];
                goto removeItem1;
              };
            } else {
              if (((((crdt)[self]).addMap)[(value3).elem]) # (NULL)) {
                with (crdt6 = [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = (((((crdt)[self]).addMap)[(value3).elem])[self]) + (1)]) {
                  crdt := [crdt6 EXCEPT ![self]["addMap"][(value3).elem] = NULL];
                  goto removeItem1;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = 1];
                goto removeItem1;
              };
            };
          } else {
            goto removeItem1;
          };
        };
      };
    removeItem1:
      with (value00 = [cmd |-> RemoveCmd, elem |-> ELEM1]) {
        if (((value00).cmd) = (AddCmd)) {
          if (((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
            with (crdt7 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
              crdt := [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
              goto addItem2;
            };
          } else {
            if (((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt8 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)]) {
                crdt := [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
                goto addItem2;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1];
              goto addItem2;
            };
          };
        } else {
          if (((value00).cmd) = (RemoveCmd)) {
            if (((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt9 = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)]) {
                crdt := [crdt9 EXCEPT ![self]["addMap"][(value00).elem] = NULL];
                goto addItem2;
              };
            } else {
              if (((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
                with (crdt10 = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
                  crdt := [crdt10 EXCEPT ![self]["addMap"][(value00).elem] = NULL];
                  goto addItem2;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                goto addItem2;
              };
            };
          } else {
            goto addItem2;
          };
        };
      };
    addItem2:
      with (value10 = [cmd |-> AddCmd, elem |-> ELEM2]) {
        if (((value10).cmd) = (AddCmd)) {
          if (((((crdt)[self]).addMap)[(value10).elem]) # (NULL)) {
            with (crdt11 = [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = (((((crdt)[self]).addMap)[(value10).elem])[self]) + (1)]) {
              crdt := [crdt11 EXCEPT ![self]["remMap"][(value10).elem] = NULL];
              goto removeItem2;
            };
          } else {
            if (((((crdt)[self]).remMap)[(value10).elem]) # (NULL)) {
              with (crdt12 = [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = (((((crdt)[self]).remMap)[(value10).elem])[self]) + (1)]) {
                crdt := [crdt12 EXCEPT ![self]["remMap"][(value10).elem] = NULL];
                goto removeItem2;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = 1];
              goto removeItem2;
            };
          };
        } else {
          if (((value10).cmd) = (RemoveCmd)) {
            if (((((crdt)[self]).remMap)[(value10).elem]) # (NULL)) {
              with (crdt13 = [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = (((((crdt)[self]).remMap)[(value10).elem])[self]) + (1)]) {
                crdt := [crdt13 EXCEPT ![self]["addMap"][(value10).elem] = NULL];
                goto removeItem2;
              };
            } else {
              if (((((crdt)[self]).addMap)[(value10).elem]) # (NULL)) {
                with (crdt14 = [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = (((((crdt)[self]).addMap)[(value10).elem])[self]) + (1)]) {
                  crdt := [crdt14 EXCEPT ![self]["addMap"][(value10).elem] = NULL];
                  goto removeItem2;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = 1];
                goto removeItem2;
              };
            };
          } else {
            goto removeItem2;
          };
        };
      };
    removeItem2:
      with (value20 = [cmd |-> RemoveCmd, elem |-> ELEM2]) {
        if (((value20).cmd) = (AddCmd)) {
          if (((((crdt)[self]).addMap)[(value20).elem]) # (NULL)) {
            with (crdt15 = [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = (((((crdt)[self]).addMap)[(value20).elem])[self]) + (1)]) {
              crdt := [crdt15 EXCEPT ![self]["remMap"][(value20).elem] = NULL];
              goto Done;
            };
          } else {
            if (((((crdt)[self]).remMap)[(value20).elem]) # (NULL)) {
              with (crdt16 = [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = (((((crdt)[self]).remMap)[(value20).elem])[self]) + (1)]) {
                crdt := [crdt16 EXCEPT ![self]["remMap"][(value20).elem] = NULL];
                goto Done;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = 1];
              goto Done;
            };
          };
        } else {
          if (((value20).cmd) = (RemoveCmd)) {
            if (((((crdt)[self]).remMap)[(value20).elem]) # (NULL)) {
              with (crdt17 = [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = (((((crdt)[self]).remMap)[(value20).elem])[self]) + (1)]) {
                crdt := [crdt17 EXCEPT ![self]["addMap"][(value20).elem] = NULL];
                goto Done;
              };
            } else {
              if (((((crdt)[self]).addMap)[(value20).elem]) # (NULL)) {
                with (crdt18 = [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = (((((crdt)[self]).addMap)[(value20).elem])[self]) + (1)]) {
                  crdt := [crdt18 EXCEPT ![self]["addMap"][(value20).elem] = NULL];
                  goto Done;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = 1];
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
\* BEGIN TRANSLATION (chksum(pcal) = "96251621" /\ chksum(tla) = "53f9a0c1")
VARIABLES crdt, pc

(* define statement *)
NODE_SET == (1) .. (NUM_NODES)
NULL == [n \in NODE_SET |-> 0]
ELEM1 == "1"
ELEM2 == "2"
ELEM3 == "3"
ELEM_SET == {ELEM1, ELEM2}
AddCmd == 1
RemoveCmd == 2
Max(a, b) == IF (a) > (b) THEN a ELSE b
MergeVectorClock(v1, v2) == [i \in DOMAIN (v1) |-> Max((v1)[i], (v2)[i])]
CompareVectorClock(v1, v2) == IF \A i \in DOMAIN (v1) : ((v1)[i]) <= ((v2)[i]) THEN TRUE ELSE FALSE
MergeKeys(a, b) == [k \in DOMAIN (a) |-> MergeVectorClock((a)[k], (b)[k])]
QUERY(r) == {elem \in DOMAIN ((r).addMap) : ~ (CompareVectorClock(((r).addMap)[elem], ((r).remMap)[elem]))}


vars == << crdt, pc >>

ProcSet == {0} \cup (NODE_SET)

Init == (* Global variables *)
        /\ crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in NODE_SET -> "addItem1"]

l1 == /\ pc[0] = "l1"
      /\ IF TRUE
            THEN /\ \E i1 \in NODE_SET:
                      \E i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}:
                        /\ Assert(((crdt)[i1]) # ((crdt)[i2]), 
                                  "Failure of assertion at line 143, column 11.")
                        /\ LET addk0 == MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap) IN
                             LET remk0 == MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap) IN
                               LET add0 == [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]] IN
                                 LET crdt0 == [crdt EXCEPT ![i1]["addMap"] = add0] IN
                                   LET crdt1 == [crdt0 EXCEPT ![i2]["addMap"] = add0] IN
                                     /\ Assert((((crdt1)[i1]).addMap) = (((crdt1)[i2]).addMap), 
                                               "Failure of assertion at line 148, column 19.")
                                     /\ LET rem0 == [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL] IN
                                          LET crdt2 == [crdt1 EXCEPT ![i1]["remMap"] = rem0] IN
                                            /\ crdt' = [crdt2 EXCEPT ![i2]["remMap"] = rem0]
                                            /\ Assert((((crdt')[i1]).remMap) = (((crdt')[i2]).remMap), 
                                                      "Failure of assertion at line 152, column 23.")
                                            /\ Assert(((crdt')[i1]) = ((crdt')[i2]), 
                                                      "Failure of assertion at line 153, column 23.")
                                            /\ pc' = [pc EXCEPT ![0] = "l1"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ crdt' = crdt

UpdateCRDT == l1

addItem1(self) == /\ pc[self] = "addItem1"
                  /\ LET value3 == [cmd |-> AddCmd, elem |-> ELEM1] IN
                       IF ((value3).cmd) = (AddCmd)
                          THEN /\ IF ((((crdt)[self]).addMap)[(value3).elem]) # (NULL)
                                     THEN /\ LET crdt3 == [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = (((((crdt)[self]).addMap)[(value3).elem])[self]) + (1)] IN
                                               /\ crdt' = [crdt3 EXCEPT ![self]["remMap"][(value3).elem] = NULL]
                                               /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                     ELSE /\ IF ((((crdt)[self]).remMap)[(value3).elem]) # (NULL)
                                                THEN /\ LET crdt4 == [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = (((((crdt)[self]).remMap)[(value3).elem])[self]) + (1)] IN
                                                          /\ crdt' = [crdt4 EXCEPT ![self]["remMap"][(value3).elem] = NULL]
                                                          /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                                ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value3).elem][self] = 1]
                                                     /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                          ELSE /\ IF ((value3).cmd) = (RemoveCmd)
                                     THEN /\ IF ((((crdt)[self]).remMap)[(value3).elem]) # (NULL)
                                                THEN /\ LET crdt5 == [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = (((((crdt)[self]).remMap)[(value3).elem])[self]) + (1)] IN
                                                          /\ crdt' = [crdt5 EXCEPT ![self]["addMap"][(value3).elem] = NULL]
                                                          /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                                ELSE /\ IF ((((crdt)[self]).addMap)[(value3).elem]) # (NULL)
                                                           THEN /\ LET crdt6 == [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = (((((crdt)[self]).addMap)[(value3).elem])[self]) + (1)] IN
                                                                     /\ crdt' = [crdt6 EXCEPT ![self]["addMap"][(value3).elem] = NULL]
                                                                     /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                                           ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value3).elem][self] = 1]
                                                                /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "removeItem1"]
                                          /\ crdt' = crdt

removeItem1(self) == /\ pc[self] = "removeItem1"
                     /\ LET value00 == [cmd |-> RemoveCmd, elem |-> ELEM1] IN
                          IF ((value00).cmd) = (AddCmd)
                             THEN /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                        THEN /\ LET crdt7 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                  /\ crdt' = [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                  /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                        ELSE /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                   THEN /\ LET crdt8 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)] IN
                                                             /\ crdt' = [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                             /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                                   ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]
                                                        /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                             ELSE /\ IF ((value00).cmd) = (RemoveCmd)
                                        THEN /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                   THEN /\ LET crdt9 == [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)] IN
                                                             /\ crdt' = [crdt9 EXCEPT ![self]["addMap"][(value00).elem] = NULL]
                                                             /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                                   ELSE /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                                              THEN /\ LET crdt10 == [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                                        /\ crdt' = [crdt10 EXCEPT ![self]["addMap"][(value00).elem] = NULL]
                                                                        /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                                              ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                   /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "addItem2"]
                                             /\ crdt' = crdt

addItem2(self) == /\ pc[self] = "addItem2"
                  /\ LET value10 == [cmd |-> AddCmd, elem |-> ELEM2] IN
                       IF ((value10).cmd) = (AddCmd)
                          THEN /\ IF ((((crdt)[self]).addMap)[(value10).elem]) # (NULL)
                                     THEN /\ LET crdt11 == [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = (((((crdt)[self]).addMap)[(value10).elem])[self]) + (1)] IN
                                               /\ crdt' = [crdt11 EXCEPT ![self]["remMap"][(value10).elem] = NULL]
                                               /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                     ELSE /\ IF ((((crdt)[self]).remMap)[(value10).elem]) # (NULL)
                                                THEN /\ LET crdt12 == [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = (((((crdt)[self]).remMap)[(value10).elem])[self]) + (1)] IN
                                                          /\ crdt' = [crdt12 EXCEPT ![self]["remMap"][(value10).elem] = NULL]
                                                          /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                                ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value10).elem][self] = 1]
                                                     /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                          ELSE /\ IF ((value10).cmd) = (RemoveCmd)
                                     THEN /\ IF ((((crdt)[self]).remMap)[(value10).elem]) # (NULL)
                                                THEN /\ LET crdt13 == [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = (((((crdt)[self]).remMap)[(value10).elem])[self]) + (1)] IN
                                                          /\ crdt' = [crdt13 EXCEPT ![self]["addMap"][(value10).elem] = NULL]
                                                          /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                                ELSE /\ IF ((((crdt)[self]).addMap)[(value10).elem]) # (NULL)
                                                           THEN /\ LET crdt14 == [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = (((((crdt)[self]).addMap)[(value10).elem])[self]) + (1)] IN
                                                                     /\ crdt' = [crdt14 EXCEPT ![self]["addMap"][(value10).elem] = NULL]
                                                                     /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                                           ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value10).elem][self] = 1]
                                                                /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "removeItem2"]
                                          /\ crdt' = crdt

removeItem2(self) == /\ pc[self] = "removeItem2"
                     /\ LET value20 == [cmd |-> RemoveCmd, elem |-> ELEM2] IN
                          IF ((value20).cmd) = (AddCmd)
                             THEN /\ IF ((((crdt)[self]).addMap)[(value20).elem]) # (NULL)
                                        THEN /\ LET crdt15 == [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = (((((crdt)[self]).addMap)[(value20).elem])[self]) + (1)] IN
                                                  /\ crdt' = [crdt15 EXCEPT ![self]["remMap"][(value20).elem] = NULL]
                                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        ELSE /\ IF ((((crdt)[self]).remMap)[(value20).elem]) # (NULL)
                                                   THEN /\ LET crdt16 == [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = (((((crdt)[self]).remMap)[(value20).elem])[self]) + (1)] IN
                                                             /\ crdt' = [crdt16 EXCEPT ![self]["remMap"][(value20).elem] = NULL]
                                                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                   ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value20).elem][self] = 1]
                                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                             ELSE /\ IF ((value20).cmd) = (RemoveCmd)
                                        THEN /\ IF ((((crdt)[self]).remMap)[(value20).elem]) # (NULL)
                                                   THEN /\ LET crdt17 == [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = (((((crdt)[self]).remMap)[(value20).elem])[self]) + (1)] IN
                                                             /\ crdt' = [crdt17 EXCEPT ![self]["addMap"][(value20).elem] = NULL]
                                                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                   ELSE /\ IF ((((crdt)[self]).addMap)[(value20).elem]) # (NULL)
                                                              THEN /\ LET crdt18 == [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = (((((crdt)[self]).addMap)[(value20).elem])[self]) + (1)] IN
                                                                        /\ crdt' = [crdt18 EXCEPT ![self]["addMap"][(value20).elem] = NULL]
                                                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                              ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value20).elem][self] = 1]
                                                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                             /\ crdt' = crdt

Node(self) == addItem1(self) \/ removeItem1(self) \/ addItem2(self)
                 \/ removeItem2(self)

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

\* Invariants

QueryOK == \A n1, n2 \in NODE_SET: ((crdt[n1] = crdt[n2]) => (QUERY(crdt[n1]) = QUERY(crdt[n2])))

\* Properties

EventualStateConvergence == []<>(\A n1, n2 \in NODE_SET: crdt[n1] = crdt[n2])
EventualValueConvergence == []<>(\A n1, n2 \in NODE_SET: QUERY(crdt[n1]) = QUERY(crdt[n2]))

NodeTermination == <>(\A n \in NODE_SET: pc[n] = "Done")

=============================================================================
