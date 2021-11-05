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

        ELEM_SET == {ELEM1, ELEM2, ELEM3}

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
        with (addk = MergeKeys(crdt[i1].addMap, crdt[i2].addMap), remk = MergeKeys(crdt[i1].remMap, crdt[i2].remMap)) {
            with (add = [i \in DOMAIN addk |-> IF CompareVectorClock(addk[i], remk[i]) THEN NULL ELSE addk[i]]) {
                crdt[i1].addMap := add;
                crdt[i2].addMap := add;
            };
            with (rem = [i \in DOMAIN remk |-> IF CompareVectorClock(addk[i], remk[i]) THEN remk[i] ELSE NULL]) {
                crdt[i1].remMap := rem;
                crdt[i2].remMap := rem;
            }
        }
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
    ELEM_SET == {ELEM1, ELEM2, ELEM3}
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
          with (addk = MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap), remk = MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap)) {
            with (add0 = [i \in DOMAIN (addk) |-> IF CompareVectorClock((addk)[i], (remk)[i]) THEN NULL ELSE (addk)[i]]) {
              with (crdt0 = [crdt EXCEPT ![i1]["addMap"] = add0]) {
                with (crdt1 = [crdt0 EXCEPT ![i2]["addMap"] = add0]) {
                  with (rem = [i \in DOMAIN (remk) |-> IF CompareVectorClock((addk)[i], (remk)[i]) THEN (remk)[i] ELSE NULL]) {
                    with (crdt2 = [crdt1 EXCEPT ![i1]["remMap"] = rem]) {
                      crdt := [crdt1 EXCEPT ![i2]["remMap"] = rem];
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
              goto getItem;
            };
          } else {
            if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
              with (crdt4 = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1]) {
                crdt := [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL];
                goto getItem;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1];
              goto getItem;
            };
          };
        } else {
          if(((value1).cmd) = (RemoveCmd)) {
            if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
              with (crdt5 = [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL]) {
                crdt := [crdt5 EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt5)[self]).remMap)[(value1).elem])[self]) + (1)];
                goto getItem;
              };
            } else {
              if(((((crdt)[self]).addMap)[(value1).elem]) # (NULL)) {
                with (crdt6 = [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL]) {
                  crdt := [crdt6 EXCEPT ![self]["remMap"][(value1).elem][self] = 1];
                  goto getItem;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1];
                goto getItem;
              };
            };
          } else {
            goto getItem;
          };
        };
      };
    getItem:
      with (yielded_crdt1 = {elem \in DOMAIN (((crdt)[self]).addMap) : ~ (CompareVectorClock((((crdt)[self]).addMap)[elem], (((crdt)[self]).remMap)[elem]))}) {
        await (ELEM1) \in (yielded_crdt1);
        goto removeItem;
      };
    removeItem:
      with (value00 = [cmd |-> RemoveCmd, elem |-> ELEM1]) {
        if(((value00).cmd) = (AddCmd)) {
          if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
            with (crdt7 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
              crdt := [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
              goto reGetItem;
            };
          } else {
            if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt8 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]) {
                crdt := [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
                goto reGetItem;
              };
            } else {
              crdt := [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1];
              goto reGetItem;
            };
          };
        } else {
          if(((value00).cmd) = (RemoveCmd)) {
            if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
              with (crdt9 = [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL]) {
                crdt := [crdt9 EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt9)[self]).remMap)[(value00).elem])[self]) + (1)];
                goto reGetItem;
              };
            } else {
              if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
                with (crdt10 = [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL]) {
                  crdt := [crdt10 EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                  goto reGetItem;
                };
              } else {
                crdt := [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                goto reGetItem;
              };
            };
          } else {
            goto reGetItem;
          };
        };
      };
    reGetItem:
      with (yielded_crdt00 = {elem \in DOMAIN (((crdt)[self]).addMap) : ~ (CompareVectorClock((((crdt)[self]).addMap)[elem], (((crdt)[self]).remMap)[elem]))}) {
        await ~ ((ELEM1) \in (yielded_crdt00));
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "5ca26aac" /\ chksum(tla) = "674f9ba6")
VARIABLES crdt, pc

(* define statement *)
NODE_SET == (1) .. (NUM_NODES)
NULL == [n \in NODE_SET |-> 0]
ELEM1 == "1"
ELEM2 == "2"
ELEM3 == "3"
ELEM_SET == {ELEM1, ELEM2, ELEM3}
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
                        LET addk == MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap) IN
                          LET remk == MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap) IN
                            LET add0 == [i \in DOMAIN (addk) |-> IF CompareVectorClock((addk)[i], (remk)[i]) THEN NULL ELSE (addk)[i]] IN
                              LET crdt0 == [crdt EXCEPT ![i1]["addMap"] = add0] IN
                                LET crdt1 == [crdt0 EXCEPT ![i2]["addMap"] = add0] IN
                                  LET rem == [i \in DOMAIN (remk) |-> IF CompareVectorClock((addk)[i], (remk)[i]) THEN (remk)[i] ELSE NULL] IN
                                    LET crdt2 == [crdt1 EXCEPT ![i1]["remMap"] = rem] IN
                                      /\ crdt' = [crdt1 EXCEPT ![i2]["remMap"] = rem]
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
                                              /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                    ELSE /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                               THEN /\ LET crdt4 == [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1] IN
                                                         /\ crdt' = [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL]
                                                         /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                               ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1]
                                                    /\ pc' = [pc EXCEPT ![self] = "getItem"]
                         ELSE /\ IF ((value1).cmd) = (RemoveCmd)
                                    THEN /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                               THEN /\ LET crdt5 == [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL] IN
                                                         /\ crdt' = [crdt5 EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt5)[self]).remMap)[(value1).elem])[self]) + (1)]
                                                         /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                               ELSE /\ IF ((((crdt)[self]).addMap)[(value1).elem]) # (NULL)
                                                          THEN /\ LET crdt6 == [crdt EXCEPT ![self]["addMap"][(value1).elem] = NULL] IN
                                                                    /\ crdt' = [crdt6 EXCEPT ![self]["remMap"][(value1).elem][self] = 1]
                                                                    /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                                          ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "getItem"]
                                         /\ crdt' = crdt

getItem(self) == /\ pc[self] = "getItem"
                 /\ LET yielded_crdt1 == {elem \in DOMAIN (((crdt)[self]).addMap) : ~ (CompareVectorClock((((crdt)[self]).addMap)[elem], (((crdt)[self]).remMap)[elem]))} IN
                      /\ (ELEM1) \in (yielded_crdt1)
                      /\ pc' = [pc EXCEPT ![self] = "removeItem"]
                 /\ crdt' = crdt

removeItem(self) == /\ pc[self] = "removeItem"
                    /\ LET value00 == [cmd |-> RemoveCmd, elem |-> ELEM1] IN
                         IF ((value00).cmd) = (AddCmd)
                            THEN /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                       THEN /\ LET crdt7 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                 /\ crdt' = [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                 /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                       ELSE /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                  THEN /\ LET crdt8 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1] IN
                                                            /\ crdt' = [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                            /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                                  ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]
                                                       /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                            ELSE /\ IF ((value00).cmd) = (RemoveCmd)
                                       THEN /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                  THEN /\ LET crdt9 == [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL] IN
                                                            /\ crdt' = [crdt9 EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt9)[self]).remMap)[(value00).elem])[self]) + (1)]
                                                            /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                                  ELSE /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                                             THEN /\ LET crdt10 == [crdt EXCEPT ![self]["addMap"][(value00).elem] = NULL] IN
                                                                       /\ crdt' = [crdt10 EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                       /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                                             ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                  /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "reGetItem"]
                                            /\ crdt' = crdt

reGetItem(self) == /\ pc[self] = "reGetItem"
                   /\ LET yielded_crdt00 == {elem \in DOMAIN (((crdt)[self]).addMap) : ~ (CompareVectorClock((((crdt)[self]).addMap)[elem], (((crdt)[self]).remMap)[elem]))} IN
                        /\ ~ ((ELEM1) \in (yielded_crdt00))
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ crdt' = crdt

Node(self) == addItem(self) \/ getItem(self) \/ removeItem(self)
                 \/ reGetItem(self)

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
