-------------------------------- MODULE shopcart --------------------------------

\* do not check for deadlocks.

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_NODES

(********************

--mpcal shopcart {
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

    mapping macro InputQueue {
        read {
            await Len($variable) > 0;
            with (r = Head($variable)) {
                $variable := Tail($variable);
                yield r;
            };
        }

        write {
            yield Append($variable, $value);
        }
    }

    archetype ANode(ref crdt[_], ref in) {
    nodeLoop:
        while (TRUE) {
            with (req = in) {
                if (req.cmd = AddCmd) {
                    Add(crdt, self, req.elem);
                } else if (req.cmd = RemoveCmd) {
                    Remove(crdt, self, req.elem);
                };
            };
        };
    }

    variable
        crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]];
        in = <<
            [cmd |-> AddCmd, elem |-> ELEM1],
            [cmd |-> RemoveCmd, elem |-> ELEM2],
            [cmd |-> AddCmd, elem |-> ELEM2],
            [cmd |-> RemoveCmd, elem |-> ELEM1]
        >>;
    
    fair process (Node \in NODE_SET) == instance ANode(ref crdt[_], ref in)
        mapping crdt[_] via AWORSet
        mapping in via InputQueue;

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
--algorithm shopcart {
  variables crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]]; in = <<[cmd |-> AddCmd, elem |-> ELEM1], [cmd |-> RemoveCmd, elem |-> ELEM2], [cmd |-> AddCmd, elem |-> ELEM2], [cmd |-> RemoveCmd, elem |-> ELEM1]>>;
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
      if(TRUE) {
        with (i1 \in NODE_SET, i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}) {
          assert ((crdt)[i1]) # ((crdt)[i2]);
          with (addk0 = MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap), remk0 = MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap)) {
            with (add0 = [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]]) {
              with (crdt0 = [crdt EXCEPT ![i1]["addMap"] = add0]) {
                with (crdt1 = [crdt0 EXCEPT ![i2]["addMap"] = add0]) {
                  assert (((crdt1)[i1]).addMap) = (((crdt1)[i2]).addMap);
                  with (rem0 = [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL]) {
                    with (crdt2 = [crdt1 EXCEPT ![i1]["remMap"] = rem0]) {
                      crdt := [crdt2 EXCEPT ![i2]["remMap"] = rem0];
                      assert (((crdt)[i1]).remMap) = (((crdt)[i2]).remMap);
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
    nodeLoop:
      if(TRUE) {
        await (Len(in)) > (0);
        with (r0 = Head(in)) {
          in := Tail(in);
          with (yielded_in = r0) {
            with (req = yielded_in) {
              if(((req).cmd) = (AddCmd)) {
                with (value1 = [cmd |-> AddCmd, elem |-> (req).elem]) {
                  if(((value1).cmd) = (AddCmd)) {
                    if(((((crdt)[self]).addMap)[(value1).elem]) # (NULL)) {
                      with (crdt3 = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)]) {
                        crdt := [crdt3 EXCEPT ![self]["remMap"][(value1).elem] = NULL];
                        goto nodeLoop;
                      };
                    } else {
                      if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
                        with (crdt4 = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).remMap)[(value1).elem])[self]) + (1)]) {
                          crdt := [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL];
                          goto nodeLoop;
                        };
                      } else {
                        crdt := [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1];
                        goto nodeLoop;
                      };
                    };
                  } else {
                    if(((value1).cmd) = (RemoveCmd)) {
                      if(((((crdt)[self]).remMap)[(value1).elem]) # (NULL)) {
                        with (crdt5 = [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt)[self]).remMap)[(value1).elem])[self]) + (1)]) {
                          crdt := [crdt5 EXCEPT ![self]["addMap"][(value1).elem] = NULL];
                          goto nodeLoop;
                        };
                      } else {
                        if(((((crdt)[self]).addMap)[(value1).elem]) # (NULL)) {
                          with (crdt6 = [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)]) {
                            crdt := [crdt6 EXCEPT ![self]["addMap"][(value1).elem] = NULL];
                            goto nodeLoop;
                          };
                        } else {
                          crdt := [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1];
                          goto nodeLoop;
                        };
                      };
                    } else {
                      goto nodeLoop;
                    };
                  };
                };
              } else {
                if(((req).cmd) = (RemoveCmd)) {
                  with (value00 = [cmd |-> RemoveCmd, elem |-> (req).elem]) {
                    if(((value00).cmd) = (AddCmd)) {
                      if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
                        with (crdt7 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
                          crdt := [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
                          goto nodeLoop;
                        };
                      } else {
                        if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
                          with (crdt8 = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)]) {
                            crdt := [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL];
                            goto nodeLoop;
                          };
                        } else {
                          crdt := [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1];
                          goto nodeLoop;
                        };
                      };
                    } else {
                      if(((value00).cmd) = (RemoveCmd)) {
                        if(((((crdt)[self]).remMap)[(value00).elem]) # (NULL)) {
                          with (crdt9 = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)]) {
                            crdt := [crdt9 EXCEPT ![self]["addMap"][(value00).elem] = NULL];
                            goto nodeLoop;
                          };
                        } else {
                          if(((((crdt)[self]).addMap)[(value00).elem]) # (NULL)) {
                            with (crdt10 = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)]) {
                              crdt := [crdt10 EXCEPT ![self]["addMap"][(value00).elem] = NULL];
                              goto nodeLoop;
                            };
                          } else {
                            crdt := [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1];
                            goto nodeLoop;
                          };
                        };
                      } else {
                        goto nodeLoop;
                      };
                    };
                  };
                } else {
                  goto nodeLoop;
                };
              };
            };
          };
        };
      } else {
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "b82e2eee" /\ chksum(tla) = "4cada235")
VARIABLES crdt, in, pc

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


vars == << crdt, in, pc >>

ProcSet == {0} \cup (NODE_SET)

Init == (* Global variables *)
        /\ crdt = [nid \in NODE_SET |-> [addMap |-> [eid \in ELEM_SET |-> NULL], remMap |-> [eid \in ELEM_SET |-> NULL]]]
        /\ in = <<[cmd |-> AddCmd, elem |-> ELEM1], [cmd |-> RemoveCmd, elem |-> ELEM2], [cmd |-> AddCmd, elem |-> ELEM2], [cmd |-> RemoveCmd, elem |-> ELEM1]>>
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in NODE_SET -> "nodeLoop"]

l1 == /\ pc[0] = "l1"
      /\ IF TRUE
            THEN /\ \E i1 \in NODE_SET:
                      \E i2 \in {x \in NODE_SET : ((crdt)[x]) # ((crdt)[i1])}:
                        /\ Assert(((crdt)[i1]) # ((crdt)[i2]), 
                                  "Failure of assertion at line 165, column 11.")
                        /\ LET addk0 == MergeKeys(((crdt)[i1]).addMap, ((crdt)[i2]).addMap) IN
                             LET remk0 == MergeKeys(((crdt)[i1]).remMap, ((crdt)[i2]).remMap) IN
                               LET add0 == [i \in DOMAIN (addk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN NULL ELSE (addk0)[i]] IN
                                 LET crdt0 == [crdt EXCEPT ![i1]["addMap"] = add0] IN
                                   LET crdt1 == [crdt0 EXCEPT ![i2]["addMap"] = add0] IN
                                     /\ Assert((((crdt1)[i1]).addMap) = (((crdt1)[i2]).addMap), 
                                               "Failure of assertion at line 170, column 19.")
                                     /\ LET rem0 == [i \in DOMAIN (remk0) |-> IF CompareVectorClock((addk0)[i], (remk0)[i]) THEN (remk0)[i] ELSE NULL] IN
                                          LET crdt2 == [crdt1 EXCEPT ![i1]["remMap"] = rem0] IN
                                            /\ crdt' = [crdt2 EXCEPT ![i2]["remMap"] = rem0]
                                            /\ Assert((((crdt')[i1]).remMap) = (((crdt')[i2]).remMap), 
                                                      "Failure of assertion at line 174, column 23.")
                                            /\ Assert(((crdt')[i1]) = ((crdt')[i2]), 
                                                      "Failure of assertion at line 175, column 23.")
                                            /\ pc' = [pc EXCEPT ![0] = "l1"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ crdt' = crdt
      /\ in' = in

UpdateCRDT == l1

nodeLoop(self) == /\ pc[self] = "nodeLoop"
                  /\ IF TRUE
                        THEN /\ (Len(in)) > (0)
                             /\ LET r0 == Head(in) IN
                                  /\ in' = Tail(in)
                                  /\ LET yielded_in == r0 IN
                                       LET req == yielded_in IN
                                         IF ((req).cmd) = (AddCmd)
                                            THEN /\ LET value1 == [cmd |-> AddCmd, elem |-> (req).elem] IN
                                                      IF ((value1).cmd) = (AddCmd)
                                                         THEN /\ IF ((((crdt)[self]).addMap)[(value1).elem]) # (NULL)
                                                                    THEN /\ LET crdt3 == [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)] IN
                                                                              /\ crdt' = [crdt3 EXCEPT ![self]["remMap"][(value1).elem] = NULL]
                                                                              /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                    ELSE /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                                                               THEN /\ LET crdt4 == [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = (((((crdt)[self]).remMap)[(value1).elem])[self]) + (1)] IN
                                                                                         /\ crdt' = [crdt4 EXCEPT ![self]["remMap"][(value1).elem] = NULL]
                                                                                         /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                               ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value1).elem][self] = 1]
                                                                                    /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                         ELSE /\ IF ((value1).cmd) = (RemoveCmd)
                                                                    THEN /\ IF ((((crdt)[self]).remMap)[(value1).elem]) # (NULL)
                                                                               THEN /\ LET crdt5 == [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt)[self]).remMap)[(value1).elem])[self]) + (1)] IN
                                                                                         /\ crdt' = [crdt5 EXCEPT ![self]["addMap"][(value1).elem] = NULL]
                                                                                         /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                               ELSE /\ IF ((((crdt)[self]).addMap)[(value1).elem]) # (NULL)
                                                                                          THEN /\ LET crdt6 == [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = (((((crdt)[self]).addMap)[(value1).elem])[self]) + (1)] IN
                                                                                                    /\ crdt' = [crdt6 EXCEPT ![self]["addMap"][(value1).elem] = NULL]
                                                                                                    /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                                          ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value1).elem][self] = 1]
                                                                                               /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                         /\ crdt' = crdt
                                            ELSE /\ IF ((req).cmd) = (RemoveCmd)
                                                       THEN /\ LET value00 == [cmd |-> RemoveCmd, elem |-> (req).elem] IN
                                                                 IF ((value00).cmd) = (AddCmd)
                                                                    THEN /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                                                               THEN /\ LET crdt7 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                                                         /\ crdt' = [crdt7 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                                                         /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                               ELSE /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                                                          THEN /\ LET crdt8 == [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)] IN
                                                                                                    /\ crdt' = [crdt8 EXCEPT ![self]["remMap"][(value00).elem] = NULL]
                                                                                                    /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                                          ELSE /\ crdt' = [crdt EXCEPT ![self]["addMap"][(value00).elem][self] = 1]
                                                                                               /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                    ELSE /\ IF ((value00).cmd) = (RemoveCmd)
                                                                               THEN /\ IF ((((crdt)[self]).remMap)[(value00).elem]) # (NULL)
                                                                                          THEN /\ LET crdt9 == [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).remMap)[(value00).elem])[self]) + (1)] IN
                                                                                                    /\ crdt' = [crdt9 EXCEPT ![self]["addMap"][(value00).elem] = NULL]
                                                                                                    /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                                          ELSE /\ IF ((((crdt)[self]).addMap)[(value00).elem]) # (NULL)
                                                                                                     THEN /\ LET crdt10 == [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = (((((crdt)[self]).addMap)[(value00).elem])[self]) + (1)] IN
                                                                                                               /\ crdt' = [crdt10 EXCEPT ![self]["addMap"][(value00).elem] = NULL]
                                                                                                               /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                                                     ELSE /\ crdt' = [crdt EXCEPT ![self]["remMap"][(value00).elem][self] = 1]
                                                                                                          /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                                                    /\ crdt' = crdt
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "nodeLoop"]
                                                            /\ crdt' = crdt
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << crdt, in >>

Node(self) == nodeLoop(self)

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

\* this property should be violated
ValueOK == <>(\A n \in NODE_SET: QUERY(crdt[n]) = {ELEM2})

\* NodeTermination == <>(\A n \in NODE_SET: pc[n] = "Done")

=============================================================================
