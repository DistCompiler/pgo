------------------------------- MODULE kvs -------------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumWriteNodes
CONSTANT NumReadNodes

(********************

--mpcal kvs {
    define {
        Key1 == "key1"
        Key2 == "key2"
        KeySet == {Key1, Key2}

        Value1 == "value1"
        Value2 == "value2"
        ValueSet == {Value1, Value2}

        WriteNodeSet == 1..NumWriteNodes
        ReadNodeSet  == (NumWriteNodes+1)..(NumWriteNodes+NumReadNodes)
    }

    archetype AWriteNode(ref kvs[_]) {
    writeNodeLoop:
        while (TRUE) {
            with (key \in KeySet, val \in ValueSet) {
                kvs[key] := val;
            };
        };
    }

    archetype AReadNode(ref kvs[_]) {
    readNodeLoop:
        while (TRUE) {
            with (key \in KeySet) {
                print <<key, kvs[key]>>;
            };
        };
    }

    variable kvs = [key \in KeySet |-> ""];

    fair process (wnode \in WriteNodeSet) == instance AWriteNode(ref kvs[_]);
    fair process (rnode \in ReadNodeSet) == instance AReadNode(ref kvs[_]);
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm kvs {
  variables kvs = [key \in KeySet |-> ""];
  define{
    Key1 == "key1"
    Key2 == "key2"
    KeySet == {Key1, Key2}
    Value1 == "value1"
    Value2 == "value2"
    ValueSet == {Value1, Value2}
    WriteNodeSet == (1) .. (NumWriteNodes)
    ReadNodeSet == ((NumWriteNodes) + (1)) .. ((NumWriteNodes) + (NumReadNodes))
  }
  
  fair process (wnode \in WriteNodeSet)
  {
    writeNodeLoop:
      if(TRUE) {
        with (key \in KeySet, val \in ValueSet) {
          kvs := [kvs EXCEPT ![key] = val];
          goto writeNodeLoop;
        };
      } else {
        goto Done;
      };
  }
  
  fair process (rnode \in ReadNodeSet)
  {
    readNodeLoop:
      if(TRUE) {
        with (key \in KeySet) {
          print <<key, (kvs)[key]>>;
          goto readNodeLoop;
        };
      } else {
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "340f058a" /\ chksum(tla) = "54141042")
VARIABLES kvs, pc

(* define statement *)
Key1 == "key1"
Key2 == "key2"
KeySet == {Key1, Key2}
Value1 == "value1"
Value2 == "value2"
ValueSet == {Value1, Value2}
WriteNodeSet == (1) .. (NumWriteNodes)
ReadNodeSet == ((NumWriteNodes) + (1)) .. ((NumWriteNodes) + (NumReadNodes))


vars == << kvs, pc >>

ProcSet == (WriteNodeSet) \cup (ReadNodeSet)

Init == (* Global variables *)
        /\ kvs = [key \in KeySet |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in WriteNodeSet -> "writeNodeLoop"
                                        [] self \in ReadNodeSet -> "readNodeLoop"]

writeNodeLoop(self) == /\ pc[self] = "writeNodeLoop"
                       /\ IF TRUE
                             THEN /\ \E key \in KeySet:
                                       \E val \in ValueSet:
                                         /\ kvs' = [kvs EXCEPT ![key] = val]
                                         /\ pc' = [pc EXCEPT ![self] = "writeNodeLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ kvs' = kvs

wnode(self) == writeNodeLoop(self)

readNodeLoop(self) == /\ pc[self] = "readNodeLoop"
                      /\ IF TRUE
                            THEN /\ \E key \in KeySet:
                                      /\ PrintT(<<key, (kvs)[key]>>)
                                      /\ pc' = [pc EXCEPT ![self] = "readNodeLoop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ kvs' = kvs

rnode(self) == readNodeLoop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in WriteNodeSet: wnode(self))
           \/ (\E self \in ReadNodeSet: rnode(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WriteNodeSet : WF_vars(wnode(self))
        /\ \A self \in ReadNodeSet : WF_vars(rnode(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
