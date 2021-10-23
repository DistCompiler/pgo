------------------------------- MODULE gcounter -------------------------------

(********************
Specification of a simple system that demonstrates using a state-based 
inrement-only CRDT. More details in the CRDT technical report:
	https://hal.inria.fr/inria-00555588/document

Model-check this spec without checking for deadlocks and with the properties
defined in the end.
********************)

EXTENDS Naturals, Sequences, TLC, FiniteSets

(********************

--mpcal gcounter {
    define {
		\* FIXME: Currently, recursive operators are not supported by PGo. 
		\* So we couldn't define SUM operator in the correct way and it's 
		\* just hardcoded for now.
		SUM(f) == f[1] + f[2] + f[3]
		NUM_NODES == 3

        NODE_SET == 1..NUM_NODES

		MAX(a, b) == IF a > b THEN a ELSE b
    }

	\* CRDT merge
    macro Merge(cntrs, i1, i2) {
		with (res = [j \in DOMAIN cntrs[i1] |-> MAX(cntrs[i1][j], cntrs[i2][j])]) {
			cntrs[i1] := res;
			cntrs[i2] := res;
		};
    }

    mapping macro LocalGCntr {
        read {
			\* CRDT query
            yield SUM($variable);
        }

        write {
            assert $value > 0;
			\* CRDT update
            yield [$variable EXCEPT ![self] = $variable[self] + $value];
        }
    } 
 
    archetype ANode(ref cntr[_]) {
    update:
        cntr[self] := 1;
    wait:
        await cntr[self] = NUM_NODES;
    }

    variables
        localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]];

    fair process (Node \in NODE_SET) == instance ANode(ref localcntrs[_])
        mapping localcntrs[_] via LocalGCntr;

    fair process (UpdateGCntr = 0) {
    l1:
        while (TRUE) {
            with (i1 \in NODE_SET; i2 \in {x \in NODE_SET: localcntrs[x] # localcntrs[i1]}) {
                Merge(localcntrs, i1, i2);
            };
        };
    }
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm gcounter {
  variables localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]];
  define{
    SUM(f) == (((f)[1]) + ((f)[2])) + ((f)[3])
    NUM_NODES == 3
    NODE_SET == (1) .. (NUM_NODES)
    MAX(a, b) == IF (a) > (b) THEN a ELSE b
  }
  
  fair process (UpdateGCntr = 0)
  {
    l1:
      if(TRUE) {
        with (i1 \in NODE_SET, i2 \in {x \in NODE_SET : ((localcntrs)[x]) # ((localcntrs)[i1])}) {
          with (res = [j \in DOMAIN ((localcntrs)[i1]) |-> MAX(((localcntrs)[i1])[j], ((localcntrs)[i2])[j])]) {
            with (localcntrs0 = [localcntrs EXCEPT ![i1] = res]) {
              localcntrs := [localcntrs0 EXCEPT ![i2] = res];
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
    update:
      with (value0 = 1) {
        assert (value0) > (0);
        localcntrs := [localcntrs EXCEPT ![self] = [(localcntrs)[self] EXCEPT ![self] = (((localcntrs)[self])[self]) + (value0)]];
        goto wait;
      };
    wait:
      with (yielded_localcntrs0 = SUM((localcntrs)[self])) {
        await (yielded_localcntrs0) = (NUM_NODES);
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "987734f7" /\ chksum(tla) = "897aacf1")
VARIABLES localcntrs, pc

(* define statement *)
SUM(f) == (((f)[1]) + ((f)[2])) + ((f)[3])
NUM_NODES == 3
NODE_SET == (1) .. (NUM_NODES)
MAX(a, b) == IF (a) > (b) THEN a ELSE b


vars == << localcntrs, pc >>

ProcSet == {0} \cup (NODE_SET)

Init == (* Global variables *)
        /\ localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in NODE_SET -> "update"]

l1 == /\ pc[0] = "l1"
      /\ IF TRUE
            THEN /\ \E i1 \in NODE_SET:
                      \E i2 \in {x \in NODE_SET : ((localcntrs)[x]) # ((localcntrs)[i1])}:
                        LET res == [j \in DOMAIN ((localcntrs)[i1]) |-> MAX(((localcntrs)[i1])[j], ((localcntrs)[i2])[j])] IN
                          LET localcntrs0 == [localcntrs EXCEPT ![i1] = res] IN
                            /\ localcntrs' = [localcntrs0 EXCEPT ![i2] = res]
                            /\ pc' = [pc EXCEPT ![0] = "l1"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED localcntrs

UpdateGCntr == l1

update(self) == /\ pc[self] = "update"
                /\ LET value0 == 1 IN
                     /\ Assert((value0) > (0), 
                               "Failure of assertion at line 101, column 9.")
                     /\ localcntrs' = [localcntrs EXCEPT ![self] = [(localcntrs)[self] EXCEPT ![self] = (((localcntrs)[self])[self]) + (value0)]]
                     /\ pc' = [pc EXCEPT ![self] = "wait"]

wait(self) == /\ pc[self] = "wait"
              /\ LET yielded_localcntrs0 == SUM((localcntrs)[self]) IN
                   /\ (yielded_localcntrs0) = (NUM_NODES)
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED localcntrs

Node(self) == update(self) \/ wait(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == UpdateGCntr
           \/ (\E self \in NODE_SET: Node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(UpdateGCntr)
        /\ \A self \in NODE_SET : WF_vars(Node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Properties

\* Note that we don't want to verify the G-Counter CRDT properties here, but we only 
\* want to verify some properties of the whole system.

EventualConvergence == []<>(\A n1, n2 \in NODE_SET: localcntrs[n1] = localcntrs[n2])

\* Cannot use Termination property due to UpdateGCntr process, which never 
\* terminates. We only want to check that all nodes will terminate.
NodeTermination == <>(\A n \in NODE_SET: pc[n] = "Done")

=============================================================================
