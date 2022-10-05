------------------------------- MODULE gcounter -------------------------------

(********************
Specification of a simple system that demonstrates using a state-based 
inrement-only CRDT. More details in the CRDT technical report:
	https://hal.inria.fr/inria-00555588/document

Model-check this spec without checking for deadlocks and with the properties
defined in the end.
********************)

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NUM_NODES

CONSTANT BENCH_NUM_ROUNDS

RECURSIVE SUM(_, _)
SUM(f, d) == IF d = {} THEN 0
                       ELSE LET x == CHOOSE x \in d: TRUE
                            IN f[x] + SUM(f, d \ {x})

(********************

--mpcal gcounter {
    define {
        NODE_SET == 1..NUM_NODES

        MAX(a, b) == IF a > b THEN a ELSE b

        IncStart  == 0
        IncFinish == 1
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
            yield SUM($variable, DOMAIN $variable);
        }

        write {
            assert $value > 0;
			\* CRDT update
            yield [$variable EXCEPT ![self] = $variable[self] + $value];
        }
    } 

    mapping macro CasualHistory {
        read {
            yield $variable;
        }

        write {
            yield $variable \cup $value;
        }
    }
 
    archetype ANode(ref cntr[_], ref c[_]) {
    update:
        cntr[self] := 1;
        c[self] := {<<self, 1>>};
    wait:
        await cntr[self] = NUM_NODES;
    }

    archetype ANodeBench(ref cntr[_], ref out)
    variable r = 0;
    {
    nodeBenchLoop:
        while (r < BENCH_NUM_ROUNDS) {
        inc:
            cntr[self] := 1;
            out := [node |-> self, event |-> IncStart];
        waitInc:
            await cntr[self] >= (r + 1) * NUM_NODES;
            out := [node |-> self, event |-> IncFinish];
            r := r + 1;
        };
    }

    variables
        localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]];
        c = [id \in NODE_SET |-> {}];
        out;

    fair process (Node \in NODE_SET) == instance ANode(ref localcntrs[_], ref c[_])
        mapping localcntrs[_] via LocalGCntr
        mapping c[_] via CasualHistory;
    
    \* fair process (Node \in NODE_SET) == instance ANodeBench(ref localcntrs[_], ref out)
        \* mapping localcntrs[_] via LocalGCntr;

    fair process (UpdateGCntr = 0) {
    l1:
        while (TRUE) {
            with (i1 \in NODE_SET; i2 \in {x \in NODE_SET: localcntrs[x] # localcntrs[i1]}) {
                Merge(localcntrs, i1, i2);
                with (cn = c[i1] \cup c[i2]) {
                    c[i1] := cn;
                    c[i2] := cn;
                };
            };
        };
    }
}

\* BEGIN PLUSCAL TRANSLATION
--algorithm gcounter {
  variables localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]]; c = [id \in NODE_SET |-> {}]; out;
  define{
    NODE_SET == (1) .. (NUM_NODES)
    MAX(a, b) == IF (a) > (b) THEN a ELSE b
    IncStart == 0
    IncFinish == 1
  }
  
  fair process (UpdateGCntr = 0)
  {
    l1:
      if (TRUE) {
        with (
          i1 \in NODE_SET, 
          i2 \in {x \in NODE_SET : ((localcntrs)[x]) # ((localcntrs)[i1])}, 
          res0 = [j \in DOMAIN ((localcntrs)[i1]) |-> MAX(((localcntrs)[i1])[j], ((localcntrs)[i2])[j])], 
          localcntrs0 = [localcntrs EXCEPT ![i1] = res0]
        ) {
          localcntrs := [localcntrs0 EXCEPT ![i2] = res0];
          with (
            cn = ((c)[i1]) \union ((c)[i2]), 
            c0 = [c EXCEPT ![i1] = cn]
          ) {
            c := [c0 EXCEPT ![i2] = cn];
            goto l1;
          };
        };
      } else {
        goto Done;
      };
  }
  
  fair process (Node \in NODE_SET)
  {
    update:
      with (value1 = 1) {
        assert (value1) > (0);
        localcntrs := [localcntrs EXCEPT ![self] = [(localcntrs)[self] EXCEPT ![self] = (((localcntrs)[self])[self]) + (value1)]];
        with (value00 = {<<self, 1>>}) {
          c := [c EXCEPT ![self] = ((c)[self]) \union (value00)];
          goto wait;
        };
      };
    wait:
      with (yielded_localcntrs0 = SUM((localcntrs)[self], DOMAIN ((localcntrs)[self]))) {
        await (yielded_localcntrs0) = (NUM_NODES);
        goto Done;
      };
  }
}

\* END PLUSCAL TRANSLATION

********************)
\* BEGIN TRANSLATION (chksum(pcal) = "9b4327e4" /\ chksum(tla) = "c3190a67")
CONSTANT defaultInitValue
VARIABLES localcntrs, c, out, pc

(* define statement *)
NODE_SET == (1) .. (NUM_NODES)
MAX(a, b) == IF (a) > (b) THEN a ELSE b
IncStart == 0
IncFinish == 1


vars == << localcntrs, c, out, pc >>

ProcSet == {0} \cup (NODE_SET)

Init == (* Global variables *)
        /\ localcntrs = [id1 \in NODE_SET |-> [id2 \in NODE_SET |-> 0]]
        /\ c = [id \in NODE_SET |-> {}]
        /\ out = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in NODE_SET -> "update"]

l1 == /\ pc[0] = "l1"
      /\ IF TRUE
            THEN /\ \E i1 \in NODE_SET:
                      \E i2 \in {x \in NODE_SET : ((localcntrs)[x]) # ((localcntrs)[i1])}:
                        LET res0 == [j \in DOMAIN ((localcntrs)[i1]) |-> MAX(((localcntrs)[i1])[j], ((localcntrs)[i2])[j])] IN
                          LET localcntrs0 == [localcntrs EXCEPT ![i1] = res0] IN
                            /\ localcntrs' = [localcntrs0 EXCEPT ![i2] = res0]
                            /\ LET cn == ((c)[i1]) \union ((c)[i2]) IN
                                 LET c0 == [c EXCEPT ![i1] = cn] IN
                                   /\ c' = [c0 EXCEPT ![i2] = cn]
                                   /\ pc' = [pc EXCEPT ![0] = "l1"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED << localcntrs, c >>
      /\ out' = out

UpdateGCntr == l1

update(self) == /\ pc[self] = "update"
                /\ LET value1 == 1 IN
                     /\ Assert((value1) > (0), 
                               "Failure of assertion at line 153, column 9.")
                     /\ localcntrs' = [localcntrs EXCEPT ![self] = [(localcntrs)[self] EXCEPT ![self] = (((localcntrs)[self])[self]) + (value1)]]
                     /\ LET value00 == {<<self, 1>>} IN
                          /\ c' = [c EXCEPT ![self] = ((c)[self]) \union (value00)]
                          /\ pc' = [pc EXCEPT ![self] = "wait"]
                /\ out' = out

wait(self) == /\ pc[self] = "wait"
              /\ LET yielded_localcntrs0 == SUM((localcntrs)[self], DOMAIN ((localcntrs)[self])) IN
                   /\ (yielded_localcntrs0) = (NUM_NODES)
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << localcntrs, c, out >>

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

EventualDelivery == <>(\A i, j \in NODE_SET: (\A f \in c[i]: f \in c[j]))

StrongConvergence == \A i, j \in NODE_SET: (c[i] = c[j]) => (localcntrs[i] = localcntrs[j])

\* Note that we don't want to verify the G-Counter CRDT properties here, but we only 
\* want to verify some properties of the whole system.

NodesConvergence == []<>(\A n1, n2 \in NODE_SET: localcntrs[n1] = localcntrs[n2])

\* Cannot use Termination property due to UpdateGCntr process, which never 
\* terminates. We only want to check that all nodes will terminate.
NodeTermination == <>(\A n \in NODE_SET: pc[n] = "Done")

=============================================================================
