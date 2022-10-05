---- MODULE NestedCRDTImpl ----
EXTENDS Sequences, TLC, Integers

CONSTANT BUFFER_SIZE

CONSTANTS ZERO_VALUE, COMBINE_FN(_, _), UPDATE_FN(_, _, _), VIEW_FN(_)

CONSTANTS READ_REQ, WRITE_REQ, ABORT_REQ, PRECOMMIT_REQ, COMMIT_REQ
CONSTANTS READ_ACK, WRITE_ACK, ABORT_ACK, PRECOMMIT_ACK, COMMIT_ACK

CONSTANTS EMPTY_CELL

CONSTANTS NUM_OPS

CONSTANTS NODE_IDS
ASSUME \A n \in NODE_IDS : n > 0

MAX_NODE_ID == (CHOOSE n \in NODE_IDS : \A n2 \in NODE_IDS : n >= n2)

RESOURCE_OF(n) == (MAX_NODE_ID + n)

RESOURCE_IDS == { RESOURCE_OF(n) : n \in NODE_IDS }

(* --mpcal NestedCRDTImpl {

define {
    IncStart  == 0
    IncFinish == 1
}

mapping macro TCPChannel {
    read {
        await Len($variable) > 0;
        with (msg = Head($variable)) {
            $variable := Tail($variable);
            yield msg;
        };
    }
    write {
        await Len($variable) < BUFFER_SIZE;
        yield Append($variable, $value);
    }
}

mapping macro SingleCellChannel {
    read {
        await $variable # EMPTY_CELL;
        with(v = $variable) {
            $variable := EMPTY_CELL;
            yield v;
        }
    }
    write {
        await $variable = EMPTY_CELL;
        yield $value;
    }
}

archetype ATestRig(ref crdt, ref countingCh, iterCount)
    variables i = 0;
{
loop:
    while(i < iterCount) {
        i := i + 1;
        crdt := 1;
        countingCh := crdt;
    };
endLoop:
    \* repeatedly read and send CRDT value, so that an external observer may poll for convergence
    countingCh := crdt;
    goto endLoop;
}

archetype ATestBench(ref crdt, ref out, iterCount, numNodes)
variable r = 0;
{
benchLoop:
    while (r < iterCount) {
    inc:
        crdt := 1;
        out := [node |-> self, event |-> IncStart];
    waitInc:
        await crdt >= (r + 1) * numNodes;
        out := [node |-> self, event |-> IncFinish];
        r := r + 1;
    };
}

archetype ACRDTResource(ref in[_], ref out[_], ref network[_], ref peers, ref timer)
variables remainingPeersToUpdate = {},
          req,
          criticalSectionInProgress = FALSE,
          state = ZERO_VALUE,
          readState = state;
{
receiveReq:
    either {
        req := in[self];
        if(req.tpe = READ_REQ) {
            if(\lnot criticalSectionInProgress) {
                readState := state;
                criticalSectionInProgress := TRUE;
            };
            out[self] := [tpe |-> READ_ACK, value |-> VIEW_FN(readState)];
        } else if(req.tpe = WRITE_REQ) {
            if(\lnot criticalSectionInProgress) {
                readState := state;
                criticalSectionInProgress := TRUE;
            };
            readState := UPDATE_FN(self, readState, req.value);
            out[self] := [tpe |-> WRITE_ACK];
        } else if(req.tpe = ABORT_REQ) {
            readState := ZERO_VALUE;
            criticalSectionInProgress := FALSE;
            out[self] := [tpe |-> ABORT_ACK];
        } else if(req.tpe = PRECOMMIT_REQ) {
            out[self] := [tpe |-> PRECOMMIT_ACK];
        } else if(req.tpe = COMMIT_REQ) {
            if(state # readState) {
                remainingPeersToUpdate := peers;
            };
            state := COMBINE_FN(state, readState);
            readState := ZERO_VALUE;
            criticalSectionInProgress := FALSE;
            out[self] := [tpe |-> COMMIT_ACK];
        } else {
            assert FALSE; \* should be unreachable
        };
    } or {
        with(updateVal = network[self]) {
            state := COMBINE_FN(updateVal, state);
        };
    } or {
        await timer;
        with(target \in remainingPeersToUpdate) {
            network[target] := state;
            remainingPeersToUpdate := remainingPeersToUpdate \ {target};
        };
    };
    goto receiveReq;
}

variables network = [ res \in RESOURCE_IDS |-> <<>> ],
          in = [res \in RESOURCE_IDS |-> EMPTY_CELL],
          out = [res \in RESOURCE_IDS |-> EMPTY_CELL];

fair process (CRDTResource \in RESOURCE_IDS) == instance ACRDTResource(ref in[_], ref out[_], ref network[_], RESOURCE_IDS \ {CRDTResource}, TRUE)
    mapping network[_] via TCPChannel
    mapping in[_] via SingleCellChannel
    mapping out[_] via SingleCellChannel;

fair process (Node \in NODE_IDS)
    variables opsDone = 0,
              writesPending = 0,
              writesAchieved = 0,
              shouldCommit = FALSE;
{
criticalSection:
    either {
        \* termination condition
        await \lnot shouldCommit;
        goto Done;
    } or {
        await opsDone < NUM_OPS;
        opsDone := opsDone + 1;
        goto readReq;
    } or {
        await opsDone < NUM_OPS;
        opsDone := opsDone + 1;
        goto writeReq;
    } or {
        await opsDone < NUM_OPS;
        opsDone := opsDone + 1;
        goto readReq;
    } or {
        await shouldCommit;
        goto preCommitReq;
    };

    \* read simulation;
readReq:
    in[RESOURCE_OF(self)] := [tpe |-> READ_REQ];
readAck:
    await out[RESOURCE_OF(self)] # EMPTY_CELL;
    assert out[RESOURCE_OF(self)].tpe = READ_ACK;
    out[RESOURCE_OF(self)] := EMPTY_CELL;
    shouldCommit := TRUE;
    goto criticalSection;

    \* abort simulation;
abortReq:
    in[RESOURCE_OF(self)] := [tpe |-> ABORT_REQ];
abortAck:
    await out[RESOURCE_OF(self)] # EMPTY_CELL;
    assert out[RESOURCE_OF(self)].tpe = ABORT_ACK;
    out[RESOURCE_OF(self)] := EMPTY_CELL;
    writesPending := 0;
    shouldCommit := FALSE;
    goto criticalSection;

writeReq:
    \* increment this here, so we can preserve monotonicity of relationship between CRDT state and Node counters
    writesPending := writesPending + 1;
    in[RESOURCE_OF(self)] := [tpe |-> WRITE_REQ, value |-> 1];
writeAck:
    await out[RESOURCE_OF(self)] # EMPTY_CELL;
    assert out[RESOURCE_OF(self)].tpe = WRITE_ACK;
    out[RESOURCE_OF(self)] := EMPTY_CELL;
    shouldCommit := TRUE;
    goto criticalSection;

preCommitReq:
    in[RESOURCE_OF(self)] := [tpe |-> PRECOMMIT_REQ];
preCommitAck:
    await out[RESOURCE_OF(self)] # EMPTY_CELL;
    assert out[RESOURCE_OF(self)].tpe = PRECOMMIT_ACK;
    out[RESOURCE_OF(self)] := EMPTY_CELL;
    either {
        await opsDone < NUM_OPS;
        opsDone := opsDone + 1;
        goto abortReq;
    } or {
    commitReq:
        in[RESOURCE_OF(self)] := [tpe |-> COMMIT_REQ];
    commitAck:
        await out[RESOURCE_OF(self)] # EMPTY_CELL;
        assert out[RESOURCE_OF(self)].tpe = COMMIT_ACK;
        out[RESOURCE_OF(self)] := EMPTY_CELL;

        \* reset and update counters
        writesAchieved := writesAchieved + writesPending;
        writesPending := 0;
        shouldCommit := FALSE;
        goto criticalSection;
    };
}

}

\* BEGIN PLUSCAL TRANSLATION
--algorithm NestedCRDTImpl {
  variables network = [res \in RESOURCE_IDS |-> <<>>]; in = [res \in RESOURCE_IDS |-> EMPTY_CELL]; out = [res \in RESOURCE_IDS |-> EMPTY_CELL];
  define{
    IncStart == 0
    IncFinish == 1
  }
  
  fair process (Node \in NODE_IDS)
    variables opsDone = 0; writesPending = 0; writesAchieved = 0; shouldCommit = FALSE;
  {
    criticalSection:
      either {
        await ~ (shouldCommit);
        goto Done;
      } or {
        await (opsDone) < (NUM_OPS);
        opsDone := (opsDone) + (1);
        goto readReq;
      } or {
        await (opsDone) < (NUM_OPS);
        opsDone := (opsDone) + (1);
        goto writeReq;
      } or {
        await (opsDone) < (NUM_OPS);
        opsDone := (opsDone) + (1);
        goto readReq;
      } or {
        await shouldCommit;
        goto preCommitReq;
      };
    readReq:
      in := [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> READ_REQ]];
      goto readAck;
    readAck:
      await ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL);
      assert (((out)[RESOURCE_OF(self)]).tpe) = (READ_ACK);
      out := [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL];
      shouldCommit := TRUE;
      goto criticalSection;
    abortReq:
      in := [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> ABORT_REQ]];
      goto abortAck;
    abortAck:
      await ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL);
      assert (((out)[RESOURCE_OF(self)]).tpe) = (ABORT_ACK);
      out := [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL];
      writesPending := 0;
      shouldCommit := FALSE;
      goto criticalSection;
    writeReq:
      writesPending := (writesPending) + (1);
      in := [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> WRITE_REQ, value |-> 1]];
      goto writeAck;
    writeAck:
      await ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL);
      assert (((out)[RESOURCE_OF(self)]).tpe) = (WRITE_ACK);
      out := [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL];
      shouldCommit := TRUE;
      goto criticalSection;
    preCommitReq:
      in := [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> PRECOMMIT_REQ]];
      goto preCommitAck;
    preCommitAck:
      await ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL);
      assert (((out)[RESOURCE_OF(self)]).tpe) = (PRECOMMIT_ACK);
      out := [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL];
      either {
        await (opsDone) < (NUM_OPS);
        opsDone := (opsDone) + (1);
        goto abortReq;
      } or {
        goto commitReq;
      };
    commitReq:
      in := [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> COMMIT_REQ]];
      goto commitAck;
    commitAck:
      await ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL);
      assert (((out)[RESOURCE_OF(self)]).tpe) = (COMMIT_ACK);
      out := [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL];
      writesAchieved := (writesAchieved) + (writesPending);
      writesPending := 0;
      shouldCommit := FALSE;
      goto criticalSection;
  }
  
  fair process (CRDTResource \in RESOURCE_IDS)
    variables remainingPeersToUpdate = {}; req; criticalSectionInProgress = FALSE; state = ZERO_VALUE; readState = state; peers = (RESOURCE_IDS) \ ({self}); timer = TRUE;
  {
    receiveReq:
      either {
        await ((in)[self]) # (EMPTY_CELL);
        with (v00 = (in)[self]) {
          in := [in EXCEPT ![self] = EMPTY_CELL];
          with (yielded_in0 = v00) {
            req := yielded_in0;
            if (((req).tpe) = (READ_REQ)) {
              if (~ (criticalSectionInProgress)) {
                readState := state;
                criticalSectionInProgress := TRUE;
                with (value00 = [tpe |-> READ_ACK, value |-> VIEW_FN(readState)]) {
                  await ((out)[self]) = (EMPTY_CELL);
                  out := [out EXCEPT ![self] = value00];
                  goto receiveReq;
                };
              } else {
                with (value01 = [tpe |-> READ_ACK, value |-> VIEW_FN(readState)]) {
                  await ((out)[self]) = (EMPTY_CELL);
                  out := [out EXCEPT ![self] = value01];
                  goto receiveReq;
                };
              };
            } else {
              if (((req).tpe) = (WRITE_REQ)) {
                if (~ (criticalSectionInProgress)) {
                  with (readState1 = state) {
                    criticalSectionInProgress := TRUE;
                    readState := UPDATE_FN(self, readState1, (req).value);
                    with (value10 = [tpe |-> WRITE_ACK]) {
                      await ((out)[self]) = (EMPTY_CELL);
                      out := [out EXCEPT ![self] = value10];
                      goto receiveReq;
                    };
                  };
                } else {
                  readState := UPDATE_FN(self, readState, (req).value);
                  with (value11 = [tpe |-> WRITE_ACK]) {
                    await ((out)[self]) = (EMPTY_CELL);
                    out := [out EXCEPT ![self] = value11];
                    goto receiveReq;
                  };
                };
              } else {
                if (((req).tpe) = (ABORT_REQ)) {
                  readState := ZERO_VALUE;
                  criticalSectionInProgress := FALSE;
                  with (value20 = [tpe |-> ABORT_ACK]) {
                    await ((out)[self]) = (EMPTY_CELL);
                    out := [out EXCEPT ![self] = value20];
                    goto receiveReq;
                  };
                } else {
                  if (((req).tpe) = (PRECOMMIT_REQ)) {
                    with (value30 = [tpe |-> PRECOMMIT_ACK]) {
                      await ((out)[self]) = (EMPTY_CELL);
                      out := [out EXCEPT ![self] = value30];
                      goto receiveReq;
                    };
                  } else {
                    if (((req).tpe) = (COMMIT_REQ)) {
                      if ((state) # (readState)) {
                        remainingPeersToUpdate := peers;
                        state := COMBINE_FN(state, readState);
                        readState := ZERO_VALUE;
                        criticalSectionInProgress := FALSE;
                        with (value40 = [tpe |-> COMMIT_ACK]) {
                          await ((out)[self]) = (EMPTY_CELL);
                          out := [out EXCEPT ![self] = value40];
                          goto receiveReq;
                        };
                      } else {
                        state := COMBINE_FN(state, readState);
                        readState := ZERO_VALUE;
                        criticalSectionInProgress := FALSE;
                        with (value41 = [tpe |-> COMMIT_ACK]) {
                          await ((out)[self]) = (EMPTY_CELL);
                          out := [out EXCEPT ![self] = value41];
                          goto receiveReq;
                        };
                      };
                    } else {
                      assert FALSE;
                      goto receiveReq;
                    };
                  };
                };
              };
            };
          };
        };
      } or {
        await (Len((network)[self])) > (0);
        with (msg00 = Head((network)[self])) {
          network := [network EXCEPT ![self] = Tail((network)[self])];
          with (
            yielded_network0 = msg00, 
            updateVal1 = yielded_network0
          ) {
            state := COMBINE_FN(updateVal1, state);
            goto receiveReq;
          };
        };
      } or {
        await timer;
        with (
          target1 \in remainingPeersToUpdate, 
          value50 = state
        ) {
          await (Len((network)[target1])) < (BUFFER_SIZE);
          network := [network EXCEPT ![target1] = Append((network)[target1], value50)];
          remainingPeersToUpdate := (remainingPeersToUpdate) \ ({target1});
          goto receiveReq;
        };
      };
  }
}

\* END PLUSCAL TRANSLATION

*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a9d530ba31a77b97e4f89c5980615dd0 (chksum(pcal) = "d88ea5f8" /\ chksum(tla) = "ded9afdb") (chksum(pcal) = "d88ea5f8" /\ chksum(tla) = "ded9afdb") (chksum(pcal) = "d88ea5f8" /\ chksum(tla) = "ded9afdb")
CONSTANT defaultInitValue
VARIABLES network, in, out, pc

(* define statement *)
IncStart == 0
IncFinish == 1

VARIABLES opsDone, writesPending, writesAchieved, shouldCommit, 
          remainingPeersToUpdate, req, criticalSectionInProgress, state, 
          readState, peers, timer

vars == << network, in, out, pc, opsDone, writesPending, writesAchieved, 
           shouldCommit, remainingPeersToUpdate, req, 
           criticalSectionInProgress, state, readState, peers, timer >>

ProcSet == (NODE_IDS) \cup (RESOURCE_IDS)

Init == (* Global variables *)
        /\ network = [res \in RESOURCE_IDS |-> <<>>]
        /\ in = [res \in RESOURCE_IDS |-> EMPTY_CELL]
        /\ out = [res \in RESOURCE_IDS |-> EMPTY_CELL]
        (* Process Node *)
        /\ opsDone = [self \in NODE_IDS |-> 0]
        /\ writesPending = [self \in NODE_IDS |-> 0]
        /\ writesAchieved = [self \in NODE_IDS |-> 0]
        /\ shouldCommit = [self \in NODE_IDS |-> FALSE]
        (* Process CRDTResource *)
        /\ remainingPeersToUpdate = [self \in RESOURCE_IDS |-> {}]
        /\ req = [self \in RESOURCE_IDS |-> defaultInitValue]
        /\ criticalSectionInProgress = [self \in RESOURCE_IDS |-> FALSE]
        /\ state = [self \in RESOURCE_IDS |-> ZERO_VALUE]
        /\ readState = [self \in RESOURCE_IDS |-> state[self]]
        /\ peers = [self \in RESOURCE_IDS |-> (RESOURCE_IDS) \ ({self})]
        /\ timer = [self \in RESOURCE_IDS |-> TRUE]
        /\ pc = [self \in ProcSet |-> CASE self \in NODE_IDS -> "criticalSection"
                                        [] self \in RESOURCE_IDS -> "receiveReq"]

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ \/ /\ ~ (shouldCommit[self])
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED opsDone
                            \/ /\ (opsDone[self]) < (NUM_OPS)
                               /\ opsDone' = [opsDone EXCEPT ![self] = (opsDone[self]) + (1)]
                               /\ pc' = [pc EXCEPT ![self] = "readReq"]
                            \/ /\ (opsDone[self]) < (NUM_OPS)
                               /\ opsDone' = [opsDone EXCEPT ![self] = (opsDone[self]) + (1)]
                               /\ pc' = [pc EXCEPT ![self] = "writeReq"]
                            \/ /\ (opsDone[self]) < (NUM_OPS)
                               /\ opsDone' = [opsDone EXCEPT ![self] = (opsDone[self]) + (1)]
                               /\ pc' = [pc EXCEPT ![self] = "readReq"]
                            \/ /\ shouldCommit[self]
                               /\ pc' = [pc EXCEPT ![self] = "preCommitReq"]
                               /\ UNCHANGED opsDone
                         /\ UNCHANGED << network, in, out, writesPending, 
                                         writesAchieved, shouldCommit, 
                                         remainingPeersToUpdate, req, 
                                         criticalSectionInProgress, state, 
                                         readState, peers, timer >>

readReq(self) == /\ pc[self] = "readReq"
                 /\ in' = [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> READ_REQ]]
                 /\ pc' = [pc EXCEPT ![self] = "readAck"]
                 /\ UNCHANGED << network, out, opsDone, writesPending, 
                                 writesAchieved, shouldCommit, 
                                 remainingPeersToUpdate, req, 
                                 criticalSectionInProgress, state, readState, 
                                 peers, timer >>

readAck(self) == /\ pc[self] = "readAck"
                 /\ ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL)
                 /\ Assert((((out)[RESOURCE_OF(self)]).tpe) = (READ_ACK), 
                           "Failure of assertion at line 276, column 7.")
                 /\ out' = [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL]
                 /\ shouldCommit' = [shouldCommit EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                 /\ UNCHANGED << network, in, opsDone, writesPending, 
                                 writesAchieved, remainingPeersToUpdate, req, 
                                 criticalSectionInProgress, state, readState, 
                                 peers, timer >>

abortReq(self) == /\ pc[self] = "abortReq"
                  /\ in' = [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> ABORT_REQ]]
                  /\ pc' = [pc EXCEPT ![self] = "abortAck"]
                  /\ UNCHANGED << network, out, opsDone, writesPending, 
                                  writesAchieved, shouldCommit, 
                                  remainingPeersToUpdate, req, 
                                  criticalSectionInProgress, state, readState, 
                                  peers, timer >>

abortAck(self) == /\ pc[self] = "abortAck"
                  /\ ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL)
                  /\ Assert((((out)[RESOURCE_OF(self)]).tpe) = (ABORT_ACK), 
                            "Failure of assertion at line 285, column 7.")
                  /\ out' = [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL]
                  /\ writesPending' = [writesPending EXCEPT ![self] = 0]
                  /\ shouldCommit' = [shouldCommit EXCEPT ![self] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                  /\ UNCHANGED << network, in, opsDone, writesAchieved, 
                                  remainingPeersToUpdate, req, 
                                  criticalSectionInProgress, state, readState, 
                                  peers, timer >>

writeReq(self) == /\ pc[self] = "writeReq"
                  /\ writesPending' = [writesPending EXCEPT ![self] = (writesPending[self]) + (1)]
                  /\ in' = [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> WRITE_REQ, value |-> 1]]
                  /\ pc' = [pc EXCEPT ![self] = "writeAck"]
                  /\ UNCHANGED << network, out, opsDone, writesAchieved, 
                                  shouldCommit, remainingPeersToUpdate, req, 
                                  criticalSectionInProgress, state, readState, 
                                  peers, timer >>

writeAck(self) == /\ pc[self] = "writeAck"
                  /\ ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL)
                  /\ Assert((((out)[RESOURCE_OF(self)]).tpe) = (WRITE_ACK), 
                            "Failure of assertion at line 296, column 7.")
                  /\ out' = [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL]
                  /\ shouldCommit' = [shouldCommit EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                  /\ UNCHANGED << network, in, opsDone, writesPending, 
                                  writesAchieved, remainingPeersToUpdate, req, 
                                  criticalSectionInProgress, state, readState, 
                                  peers, timer >>

preCommitReq(self) == /\ pc[self] = "preCommitReq"
                      /\ in' = [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> PRECOMMIT_REQ]]
                      /\ pc' = [pc EXCEPT ![self] = "preCommitAck"]
                      /\ UNCHANGED << network, out, opsDone, writesPending, 
                                      writesAchieved, shouldCommit, 
                                      remainingPeersToUpdate, req, 
                                      criticalSectionInProgress, state, 
                                      readState, peers, timer >>

preCommitAck(self) == /\ pc[self] = "preCommitAck"
                      /\ ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL)
                      /\ Assert((((out)[RESOURCE_OF(self)]).tpe) = (PRECOMMIT_ACK), 
                                "Failure of assertion at line 305, column 7.")
                      /\ out' = [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL]
                      /\ \/ /\ (opsDone[self]) < (NUM_OPS)
                            /\ opsDone' = [opsDone EXCEPT ![self] = (opsDone[self]) + (1)]
                            /\ pc' = [pc EXCEPT ![self] = "abortReq"]
                         \/ /\ pc' = [pc EXCEPT ![self] = "commitReq"]
                            /\ UNCHANGED opsDone
                      /\ UNCHANGED << network, in, writesPending, 
                                      writesAchieved, shouldCommit, 
                                      remainingPeersToUpdate, req, 
                                      criticalSectionInProgress, state, 
                                      readState, peers, timer >>

commitReq(self) == /\ pc[self] = "commitReq"
                   /\ in' = [in EXCEPT ![RESOURCE_OF(self)] = [tpe |-> COMMIT_REQ]]
                   /\ pc' = [pc EXCEPT ![self] = "commitAck"]
                   /\ UNCHANGED << network, out, opsDone, writesPending, 
                                   writesAchieved, shouldCommit, 
                                   remainingPeersToUpdate, req, 
                                   criticalSectionInProgress, state, readState, 
                                   peers, timer >>

commitAck(self) == /\ pc[self] = "commitAck"
                   /\ ((out)[RESOURCE_OF(self)]) # (EMPTY_CELL)
                   /\ Assert((((out)[RESOURCE_OF(self)]).tpe) = (COMMIT_ACK), 
                             "Failure of assertion at line 319, column 7.")
                   /\ out' = [out EXCEPT ![RESOURCE_OF(self)] = EMPTY_CELL]
                   /\ writesAchieved' = [writesAchieved EXCEPT ![self] = (writesAchieved[self]) + (writesPending[self])]
                   /\ writesPending' = [writesPending EXCEPT ![self] = 0]
                   /\ shouldCommit' = [shouldCommit EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                   /\ UNCHANGED << network, in, opsDone, 
                                   remainingPeersToUpdate, req, 
                                   criticalSectionInProgress, state, readState, 
                                   peers, timer >>

Node(self) == criticalSection(self) \/ readReq(self) \/ readAck(self)
                 \/ abortReq(self) \/ abortAck(self) \/ writeReq(self)
                 \/ writeAck(self) \/ preCommitReq(self)
                 \/ preCommitAck(self) \/ commitReq(self)
                 \/ commitAck(self)

receiveReq(self) == /\ pc[self] = "receiveReq"
                    /\ \/ /\ ((in)[self]) # (EMPTY_CELL)
                          /\ LET v00 == (in)[self] IN
                               /\ in' = [in EXCEPT ![self] = EMPTY_CELL]
                               /\ LET yielded_in0 == v00 IN
                                    /\ req' = [req EXCEPT ![self] = yielded_in0]
                                    /\ IF ((req'[self]).tpe) = (READ_REQ)
                                          THEN /\ IF ~ (criticalSectionInProgress[self])
                                                     THEN /\ readState' = [readState EXCEPT ![self] = state[self]]
                                                          /\ criticalSectionInProgress' = [criticalSectionInProgress EXCEPT ![self] = TRUE]
                                                          /\ LET value00 == [tpe |-> READ_ACK, value |-> VIEW_FN(readState'[self])] IN
                                                               /\ ((out)[self]) = (EMPTY_CELL)
                                                               /\ out' = [out EXCEPT ![self] = value00]
                                                               /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                     ELSE /\ LET value01 == [tpe |-> READ_ACK, value |-> VIEW_FN(readState[self])] IN
                                                               /\ ((out)[self]) = (EMPTY_CELL)
                                                               /\ out' = [out EXCEPT ![self] = value01]
                                                               /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                          /\ UNCHANGED << criticalSectionInProgress, 
                                                                          readState >>
                                               /\ UNCHANGED << remainingPeersToUpdate, 
                                                               state >>
                                          ELSE /\ IF ((req'[self]).tpe) = (WRITE_REQ)
                                                     THEN /\ IF ~ (criticalSectionInProgress[self])
                                                                THEN /\ LET readState1 == state[self] IN
                                                                          /\ criticalSectionInProgress' = [criticalSectionInProgress EXCEPT ![self] = TRUE]
                                                                          /\ readState' = [readState EXCEPT ![self] = UPDATE_FN(self, readState1, (req'[self]).value)]
                                                                          /\ LET value10 == [tpe |-> WRITE_ACK] IN
                                                                               /\ ((out)[self]) = (EMPTY_CELL)
                                                                               /\ out' = [out EXCEPT ![self] = value10]
                                                                               /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                ELSE /\ readState' = [readState EXCEPT ![self] = UPDATE_FN(self, readState[self], (req'[self]).value)]
                                                                     /\ LET value11 == [tpe |-> WRITE_ACK] IN
                                                                          /\ ((out)[self]) = (EMPTY_CELL)
                                                                          /\ out' = [out EXCEPT ![self] = value11]
                                                                          /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                     /\ UNCHANGED criticalSectionInProgress
                                                          /\ UNCHANGED << remainingPeersToUpdate, 
                                                                          state >>
                                                     ELSE /\ IF ((req'[self]).tpe) = (ABORT_REQ)
                                                                THEN /\ readState' = [readState EXCEPT ![self] = ZERO_VALUE]
                                                                     /\ criticalSectionInProgress' = [criticalSectionInProgress EXCEPT ![self] = FALSE]
                                                                     /\ LET value20 == [tpe |-> ABORT_ACK] IN
                                                                          /\ ((out)[self]) = (EMPTY_CELL)
                                                                          /\ out' = [out EXCEPT ![self] = value20]
                                                                          /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                     /\ UNCHANGED << remainingPeersToUpdate, 
                                                                                     state >>
                                                                ELSE /\ IF ((req'[self]).tpe) = (PRECOMMIT_REQ)
                                                                           THEN /\ LET value30 == [tpe |-> PRECOMMIT_ACK] IN
                                                                                     /\ ((out)[self]) = (EMPTY_CELL)
                                                                                     /\ out' = [out EXCEPT ![self] = value30]
                                                                                     /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                                /\ UNCHANGED << remainingPeersToUpdate, 
                                                                                                criticalSectionInProgress, 
                                                                                                state, 
                                                                                                readState >>
                                                                           ELSE /\ IF ((req'[self]).tpe) = (COMMIT_REQ)
                                                                                      THEN /\ IF (state[self]) # (readState[self])
                                                                                                 THEN /\ remainingPeersToUpdate' = [remainingPeersToUpdate EXCEPT ![self] = peers[self]]
                                                                                                      /\ state' = [state EXCEPT ![self] = COMBINE_FN(state[self], readState[self])]
                                                                                                      /\ readState' = [readState EXCEPT ![self] = ZERO_VALUE]
                                                                                                      /\ criticalSectionInProgress' = [criticalSectionInProgress EXCEPT ![self] = FALSE]
                                                                                                      /\ LET value40 == [tpe |-> COMMIT_ACK] IN
                                                                                                           /\ ((out)[self]) = (EMPTY_CELL)
                                                                                                           /\ out' = [out EXCEPT ![self] = value40]
                                                                                                           /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                                                 ELSE /\ state' = [state EXCEPT ![self] = COMBINE_FN(state[self], readState[self])]
                                                                                                      /\ readState' = [readState EXCEPT ![self] = ZERO_VALUE]
                                                                                                      /\ criticalSectionInProgress' = [criticalSectionInProgress EXCEPT ![self] = FALSE]
                                                                                                      /\ LET value41 == [tpe |-> COMMIT_ACK] IN
                                                                                                           /\ ((out)[self]) = (EMPTY_CELL)
                                                                                                           /\ out' = [out EXCEPT ![self] = value41]
                                                                                                           /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                                                      /\ UNCHANGED remainingPeersToUpdate
                                                                                      ELSE /\ Assert(FALSE, 
                                                                                                     "Failure of assertion at line 412, column 23.")
                                                                                           /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                                                                                           /\ UNCHANGED << out, 
                                                                                                           remainingPeersToUpdate, 
                                                                                                           criticalSectionInProgress, 
                                                                                                           state, 
                                                                                                           readState >>
                          /\ UNCHANGED network
                       \/ /\ (Len((network)[self])) > (0)
                          /\ LET msg00 == Head((network)[self]) IN
                               /\ network' = [network EXCEPT ![self] = Tail((network)[self])]
                               /\ LET yielded_network0 == msg00 IN
                                    LET updateVal1 == yielded_network0 IN
                                      /\ state' = [state EXCEPT ![self] = COMBINE_FN(updateVal1, state[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                          /\ UNCHANGED <<in, out, remainingPeersToUpdate, req, criticalSectionInProgress, readState>>
                       \/ /\ timer[self]
                          /\ \E target1 \in remainingPeersToUpdate[self]:
                               LET value50 == state[self] IN
                                 /\ (Len((network)[target1])) < (BUFFER_SIZE)
                                 /\ network' = [network EXCEPT ![target1] = Append((network)[target1], value50)]
                                 /\ remainingPeersToUpdate' = [remainingPeersToUpdate EXCEPT ![self] = (remainingPeersToUpdate[self]) \ ({target1})]
                                 /\ pc' = [pc EXCEPT ![self] = "receiveReq"]
                          /\ UNCHANGED <<in, out, req, criticalSectionInProgress, state, readState>>
                    /\ UNCHANGED << opsDone, writesPending, writesAchieved, 
                                    shouldCommit, peers, timer >>

CRDTResource(self) == receiveReq(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in NODE_IDS: Node(self))
           \/ (\E self \in RESOURCE_IDS: CRDTResource(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NODE_IDS : WF_vars(Node(self))
        /\ \A self \in RESOURCE_IDS : WF_vars(CRDTResource(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c9b2b573ce783e8d24799e5d51491031

MonotonicState == [][\A self \in RESOURCE_IDS : \A k \in DOMAIN state[self] : state[self][k] <= state'[self][k]]_vars

NodesTerminated == \A self \in NODE_IDS : pc[self] = "Done"

NodeTermination == <> NodesTerminated

CRDTsStabilised == \A self \in RESOURCE_IDS : remainingPeersToUpdate[self] = {} /\ \lnot criticalSectionInProgress[self]

CRDTStabilises == <>[](CRDTsStabilised)

CRDTSync == <>(\A <<self1, self2>> \in RESOURCE_IDS \X RESOURCE_IDS : VIEW_FN(state[self1]) = VIEW_FN(state[self2]))

RECURSIVE Sum(_)

Sum(s) == IF s = {} THEN 0
          ELSE LET elem == CHOOSE x \in s : TRUE
               IN elem + Sum(s \ {elem})

CRDTParity == <>[](LET expectedTotal == Sum({ writesAchieved[self] : self \in NODE_IDS })
                 IN NodesTerminated /\ CRDTsStabilised /\ \A self \in RESOURCE_IDS : VIEW_FN(state[self]) = expectedTotal)

StateSanity == Sum({ VIEW_FN(state[self]) : self \in RESOURCE_IDS }) <= Sum({ writesPending[self] + writesAchieved[self] : self \in NODE_IDS })

====
