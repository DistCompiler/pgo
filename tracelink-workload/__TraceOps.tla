---- MODULE __TraceOps ----
EXTENDS IOUtils, Integers, Sequences, TLC

VARIABLE __pc
VARIABLE __viable_pids
CONSTANT __tracefile_name

pc == __pc
traces == IODeserialize(__tracefile_name, FALSE)

EpochCompareLT(left, right) ==
    LET leftHigh == left[1]
        leftLow == left[2]
        rightHigh == right[1]
        rightLow == right[2]
    IN  \/ leftHigh < rightHigh
        \/ /\ leftHigh = rightHigh
           /\ leftLow < rightLow

ViablePIDs ==
    LET pidsWithRecords == { pid \in DOMAIN traces : pc[pid] <= Len(traces[pid]) }
    IN  { pid \in pidsWithRecords :
            \lnot \E pid2 \in pidsWithRecords :
                /\ pid # pid2
                /\ EpochCompareLT(traces[pid2][pc[pid2]].op_end, traces[pid][pc[pid]].op_start) }

Init ==
    /\ pc = [pid \in DOMAIN traces |-> 1]
    /\ __viable_pids = ViablePIDs

====
