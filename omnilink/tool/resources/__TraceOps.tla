---- MODULE __TraceOps ----
EXTENDS IOUtils, Integers, Sequences, TLC, TLCExt, FiniteSetsExt

VARIABLES __vars, __Spec_vars, __state

VARIABLE __pc
VARIABLE __viable_pids
VARIABLE __action
CONSTANT __tracefile_name

traces == TLCCache(IODeserialize(__tracefile_name, TRUE), {__tracefile_name})

ViablePIDs ==
    LET pidsWithRecords == TLCCache({ pid \in DOMAIN traces : __pc[pid] <= Len(traces[pid]) }, {"pidsWithRecords"})
    IN  { pid \in pidsWithRecords :
            \lnot \E pid2 \in pidsWithRecords :
                /\ pid # pid2
                /\ traces[pid2][__pc[pid2]].op_end < traces[pid][__pc[pid]].op_start }

Init ==
    /\ TLCSet(42, "validation in progress")
    /\ __pc = [pid \in DOMAIN traces |-> 1]
    /\ __viable_pids = ViablePIDs
    /\ __action = <<>>

AtEndOfTrace ==
    \A pid \in DOMAIN traces:
        __pc[pid] = Len(traces[pid]) + 1

TerminateAtEnd ==
    AtEndOfTrace =>
    /\ TLCSet(42, "validation success")
    /\ TLCSet("exit", TRUE)

\* TLC won't print aliases when recording init state only, so print the options
\* directly, or the human can't see anything.
PrintOptionsAtInitState ==
    /\ TLCGet("level") = 1 \* Only print if we're at init.
    /\ PrintT("Deadlock reached at init state. Printing all initial actions:")
    /\ \A pid \in DOMAIN traces :
        IF traces[pid] # <<>>
        THEN PrintT(<<pid, traces[pid][1]>>)
        ELSE PrintT(<<pid, "has 0 events">>)
    /\ FALSE \* Fail so we don't influence state space exploration

EndCheck ==
    /\ TerminateAtEnd
    /\ FALSE

PostCondition ==
    Print("check validation succeeded", TLCGet(42) = "validation success")

DebugAlias ==
    [
        __successors |-> [ pid \in __viable_pids |-> traces[pid][__pc[pid]] ]
    ] @@ __state 

__pc_depth ==
    SumSet({ __pc[pid] : pid \in DOMAIN __pc })

====
