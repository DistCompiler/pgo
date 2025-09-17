---- MODULE __TraceOps ----
EXTENDS IOUtils, Integers, Sequences, TLC, TLCExt, FiniteSetsExt

VARIABLES __vars, __Spec_vars, __state

VARIABLE __pc
VARIABLE __viable_pids
VARIABLE __action
CONSTANT __tracefile_name

traces == TLCCache(IODeserialize(__tracefile_name, FALSE), {__tracefile_name})

efficientView == <<__Spec_vars, TLCGet("level")>>

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

AtEndOfTracePC ==
    Print("check validation succeeded", TLCGet(42) = "validation success")

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
    /\ CASE AtEndOfTrace -> TRUE \* (a)
         [] TLCGet("queue") # 0 -> TRUE \* (b)
         [] OTHER -> PrintOptionsAtInitState \* Always false, diagnostic only.
       (* THIS IS A HACK. Read below for dragons.
        * 
        * Assumptions:
        * - Deadlock checking is active.
        * - TLC is performing breadth-first search (BFS). This will be completely
        *   broken with a depth-first queue, and I didn't even think about
        *   simulation mode. In fact, I have seen depth-first queue accept
        *   invalid outputs with this definition, so do not trust anything
        *   you see if this definition is combined with non BFS evaluation.
        * - Because this expression comes syntactically after all useful
        *   next-states disjunctions, it will be evaluated after they have
        *   had a chance to add items to the state queue.
        *   !THIS IS THE HACK PART! -> it relies on a (true as of writing)
        *   assumption regarding how TLC evaluates next-state relations.
        * - Therefore, if we get here and our state queue is empty, we have
        *   exhausted all other possible ways to move beyond our next-state.
        * 
        * Behavior:
        * (a) If we are at end of trace, allow a self-loop, because that is
        *     our desired outcome and it's fine to stop here.
        * (b) If we are out of options but there are states on the queue,
        *     allow a self loop to make TLC keep searching.
        * 
        * If we have not exhausted the trace and the queue is empty, we should
        * force TLC to report a deadlock at exactly this state. Do this
        * by disabling this action and therefore not adding a self loop.
        * Because of how BFS works, our current trace is a pseudo-randomly
        * selected longest prefix TLC could find where all predecessor states
        * could be linearized. If there was more than one way to do that, TLC
        * will be forced to report the last one that comes off its state queue.
        * Careful use of the debugger should allow exploring other
        * interpretations (breakpoint on the trace length to see them).
        *)
    /\ UNCHANGED __vars

DebugAlias ==
    [
        __successors |-> [ pid \in __viable_pids |-> traces[pid][__pc[pid]] ]
    ] @@ __state 

====
