---- MODULE EmptyBlock ----
EXTENDS TLC

\* the only pcalgen-specific error! gogen can handle this,
\* but it's fundamentally invalid for a PCal algorithm to have no processes

(* (*:: expectedError: MPCalEffectivelyNoProcesses *) --mpcal EmptyBlock { } *)

\* BEGIN TRANSLATION
====