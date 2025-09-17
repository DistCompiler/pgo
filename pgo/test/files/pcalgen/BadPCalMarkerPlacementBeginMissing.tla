---- MODULE BadPCalMarkerPlacementBeginMissing ----
EXTENDS TLC

(* --mpcal BadPCalMarkerPlacementBeginMissing {
process (Nothing = 0) {
    lbl: skip;
}
} *)

\* +3 because it's not worth the pain of trying to get the error to _not_ point to END vs. the \* part of the comment
\*:: expectedError+3: PCalTagsError
\* END PLUSCAL TRANSLATION

\* BEGIN TRANSLATION

====