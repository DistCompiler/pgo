#!/usr/bin/env bash

set -x -e

cat << EOM >>$ANTITHESIS_OUTPUT_DIR/sdk.jsonl
{"antithesis_setup": { "status": "complete", "details": {"message": "Set up complete - ready for testing!" }}}
EOM

sleep infinity
