#!/usr/bin/env bash

set -x -e

echo '{"antithesis_setup": { "status": "complete", "details": {"message": "Set up complete - ready for testing!" }}}' >>$ANTITHESIS_OUTPUT_DIR/sdk.jsonl

sleep infinity
