#!/usr/bin/env bash

set -euo pipefail

BENCHMARK="$PWD/run_benchmark.sh"

LOCK_DIR="./lock"
SHCOUNTER_DIR="../test/files/general/shcounter.tla.gotests"

# cd "$LOCK_DIR"
# $BENCHMARK "Lock"
# cd -
cd "$SHCOUNTER_DIR"
$BENCHMARK "Counter"
cd -
gnuplot graph.p
