#!/usr/bin/env bash

set -euo pipefail

BENCHMARK="$PWD/run_benchmark.sh"

LOCK_DIR="./lock"
SHCOUNTER_DIR="./shcounter"

cd "$SHCOUNTER_DIR"
$BENCHMARK "Counter"
cd -
cd "$LOCK_DIR"
$BENCHMARK "Lock"
cd -
gnuplot graph.p
