#!/usr/bin/env bash

set -euo pipefail

ulimit -n 500000

rm -f results.txt
export PGO_BENCHMARK_ITERATIONS=1
for NUM_NODES in {25..50}; do
    echo "Running test $1 with $NUM_NODES nodes ($PGO_BENCHMARK_ITERATIONS iterations)"
    env "PGO_BENCHMARK=true" "NUM_NODES=$NUM_NODES" go test -timeout 60s >stdout.txt 2>stderr.txt
done
