#!/usr/bin/env bash

set -euo pipefail

ulimit -n 500000

rm -f results.txt
export PGO_BENCHMARK_ITERATIONS=$2

TEST_COMMAND="$3"
for NUM_NODES in {1..50}; do
    echo "Running test $1 with $NUM_NODES nodes ($PGO_BENCHMARK_ITERATIONS iterations)"
    env "PGO_BENCHMARK=true" "NUM_NODES=$NUM_NODES" go $TEST_COMMAND >stdout.txt 2>stderr.txt
done
