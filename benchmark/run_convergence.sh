#!/usr/bin/env bash

set -euo pipefail

ulimit -n 500000

rm -f results.txt
export PGO_BENCHMARK_ITERATIONS=3
export NUM_NODES=5
export BROADCAST_INTERVAL=5
for NUM_NODES in {1..50}; do
    echo "Running test $1 with $NUM_NODES nodes ($PGO_BENCHMARK_ITERATIONS iterations)"
    for PGO_BENCHMARK_ITERATIONS in {1..3}; do
        echo "Iteration $PGO_BENCHMARK_ITERATIONS..."
        rm -rf logs
        env "PGO_BENCHMARK=true" "NUM_NODES=$NUM_NODES" "BROADCAST_INTERVAL=$BROADCAST_INTERVAL" go test >stdout.txt 2>stderr.txt
        python "../convergence.py"
    done
done
