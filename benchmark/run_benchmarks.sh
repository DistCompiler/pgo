#!/usr/bin/env bash

set -euo pipefail

BENCHMARK="$PWD/run_benchmark.sh"

LOCK_DIR="./lock"
GCOUNTER_DIR="./gcounter"
SHCOUNTER_DIR="./shcounter"
SHOPCART_DIR="./shopcart"
SHOPCART_CRDT_DIR="./shopcart-crdt"

# cd "$SHOPCART_CRDT_DIR"
# $BENCHMARK "Shopcart CRDT" 1 'test -run .*Compare'
# cd -
# cd "$SHOPCART_DIR"
# $BENCHMARK "Shopcart" 1 "test"
# cd -
cd "$GCOUNTER_DIR"
$BENCHMARK "Counter" 3 "test"
cd -
cd "$SHCOUNTER_DIR"
$BENCHMARK "Counter" 3 "test"
cd -
# cd "$LOCK_DIR"
# $BENCHMARK "Lock" 3 "test"
# cd -
./make_graphs.sh
