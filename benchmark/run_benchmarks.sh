#!/usr/bin/env bash

set -euo pipefail

BENCHMARK="$PWD/run_benchmark.sh"

GCOUNTER_DIR="../test/files/general/gcounter.tla.gotests"
SHOPCART_CRDT_DIR="./shopcart-crdt"

cd "$GCOUNTER_DIR"
$BENCHMARK "Counter-CRDT"
cd -

cd "$SHOPCART_CRDT_DIR"
$BENCHMARK "Shopcart-CRDT"
cd -

gnuplot graph.p