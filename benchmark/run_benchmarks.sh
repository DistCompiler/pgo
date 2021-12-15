#!/usr/bin/env bash

set -euo pipefail

BENCHMARK="$PWD/run_benchmark.sh"

LOCK_DIR="./lock"
SHCOUNTER_DIR="./shcounter"
SHOPCART_DIR="./shopcart"

cd "$SHOPCART_DIR"
$BENCHMARK "Shopcart" 1
cd -
cd "$SHCOUNTER_DIR"
$BENCHMARK "Counter" 3
cd -
cd "$LOCK_DIR"
$BENCHMARK "Lock" 3
cd -
./make_graphs.sh
