#!/usr/bin/env bash

set -euo pipefail

CONVERGENCE="$PWD/run_convergence.sh"
SHOPCART_CRDT_DIR="./shopcart-crdt"

cd "$SHOPCART_CRDT_DIR"
  $CONVERGENCE "Shopcart-CRDT"
cd -