#!/usr/bin/env bash

env PGO_TWOPC_LOG=info go test --race | grep -e 'Commit(\(TRUE\|FALSE\)' | python3 test_correctness.py
