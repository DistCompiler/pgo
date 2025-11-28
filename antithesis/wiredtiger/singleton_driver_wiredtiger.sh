#!/usr/bin/env bash

set -x -e

cd /workspaces/antithesis

mkdir ./tmp
./model_tracelink

mkdir ./check

mv tracing-*.log ./check/

./pgo.jar workloadgen-tla Storage.tla ./check/

cp MCStorageValidate.tla MCStorageValidate.cfg __TraceOps.tla ./check

./pgo.jar tlc check/MCStorageValidate.tla &>tracelink_out.txt && echo ok
