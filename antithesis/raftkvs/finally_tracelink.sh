#!/usr/bin/env bash

set -e -x

/workspaces/antithesis/pgo.jar tracegen /workspaces/antithesis/raftkvs.tla /workspaces/antithesis/traces_found --noall-paths --progress-inv
/workspaces/antithesis/pgo.jar tlc --dfs -- /workspaces/antithesis/traces_found/raftkvsValidate.tla
