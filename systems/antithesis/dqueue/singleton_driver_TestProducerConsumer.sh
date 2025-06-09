#!/usr/bin/env bash

set -x -e

/workspaces/antithesis/dqueue.test -test.run TestProducerConsumer
