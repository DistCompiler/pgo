#!/bin/sh

# Runs PGo from the compiled class files, passing all command
# line argument directly to main().

java -ea -cp ./lib/plume.jar:./lib/json.jar:./bin/ pgo.PGoMain $*
