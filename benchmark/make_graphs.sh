#!/usr/bin/env bash

set -euo pipefail

for graph_file in graphscripts/*.p; do
    echo "Making graph $graph_file"
    gnuplot -d -e "load 'graphscripts/base'" $graph_file
done
