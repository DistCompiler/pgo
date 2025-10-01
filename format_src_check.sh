#!/usr/bin/env bash

set -x -e

./mill --meta-level 1 mill.scalalib.scalafmt/checkFormatAll
./mill __.fix --check
./mill mill.scalalib.scalafmt/checkFormatAll
