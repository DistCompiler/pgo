#!/usr/bin/env bash

set -x -e

./mill --meta-level 1 mill.scalalib.scalafmt/checkFormatAll
./mill mill.scalalib.scalafmt/checkFormatAll
