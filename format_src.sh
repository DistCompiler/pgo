#!/usr/bin/env bash

set -x -e

./mill --meta-level 1 mill.scalalib.scalafmt/
./mill mill.scalalib.scalafmt/
