#!/usr/bin/env bash

./mill --meta-level 1 mill.scalalib.scalafmt/
./mill mill.scalalib.scalafmt/
