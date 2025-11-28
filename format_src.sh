#!/usr/bin/env bash

set -x -e

nix-shell --packages llvmPackages_21.clang-tools --command 'shopt -s globstar && clang-format -i --style=file:omnilink/.clang-format omnilink/**/*.{hpp,cpp,h}'
./mill --meta-level 1 mill.scalalib.scalafmt/
./mill __.fix
./mill mill.scalalib.scalafmt/
