#!/usr/bin/env bash

set -x -e

nix-shell --packages llvmPackages_21.clang-tools --command 'shopt -s globstar && clang-format --dry-run -Werror --style=file:omnilink/.clang-format omnilink/**/*.{hpp,cpp,h}'
./mill --meta-level 1 mill.scalalib.scalafmt/checkFormatAll
./mill __.fix --check
./mill mill.scalalib.scalafmt/checkFormatAll
