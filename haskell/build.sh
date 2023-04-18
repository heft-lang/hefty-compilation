#!/usr/bin/env sh
set -e
mkdir -p build/
cabal run --verbose=0 hefty-compiler > build/test.s
clang build/test.s runtime.c -o bin/test