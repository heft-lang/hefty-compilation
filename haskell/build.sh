#!/usr/bin/env sh
set -e
cabal build exes
mkdir -p build/
cabal run > build/test.s
as build/test.s -o build/test.o
gcc build/test.o runtime.c -o bin/test