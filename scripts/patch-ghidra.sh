#!/bin/sh

ROOT=$(realpath "$(dirname "$0")/..")
. "$ROOT/scripts/util.sh"

cd "$GHIDRA_ROOT/Ghidra/Features/Decompiler"
patch -p1 <"$ROOT/scripts/ghidra.patch"
gmake -C src/decompile/cpp -j$(sysctl -n hw.ncpu) ghidra_opt CC=clang CXX=clang++
rm -rf os/null
mkdir os/null
cp src/decompile/cpp/ghidra_opt os/null/decompile
cp os/linux_x86_64/sleigh os/null/sleigh
