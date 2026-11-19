#!/bin/sh
# Compile and run tools/vcomp-check/Main.agda (needs agda and ghc).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=${VCOMP_CHECK_BUILD:-$here/_build}
cd "$here"
LC_ALL=C.UTF-8 agda --no-libraries -i . -i "$root/src" --compile --compile-dir="$out" Main.agda +RTS -M10G -RTS
LC_ALL=C.UTF-8 "$out/Main"
