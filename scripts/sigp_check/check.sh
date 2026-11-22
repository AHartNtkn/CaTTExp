#!/bin/sh
# Compare Uniform/SigP.agda with scripts/e6/reachability_theory.py term by term.
# The s_n/t_n operations have no stated boundary in the Python; their
# boundary fields are masked. Exits non-zero on any difference.
set -e
cd "$(dirname "$0")"
LC_ALL=C.UTF-8 agda --no-libraries -i . -i ../../src --compile --compile-dir=build DumpSigP.agda >/dev/null
./build/DumpSigP > agda.txt
python3 dump_py.py > py.txt
mask() { sed 's/^\(OP [st][0-9]*|\)|[^|]*|.*/\1|/' "$1"; }
mask py.txt > py.masked; mask agda.txt > agda.masked
diff py.masked agda.masked && echo "SigP matches reachability_theory.py: $(wc -l < py.txt) operations, equations and rules"
