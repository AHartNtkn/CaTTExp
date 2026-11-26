#!/usr/bin/env python3
"""Sharing-aware certificate that the Horiz3 cone context is well formed.

Usage: python3 tools/dag_horiz3_cone.py CONE_CTX.pkl OUTDIR
       python3 tools/dag_horiz3_cone.py --test TABLE.pkl I OUTDIR

The second form writes the small test DagCtxSmall: the context of answer
I of the answer table (horiz3-table-25.pkl) extended by its query type
t → u (I = 8 for the committed test).

CONE_CTX.pkl is the 31-entry cone context over ConeShapesThree.Horiz3, a
pickled list of catt-format types, as computed by tools/cone_rcs.py from
the 25-entry answer table (the cone thread keeps it as
horiz3-cone-ctx.pkl in the project files). Writes
CaTTExp.Generated.DagHoriz3Cone{Check,Data,QTable} and their part modules
under OUTDIR; DagHoriz3ConeCheck proves `queryCtxOf queryS qCtx ⊢ctx`
(Dag.Sound.certifiedCtxQ). About 1.13M items, 150 MB of data, so not
committed; checking it takes about 130 min and 12 GB (+RTS -M12G).
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(1000000)

import dag_cert  # noqa: E402


def main():
    if sys.argv[1] == '--test':
        import catt
        ans, _ = pickle.load(open(sys.argv[2], 'rb'))
        G, A, t, u, _ = ans[int(sys.argv[3])]
        print(dag_cert.emit_ctx_all('DagCtxSmall', list(G) + [catt.arr(A, t, u)], sys.argv[4])[1])
        return
    K = pickle.load(open(sys.argv[1], 'rb'))
    _, st = dag_cert.emit_ctx_all('DagHoriz3Cone', K, sys.argv[2])
    print(st)


if __name__ == '__main__':
    main()
