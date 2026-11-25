#!/usr/bin/env python3
"""Sharing-aware certificate for the answer to Horiz3 query (2).

Usage: python3 tools/dag_horiz3_q2.py ANSWER.pkl OUTDIR [N PREFIX]

With N and PREFIX, certify instead a subterm of the answer whose DAG has
at most N nodes (descending into the largest argument), as module
CaTTExp.Generated.PREFIX{Data,QTable,Check}: a test of the same pipeline
at a smaller size. N = 20000 gives the 18,794-item test of
notes/dag-certificates.md.

ANSWER.pkl is the relative-coherence answer w to the query in
tools/fixtures/rc_horiz3_query2.txt.gz (a pickled catt term; the cone
thread keeps it as rc_query2_answer.pkl in the project files). The
answer is re-checked by catt.infer in Python before anything is emitted,
then written as CaTTExp.Generated.DagHoriz3Q2{Data,QTable,Check} under
OUTDIR (notes/dag-certificates.md). The data is about 82 MB, so it is
not committed; checking DagHoriz3Q2Check takes about 75 min and 4 GB.
"""
import ast
import gzip
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(1000000)

import catt  # noqa: E402
import dag_cert  # noqa: E402


def main():
    ans, outdir = sys.argv[1], sys.argv[2]
    sub = (int(sys.argv[3]), sys.argv[4]) if len(sys.argv) > 4 else None
    G, A, t, u = ast.literal_eval(
        gzip.open(os.path.join(HERE, 'fixtures', 'rc_horiz3_query2.txt.gz'), 'rt').read())
    w = catt.hc(pickle.load(open(ans, 'rb')), {})
    ty = catt.arr(A, t, u)
    t0 = time.time()
    if catt.infer(G, w) != ty:
        sys.exit('the answer does not have the query type')
    print('Python re-check: %.0f s' % (time.time() - t0))
    if sub:
        w = subterm(w, sub[0])
        ty = catt.infer(G, w)
        _, st = dag_cert.emit_all(sub[1], G, ty, w, outdir, tree_query=sub[0] <= 1000)
    else:
        _, st = dag_cert.emit_all('DagHoriz3Q2', G, ty, w, outdir, tree_query=False)
    print(st)


def dag_size(x):
    seen, st = set(), [x]
    while st:
        y = st.pop()
        if y[0] == 'v' or id(y) in seen:
            continue
        seen.add(id(y))
        st.extend(y[3])
    return len(seen)


def subterm(x, n):
    while dag_size(x) > n:
        x = max((a for a in x[3] if a[0] == 'coh'), key=dag_size)
    return x


if __name__ == '__main__':
    main()
