"""Print reachability_theory.py's presentation in the format of DumpSigP.agda."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'e6'))
from reachability_theory import OPERATIONS, EQUATIONS, RULES

def sh(t):
    if isinstance(t, str):
        return t
    return "(" + " ".join([t[0]] + [sh(a) for a in t[1:]]) + ")"

def g(gs):
    return ";".join(sh(l) + "=" + sh(r) for l, r in gs)

out = []
for n, o in OPERATIONS.items():
    out.append(f"OP {n}|{g(o.guards)}|{sh(o.source) if o.source else '?'}|{sh(o.target) if o.target else '?'}")
for s in EQUATIONS:
    out.append(f"EQ {s.name}|{','.join(f'{v}:{d}' for v, d in s.variables)}|{g(s.guards)}|{sh(s.left)}|{sh(s.right)}")
for s in RULES:
    out.append(f"RULE {s.name}|{','.join(f'{v}:{d}' for v, d in s.variables)}|{g(s.guards)}|{sh(s.left)}|{sh(s.right)}")
print("\n".join(out))
