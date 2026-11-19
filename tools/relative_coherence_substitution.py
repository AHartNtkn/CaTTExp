"""Check repeated top slots in the substitution theorem of Researcher Response 11."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path

from catt import STAR, arr, check_ctx, comp2, fv_tm, fv_ty, infer, tdim_tm, v
from emit_agda import Emitter
from relative_coherence_strip_fibres import Complex


def triangle_term():
    # Replace p : f => f on a loop f by a triangle with sides h, k and l.
    context = (STAR,)
    x = v(0)

    def declare(source, target):
        nonlocal context
        ty = infer(context, source)
        assert ty == infer(context, target)
        term = v(len(context))
        context += (arr(ty, source, target),)
        return term

    f = declare(x, x)
    a, b, c = (declare(f, f) for _ in range(3))
    h, k, direct = declare(a, b), declare(b, c), declare(a, c)
    triangle = declare(comp2(context, 2, h, k), direct)
    term = comp2(context, 0, comp2(context, 1, triangle, triangle), triangle)
    check_ctx(context)
    assert tdim_tm(context, term) == 4
    support = set(fv_tm(term))
    for i in reversed(range(len(context))):
        if i in support:
            support.update(fv_ty(context[i]))
    assert support == set(range(len(context)))
    return context, term


def compare_serializations():
    # Events h,k or l in each of three slots of (p *_1 p) *_0 p.
    # Reading a slot requires no information from the other two slots.
    def visit(states, word):
        if states == ("c",) * 3:
            yield word
        for i, state in enumerate(states):
            for before, arrow, after in (("a", "h", "b"), ("b", "k", "c"), ("a", "l", "c")):
                if before == state:
                    yield from visit(states[:i] + (after,) + states[i + 1:], word + ((i, arrow),))

    words = set(visit(("a",) * 3, ()))
    remaining = words.copy()
    classes = {}
    while remaining:
        seed = remaining.pop()
        component, pending = {seed}, [seed]
        while pending:
            current = pending.pop()
            for j, (left, right) in enumerate(zip(current, current[1:])):
                if left[0] == right[0]:
                    continue
                exchanged = current[:j] + (right, left) + current[j + 2:]
                assert exchanged in words
                if exchanged in remaining:
                    remaining.remove(exchanged)
                    component.add(exchanged)
                    pending.append(exchanged)
        signatures = {tuple("".join(a for slot, a in word if slot == i) for i in range(3))
                      for word in component}
        assert len(signatures) == 1
        signature = signatures.pop()
        assert signature not in classes
        classes[signature] = len(component)
    assert set(classes) == set(product(("hk", "l"), repeat=3))
    assert classes[("hk",) * 3] == 90
    print(len(words), "serial 3-histories,", len(classes), "classes under adjacent exchange")


def independent_circle_histories(copies):
    # The two-slot hom of the free enriched loop contains two independent
    # copies of the three-lane A,B circuit of Response 3. Distinct names track
    # positions of the same labels in the repeated word.
    rules = {}
    for i in range(copies):
        lane = 3 * i
        left, right = "ABCD"[2 * i:2 * i + 2]
        rules[left] = {lane: ("l", "r"), lane + 1: ("", "")}
        rules[right] = {lane + 1: ("", ""), lane + 2: ("l", "r")}
    model = Complex(("l", "", "l") * copies, ("r", "", "r") * copies, rules)
    assert len(model.components) == 1
    betti = model.betti(model.components[0])
    assert betti == ((1, 1) if copies == 1 else (1, 2, 1))
    print(copies, "slot(s):", dict(sorted(Counter(model.degrees).items())), "Betti", betti)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path)
    args = parser.parse_args()
    ctx, witness = triangle_term()
    if args.agda:
        emitter = Emitter()
        emitter.check_typed("repeated-triangle", ctx, witness)
        args.agda.write_text(emitter.module(args.agda.stem, "Three occurrences of a substituted triangle."))
    compare_serializations()
    for count in (1, 2):
        independent_circle_histories(count)
