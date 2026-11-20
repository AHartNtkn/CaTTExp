"""Check the face erasures and geometric carriers used in Researcher Response 9."""
from functools import cache, reduce
from itertools import product

from catt import check_ctx, comp2, infer, subst_tm, v
from relative_coherence_spherical_fibres import catt_context, ring
from relative_coherence_strip_fibres import Complex, events


def check_syntax(k):
    original, _, rows = catt_context(k)
    seams = rows[1::2]
    colours = tuple(v(len(original) + i) for i in range(k))
    coloured = original + tuple(infer(original, row["d"]) for row in seams)
    check_ctx(coloured)

    def horizontal(terms):
        if len(terms) == 1:
            return terms[0]
        cut = len(terms) // 2
        return comp2(coloured, 0, horizontal(terms[:cut]), horizontal(terms[cut:]))

    @cache
    def ends(face):
        result = []
        for final in (False, True):
            lanes = []
            for j, row in enumerate(rows):
                word = [row["t"]] if "t" in row else []
                if j % 2:
                    i = j // 2
                    left = colours[i] if face[i] == -1 else row["p"]
                    right = colours[i] if face[i] == 1 else row["p"]
                    word.extend([right, row["e"], left] if final else [left, row["d"], right])
                else:
                    word.append(row["r" if final else "l"])
                lanes.append(reduce(lambda x, y: comp2(coloured, 1, x, y), word))
            result.append(horizontal(lanes))
        assert infer(coloured, result[0]) == infer(coloured, result[1])
        return tuple(result)

    checks = 0
    for i, row in enumerate(seams):
        sigma = tuple(row["p"] if j == colours[i][1] else v(j) for j in range(len(coloured)))
        for face in product((-1, 0, 1), repeat=k):
            if face[i]:
                larger = face[:i] + (0,) + face[i + 1:]
                assert tuple(subst_tm(t, sigma) for t in ends(face)) == ends(larger)
                checks += 1
    print(k, "seams:", checks, "face inclusions preserve both literal CaTT endpoints")


def visible(cell, k, *, require_visible=True):
    signs = []
    for i in range(k):
        a, b = chr(65 + 2 * i), chr(66 + 2 * i)
        lane = 2 * i + 1
        ta = next(j for j, tier in enumerate(cell) if a in events(tier))
        tb = next(j for j, tier in enumerate(cell) if b in events(tier))
        if ta < tb:
            signs.append(0)
        elif ta == tb:
            word = cell[ta][lane]
            signs.append(1 if word.index(a) < word.index(b) else -1)
        else:
            word = cell[tb][lane]
            signs.append(1 if word.index("d") < word.index(b) else -1)
    if require_visible:
        assert any(signs)
    return tuple(signs)


def check_geometry(k):
    initial, final, rules, typed = ring(k)
    base = Complex(initial, final, rules, typed)
    data = [visible(cell, k) for cell in base.cells]
    for i, boundary in enumerate(base.facets):
        for j in boundary:
            assert all(y == 0 or x == y for x, y in zip(data[i], data[j]))
    # A fresh h is another endomorphism of p on each frozen seam.
    for face in product((-1, 0, 1), repeat=k):
        if not any(face):
            continue
        start, finish = list(initial), list(final)
        for i, sign in enumerate(face):
            if sign:
                j = 2 * i + 1
                start[j] = "thd" if sign < 0 else "tdh"
                finish[j] = "teh" if sign < 0 else "the"

        def typed_with_h(tier):
            return typed(tuple(word.replace("h", "d") for word in tier))

        coloured = Complex(tuple(start), tuple(finish), rules, typed_with_h)
        images = [tuple(tuple(w.replace("h", "") for w in tier) for tier in cell)
                  for cell in coloured.cells]
        expected = {cell for cell, signs in zip(base.cells, data)
                    if all(not x or not y or x == y for x, y in zip(signs, face))}
        assert len(images) == len(expected) and set(images) == expected
        image_indices = [base.index[cell] for cell in images]
        for j, facets in enumerate(coloured.facets):
            assert sorted(image_indices[f] for f in facets) == sorted(base.facets[image_indices[j]])
        assert len(coloured.components) == 1 and coloured.betti(coloured.components[0]) == (1,)
    print(k, "seams: exact coloured subcomplexes and reversed cube-face map verified")


if __name__ == "__main__":
    check_syntax(4)
    check_geometry(2)
    check_geometry(3)
