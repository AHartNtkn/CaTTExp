"""Check horizontal factorizations and fourth-degree lifts with Rice's bounded checker."""
from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


WIDTH_ONE = ('--insertion-width', '1')
FULL = ('--sua',)
CTX = '(x : *) (f : x -> x) (a : comp[f,f] -> comp[f,f]) (b : id(x) -> id(x))'
HEADS = """
def h [[a],[b]] = comp[[a],[b]]
def hthree [[a],[b],[c]] = comp[[a],[b],[c]]
def hfour [[a],[b],[c],[d]] = comp[[a],[b],[c],[d]]
def flat = coh [ [[a],[b],[c]] : h(h(a,b),c) -> hthree(a,b,c) ]
def unflat = coh [ [[a],[b],[c]] : hthree(a,b,c) -> h(h(a,b),c) ]
def flatthree = coh [ [[a],[b],[c],[d]] : h(hthree(a,b,c),d) -> hfour(a,b,c,d) ]
def otherflat = coh [ [[a],[b],[c],[d]] : hthree(h(a,b),c,d) -> hfour(a,b,c,d) ]
def carry = coh [ {f{a{t}aa}g}{j{b}k} : h(a,b) -> h(aa,b) ]
def carrythree = coh [ {f{a{t}aa}g}{j{b}k}{l{c}m} : hthree(a,b,c) -> hthree(aa,b,c) ]
def route [[a],[b],[c],[d]] = comp[carry(flat(a,b,c),d),flatthree(a,b,c,d)]
def other [[a],[b],[c],[d]] = comp[flat(h(a,b),c,d),otherflat(a,b,c,d)]
def joinrows = coh [ [[a],[b],[c],[d]] : route(a,b,c,d) -> other(a,b,c,d) ]
def splitrows = coh [ [[a],[b],[c],[d]] : other(a,b,c,d) -> route(a,b,c,d) ]
def before {f{a{t}aa}g}{j{b}k}{l{c}m} = comp[flat(a,b,c),carrythree(t,b,c)]
def after {f{a{t}aa}g}{j{b}k}{l{c}m} = comp[carry(carry(t,b),c),flat(aa,b,c)]
def natural = coh [ {f{a{t}aa}g}{j{b}k}{l{c}m} : before(t,b,c) -> after(t,b,c) ]
def threehead [[[a,b]],[[c]]] = comp[[[a,b]],[[c]]]
def sides [[[l]],[[r]]] = comp[[[l]],[[r]]]
def triples [[[l,a,r,s,b,t]],[[u,c,v]]] = threehead(comp[l,a,r],comp[s,b,t],comp[u,c,v])
def around [[[l,a,r,s,b,t]],[[u,c,v]]] = comp[sides(l,u),threehead(comp[a,comp[r,s]],b,c),sides(t,v)]
def rectangle = coh [ [[[l,a,r,s,b,t]],[[u,c,v]]] : triples(l,a,r,s,b,t,u,c,v) -> around(l,a,r,s,b,t,u,c,v) ]
def rectangle_back = coh [ [[[l,a,r,s,b,t]],[[u,c,v]]] : around(l,a,r,s,b,t,u,c,v) -> triples(l,a,r,s,b,t,u,c,v) ]
"""


@cache
def groupings(leaves):
    """All ordered trees with these leaves and at least two children per node."""
    if len(leaves) == 1:
        return leaves
    result = []
    for count in range(1, len(leaves)):
        for cuts in combinations(range(1, len(leaves)), count):
            bounds = (0, *cuts, len(leaves))
            pieces = [groupings(leaves[a:b]) for a, b in zip(bounds, bounds[1:])]
            result.extend(product(*pieces))
    return tuple(result)


def active(tree):
    if isinstance(tree, str):
        return tree != 'f'
    return any(map(active, tree))


def expression(tree):
    if isinstance(tree, str):
        return tree
    entries = [f'[{expression(t)}]' if active(t) else expression(t) for t in tree]
    return 'comp[' + ','.join(entries) + ']'


def reduce_stationary(tree):
    if isinstance(tree, str):
        return tree
    slots = []
    for child in tree:
        word = reduce_stationary(child)
        if isinstance(word, tuple) and not active(word):
            slots.extend(word)
        else:
            slots.append(word)
    return tuple(slots)


def check_fibres(binary, directory):
    count = 0
    distinct = 0
    for leaves in [('a', 'b', 'a', 'b', 'a'), ('f', 'f', 'a', 'f', 'f'),
                   ('b', 'comp[a,a]', 'f', 'f', 'a')]:
        trees = groupings(leaves)
        source = '\n'.join(f'normalise {expression(t)} in {CTX}' for t in trees)
        (directory / 'Forms.catt').write_text(source + '\n')
        for mode in (WIDTH_ONE, FULL):
            output = run(binary, directory, 'Forms.catt', mode)
            accepted(output, 'Forms.catt', [])
            forms = re.findall(r'Normal form:\s*(.*?)\s+has type:', output, re.S)
            expected = [reduce_stationary(t) if mode == WIDTH_ONE else leaves for t in trees]
            pairs = set(zip(expected, forms, strict=True))
            assert len(pairs) == len(set(expected)) == len(set(forms))
            if mode == WIDTH_ONE:
                distinct += len(pairs)
        count += len(trees)
    print(f'{count} horizontal expressions, {distinct} width-one forms, three full forms')


def check_tracks(binary, directory):
    def check_file(filename, definitions, mode, bad=False):
        (directory / filename).write_text('import Heads\n' + '\n'.join(definitions) + '\n')
        names = [line.split()[1] for line in definitions]
        output = run(binary, directory, filename, mode)
        if bad:
            name, = names
            rejected(output, filename, name)
        else:
            accepted(output, filename, names)

    (directory / 'Heads.catt').write_text(HEADS)
    args = '(a,b,id(comp[f,f]),a)'
    source = 'route' + args
    target = 'other' + args
    high = f'{CTX} (z : {target} -> {target})'
    fitted = f'comp[joinrows{args},z,splitrows{args}]'
    direct = f'def direct {high} : {source} -> {source} = z'
    check_file('Fit.catt', [f'def fit {high} : {source} -> {source} = {fitted}'], WIDTH_ONE)
    check_file('Direct.catt', [direct], WIDTH_ONE, bad=True)
    check_file('Direct.catt', [direct], FULL)
    check_file('Class.catt', [
        f'def classfit {high} : {fitted} -> z = id(z)',
        f'def classjoin {CTX} : joinrows{args} -> id({source}) = id(id({source}))',
        f'def classnat {CTX} : natural(flat(a,b,a),a,b) -> id(before(flat(a,b,a),a,b))'
        ' = id(id(before(flat(a,b,a),a,b)))'], FULL)
    check_file('Wrong.catt', [f'def wrong {high} : {fitted} -> id({source}) = id({fitted})'],
               FULL, bad=True)

    base = 'hthree(a,b,a)'
    mid = f'{CTX} (y : {base} -> {base}) (z : {base} -> {base})'
    enter, leave = 'flat(a,b,a)', 'unflat(a,b,a)'
    labels = f'({enter},y,{leave},{enter},z,{leave},{enter},y,{leave})'
    start, end = 'triples' + labels, 'around' + labels
    ext = f'{mid} (e : {end} -> {end})'
    fitted = f'comp[rectangle{labels},e,rectangle_back{labels}]'
    check_file('Rect.catt', [
        f'def rect {mid} : {start} -> {end} = rectangle{labels}',
        f'def fitrect {ext} : {start} -> {start} = {fitted}'], WIDTH_ONE)
    check_file('RectClass.catt', [
        f'def rectclass {mid} : rectangle{labels} -> id(threehead(y,z,y)) = id(rectangle{labels})',
        f'def fittedclass {ext} : {fitted} -> e = id(e)'], FULL)
    print('Checked row contraction, naturality, shared-seam rectangle and both lifted classes')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    binary = parser.parse_args().binary.resolve()
    with TemporaryDirectory() as temp:
        directory = Path(temp)
        check_fibres(binary, directory)
        check_tracks(binary, directory)
