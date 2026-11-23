"""Substitute three connected closed rewrite diagrams into a scalar four-type.

Input JSON has edges, rules (as for semistrict_surface_history_group), root,
bubble (temporal position/name pairs from the empty edge path back to it),
query (two positive three-strand crossing lists), and attachments (such pairs).
"""
import argparse
import json
from itertools import product
from pathlib import Path

from semistrict_surface_braid_reflection import end_vertex, follow
from semistrict_surface_history_group import Presentation, inv
from semistrict_surface_shared_edge import braid_image


def check_connected(data):
    wires, parents = [], []
    root = data['root']
    for i,(pos,name) in enumerate(data['bubble']):
        v,l,r = data['rules'][name]
        path = ''.join(edge for edge,_ in wires)
        if not (0 <= pos <= len(wires) and path.startswith(l,pos) and
                end_vertex(data['edges'],root,path[:pos]) == v and
                end_vertex(data['edges'],v,l) == end_vertex(data['edges'],v,r)):
            raise ValueError('not a legal edge rewrite')
        parents.append(i)
        for _,j in wires[pos:pos+len(l)]:
            while parents[j] != j:
                j = parents[j]
            parents[j] = i
        wires[pos:pos+len(l)] = [(e,i) for e in r]
    if wires or sum(i==p for i,p in enumerate(parents)) != 1:
        raise ValueError('the bubble must be nonempty, connected and have empty boundary')


def block_word(k,w):
    out = []
    for x in w:
        if abs(x) not in (1,2):
            raise ValueError('expected a three-strand crossing')
        offset = (abs(x)-1)*k
        block = tuple(offset+b+a for b in range(k) for a in range(k,0,-1))
        out.extend(block if x>0 else inv(block))
    return tuple(out)


def compile_faces(data):
    check_connected(data)
    h = tuple(tuple(x) for x in data['bubble'])*3
    marks = {x:(l,r) for x,(_,l,r) in data['rules'].items()}
    def faces(pair):
        l,r = (block_word(len(h)//3,w) for w in pair)
        if follow(h,l,marks) != h or follow(h,r,marks) != h:
            raise ValueError('block exchange did not return to the original history')
        return [data['root'],'',h,l,r]
    return dict(edges=data['edges'],rules=data['rules'],query=faces(data['query']),
                attachments=[faces(pair) for pair in data['attachments']])


def forget(k, marks, w):
    selected = [i == j*k+marks[j] for j in range(3) for i in range(j*k,(j+1)*k)]
    out = []
    for letter in w:
        i = abs(letter)-1
        if selected[i] and selected[i+1]:
            out.append((1+sum(selected[:i]))*(1 if letter>0 else -1))
        selected[i],selected[i+1] = selected[i+1],selected[i]
    return tuple(out)


def check_model(data):
    k = len(data['bubble'])
    model = compile_faces(data)
    full = Presentation(model)
    # Verify a B3-valued retraction on the computed presentation, including
    # the cable images of both standard generators. Internal marks may differ.
    rels, sections = 0,0
    for choice in product(range(k),repeat=3):
        images = {g:forget(k,choice,full.braids[g]) for g in full.generators}
        def action(word):
            return braid_image(3,tuple(y for g in word for y in
                                       (images[g] if g>0 else inv(images[-g]))))
        for rel in full.relators:
            assert action(rel) == braid_image(3,())
            rels += 1
        for letter in (1,2):
            other = dict(model)
            other['query'] = [*model['query'][:3],(),block_word(k,(letter,))]
            assert action(Presentation(other).target) == braid_image(3,(letter,))
            sections += 1
    return full.vertices,rels,sections


def semigroup_code(w):
    return tuple(z for a in w for z in (1,1)+(2,)*(2*(a+2))+(1,1))


def promised_semigroup(relations,query):
    """Encode a symmetric semigroup word problem; the surface always answers yes."""
    words = [w for pair in [*relations,query] for w in pair]
    if any(not w or any(a < 0 for a in w) for w in words):
        raise ValueError('use nonempty words on nonnegative integer letters')
    guard = (1,2)*3
    rules = [(semigroup_code(l),semigroup_code(r)) for l,r in relations]
    for a in sorted({a for w in words for a in w}):
        rules.append((guard+semigroup_code((a,)),guard))
    return [(l,r) for p in rules for l,r in (p,p[::-1])],tuple(map(semigroup_code,query))


def checks():
    # One bubble with a birth and a death and no scalar generator.
    data = dict(edges={'f':('v','v')},rules={'u':('v','','f'),'d':('v','f','')},root='v',
                bubble=[(0,'u'),(0,'d')],query=[[],[1]],attachments=[])
    vertices,rels,sections = check_model(data)
    # More complex connected components, including two identical births merging.
    data['rules'].update({'m':('v','ff','f'),'s':('v','f','ff')})
    count = 0
    for b in ([(0,'u'),(0,'s'),(0,'m'),(0,'d')],
              [(0,'u'),(1,'u'),(0,'m'),(0,'d')]):
        data['bubble']=b
        data['attachments']=[[[1,2,1],[2,1,2]]]
        compile_faces(data)
        k = len(b)
        for w in product((1,-1,2,-2),repeat=3):
            cabled = block_word(k,w)
            for choice in product(range(k),repeat=3):
                assert forget(k,choice,cabled) == w
                count += 1
    data['bubble']=[(0,'u'),(0,'d')]
    rules = [((0,1),(1,0))]
    encoded = 0
    for n in range(1,5):
        for w in product(range(2),repeat=n):
            rewrites, query = promised_semigroup(rules,(w,w[::-1]))
            data['query'],data['attachments'] = query,rewrites
            compile_faces(data)
            start = query[0]
            assert not any(start[i:i+3] in ((1,2,1),(2,1,2)) for i in range(len(start)))
            actual = {start[:i]+r+start[i+len(l):] for l,r in rewrites
                      for i in range(len(start)-len(l)+1) if start[i:i+len(l)] == l}
            expected = {semigroup_code(w[:i]+w[i:i+2][::-1]+w[i+2:])
                        for i in range(n-1) if w[i]!=w[i+1]}
            assert actual == expected
            encoded += 1
    print(f'{vertices} birth/death histories, {rels} checked group relations, '
          f'{sections} section images, {count} marked subbraid checks, {encoded} guarded code words')


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',type=Path)
    ap.add_argument('--emit',type=Path)
    args=ap.parse_args()
    if args.input or args.emit:
        if not (args.input and args.emit):
            ap.error('--input and --emit are required together')
        result=compile_faces(json.loads(args.input.read_text()))
        args.emit.write_text(json.dumps(result,indent=2)+'\n')
    else:
        checks()
