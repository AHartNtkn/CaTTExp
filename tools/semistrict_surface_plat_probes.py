"""Decide a single probe word at the pair births, signed braid and deaths of a plat.

JSON fields: pairs (positive bridge count), braid (signed adjacent exchanges on
2*pairs strands), word (signed meridians of the first strands of birth pairs).
Optional sizes decorate each strand by a point (1) or closed lens (>=2 gates).
The decision returns a finite permutation model or a relation derivation.
"""
import json
from argparse import ArgumentParser
from collections import deque
from itertools import count, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_birth_death_packets import follow
from semistrict_surface_chain_probe import peripheral, transport
from semistrict_surface_component_braids import restrict
from semistrict_surface_exact_boundary import accepted, run
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv, reduced
from semistrict_surface_serial_gate_tracks import push
from semistrict_surface_shared_edge import braid_image


def presentation(pairs, braid):
    if type(pairs) is not int or pairs < 1:
        raise ValueError('expected a positive number of birth pairs')
    if any(type(g) is not int or not 0 < abs(g) < 2*pairs for g in braid):
        raise ValueError('invalid braid generator')
    initial = [(g,) for i in range(1,pairs+1) for g in (i,-i)]
    final = transport(initial,braid)
    return [peripheral(final[i:i+2]) for i in range(0,2*pairs,2)]


def decorated_seam(sizes, braid):
    rows, ports, representatives = [],{},set()
    for i,size in enumerate(sizes):
        if type(size) is not int or size<1:
            raise ValueError('each strand needs a positive number of gates')
        representatives.add(len(rows))
        for j in range(size):
            name = (i,j)
            boundary = ('','')
            if size>1:
                if j==0:
                    boundary = ('','aa')
                elif j==size-1:
                    boundary = ('aa','')
            rows.append((int(0<j<size-1),name))
            ports[name] = boundary
    wide = cable(braid,sizes)
    reached = follow(tuple(rows),wide,ports)
    order = list(range(len(sizes)))
    for g in braid:
        k = abs(g)-1
        order[k:k+2] = reversed(order[k:k+2])
    expected = tuple((int(0<j<sizes[i]-1),(i,j)) for i in order for j in range(sizes[i]))
    assert reached==expected
    small = restrict(len(rows),wide,representatives)
    assert braid_image(len(sizes),small)==braid_image(len(sizes),braid)
    return small,len(wide)


def word_value(word, maps, degree):
    value = list(range(degree))
    for letter in word:
        perm = maps[abs(letter)-1]
        value = [perm[i] if letter>0 else perm.index(i) for i in value]
    return tuple(value)


def models(rank, relations, word):
    for degree in count(2):
        identity = tuple(range(degree))
        for maps in product(permutations(identity),repeat=rank):
            image = word_value(word,maps,degree)
            if image!=identity and all(word_value(r,maps,degree)==identity for r in relations):
                yield dict(raw_filler=False,degree=degree,generators=maps,word_image=image)
            yield None


def rewrites(rank, relations):
    # Cyclic relators and their inverses can be split anywhere. Include both
    # directions for free cancellations, also on words that are not reduced.
    equations = set()
    for g in range(1,rank+1):
        for pair in ((g,-g),(-g,g)):
            equations.update([(pair,()),((),pair)])
    for rel in relations:
        for direction in (rel,inv(rel)):
            for i in range(len(rel)):
                rotation = direction[i:]+direction[:i]
                for j in range(len(rel)+1):
                    equations.add((rotation[:j],inv(rotation[j:])))
    return sorted(equations,key=lambda t:(len(t[1])-len(t[0]),t))


def proofs(rank, relations, word):
    equations = rewrites(rank,relations)
    parent = {word:None}
    queue = deque([word])
    while queue:
        current = queue.popleft()
        for a,b in equations:
            for i in range(len(current)-len(a)+1):
                if current[i:i+len(a)] == a:
                    new = current[:i]+b+current[i+len(a):]
                    if new not in parent:
                        parent[new] = (current,i,a,b)
                        if not new:
                            proof = []
                            while parent[new] is not None:
                                new,pos,old,replacement = parent[new]
                                proof.append([pos,old,replacement])
                            yield dict(raw_filler=True,rewrites=proof[::-1])
                        queue.append(new)
                yield None


def decide(data):
    rank, braid, word = data['pairs'],data['braid'],tuple(data['word'])
    relations = presentation(rank,braid)
    if 'sizes' in data:
        if len(data['sizes'])!=2*rank:
            raise ValueError('give one size for every middle strand')
        projected,_ = decorated_seam(data['sizes'],braid)
        relations = presentation(rank,projected)
    if any(type(g) is not int or not 0<abs(g)<=rank for g in word):
        raise ValueError('meridian outside the birth row')
    word = reduced(word)
    if not word:
        answer = dict(raw_filler=True,rewrites=[])
    else:
        positive = proofs(rank,relations,word)
        negative = models(rank,relations,word)
        while True:
            answer = next(positive,None) or next(negative)
            if answer is not None:
                break
    return dict(relations=relations,reduced_word=word,**answer)


def audit():
    pairs = 2
    comm = (1,2,-1,-2)
    tests = 0
    # Independently compute the death meridian by point-pushing on the full
    # five-strand drawing, then impose the two input cap relations.
    raw_frame = [(i,) for i in range(1,5)]
    birth = [1,-1,2,-2]
    for n in range(-4,5):
        braid = (2 if n>=0 else -2,)*abs(n)
        wide = tuple((abs(i)+1)*(1 if i>0 else -1) for i in braid)
        rels = presentation(pairs,braid)
        for j in range(2):
            death = (2*j+2,2*j+1)
            actual = wide+push(death)+inv(wide)
            read = peripheral(transport(raw_frame,braid)[2*j:2*j+2])
            assert braid_image(5,actual)==braid_image(5,push(read))
            assert reduced(tuple(birth[abs(g)-1]*(1 if g>0 else -1) for g in read))==rels[j]
            tests += 1
    for n,should_fill in [(0,False),(1,True),(2,True),(3,False),(-3,False)]:
        data = dict(pairs=2,braid=[2 if n>0 else -2]*abs(n),word=comm)
        answer = decide(data)
        assert answer['raw_filler']==should_fill
        if should_fill:
            word = comm
            moves = set(rewrites(2,answer['relations']))
            for i,a,b in answer['rewrites']:
                assert (a,b) in moves and word[i:i+len(a)]==a
                word = word[:i]+b+word[i+len(a):]
            assert not word
        else:
            d = answer['degree']
            assert d==3
            maps = answer['generators']
            assert all(word_value(r,maps,d)==tuple(range(d)) for r in answer['relations'])
            assert word_value(comm,maps,d)!=tuple(range(d))
        print(f"middle exponent {n}: {len(answer['rewrites'])} relation steps" if should_fill
              else f"middle exponent {n}: commutator moves sheets by {answer['word_image']}")
    print(f'{tests} independently checked cap words on five strands')
    checks = exchanges = 0
    for length in range(4):
        for braid in product((1,-1,2,-2,3,-3),repeat=length):
            projected,n = decorated_seam([3,1,2,4],braid)
            assert presentation(2,projected)==presentation(2,braid)
            checks += 1
            exchanges += n
    print(f'{checks} decorated seams, {exchanges} positioned exchanges, all cap relations preserved')


def typed(checkout):
    ctx = '(x : *) (a : id(x) -> id(x))'
    rules = ' (b : id(id(x)) -> comp[a,a]) (d : comp[a,a] -> id(id(x))) (s : id(id(x)) -> id(id(x)))'
    text = f"""import examples/eh
def regroup = coh [ [a,b,c,d] : comp[comp[a,b],comp[c,d]] -> comp[a,comp[b,c],d] ]
def ungroup = coh [ [a,b,c,d] : comp[a,comp[b,c],d] -> comp[comp[a,b],comp[c,d]] ]
def crossing {ctx} = comp[a,[eh(x,a,a)],a]
def plat {ctx}{rules} : id(id(x)) -> id(id(x)) =
  comp[s,unitor_l_inv(id(id(x))),comp[[b],[b]],regroup(a,a,a,a),
       crossing(x,a),crossing(x,a),crossing(x,a),ungroup(a,a,a,a),
       comp[[d],[d]],unitor_l(id(id(x)))]
"""
    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory/'examples').symlink_to(checkout.resolve()/'examples',target_is_directory=True)
        (directory/'Plat.catt').write_text(text)
        for flags in ([],['--su'],['--sua']):
            output = run(checkout.resolve()/'target/release/catt_strict',directory,'Plat.catt',flags)
            accepted(output,'Plat.catt',['crossing','plat'])
    print('written four-strand plat with a parked probe checked in raw, --su and --sua')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--rice',type=Path,help='built catt-strict checkout')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(decide(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
        if args.rice:
            typed(args.rice)
