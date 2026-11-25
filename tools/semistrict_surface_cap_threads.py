"""Reduce a named scalar probe complement to a movie with only births, deaths and braids.

Input follows semistrict_surface_probe_threads; exactly one port may also be empty.
Treat occurrences with both ports empty as free probes. Output includes the target
movie and an integral free-group change of basis before imposing its cap relators.
"""
from argparse import ArgumentParser
import json
from pathlib import Path
from itertools import permutations,product
from collections import Counter

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import inv,reduced
from semistrict_surface_probe_threads import select_paths
from semistrict_surface_trefoil_mixed import substitute


def complete(data):
    width = data['initial']
    if type(width) is not int or width<0:
        raise ValueError('expected a nonnegative initial width')
    steps = data['steps']
    initial = width+sum(s['input']==0 for s in steps)
    # The dummy unary site gives the first auxiliary approach its own seam.
    positive = [dict(slot=0,input=1,output=1,seam=[])] if initial else []
    kinds = ['pass'] if positive else []
    births,remaining = [],list(range(width,initial))
    total = initial
    for s in steps:
        a,p,q = (s[key] for key in ('slot','input','output'))
        if (any(type(v) is not int for v in (a,p,q)) or min(p,q)<0 or
            p+q==0 or not 0<=a<=width-p):
            raise ValueError('invalid active port; treat a portless site as a free probe')
        if p==0:
            births.append(remaining.pop(0))
            positive[-1]['seam'].extend(-i for i in range(width,a,-1))
        u,v = max(p,1),max(q,1)
        total += v-u
        width += q-p
        seam = s.get('seam',[])
        if any(type(g) is not int or not 1<=abs(g)<width for g in seam):
            raise ValueError('seam crosses outside the real cut')
        # Keep unused initial tails first and completed terminal tails last.
        exit_word = list(range(a+1,total)) if q==0 else []
        positive.append(dict(slot=a,input=u,output=v,seam=exit_word+list(seam)))
        kinds.append('birth' if not p else 'death' if not q else 'pass')
    return dict(initial=initial,steps=positive),kinds,births


def joined(words):
    return reduced(x for w in words for x in w)


def artin(words,g):
    i = abs(g)-1
    a,b = words[i:i+2]
    words[i:i+2] = [reduced(a+b+inv(a)),a] if g>0 else [b,reduced(inv(b)+a+b)]


def resolve_caps(data):
    positive,kinds,birth_edges = complete(data)
    initial,events,paths,packets,_,_ = select_paths(positive)
    # Sort futures lexicographically within each common path prefix.
    bundles = [sorted(pkt,key=paths.__getitem__) for pkt in packets[:initial]]
    expressions = [(i+1,) for i in range(initial)]
    order = [t for block in bundles for t in block]
    physical = [(t+1,) for t in order]
    images = [tuple(t+1 for t in block) for block in bundles]
    active = set(order)-{t for e in birth_edges for t in packets[e]}
    edge_words = {i:(i+1,) for i in range(initial)}
    death_edges,braid,movie = [],[],[]
    start_order = order.copy()

    def move(g):
        sizes = [len(b) for b in bundles]
        for h in cable([g],sizes):
            artin(physical,h)
            j = abs(h)-1
            order[j],order[j+1] = order[j+1],order[j]
            braid.append(h)
        artin(expressions,g)
        i = abs(g)-1
        bundles[i],bundles[i+1] = bundles[i+1],bundles[i]

    def record(before,moves):
        selected = {i for i,t in enumerate(before) if t in active}
        projected = restrict(len(before),moves,selected)
        if projected:
            movie.append(dict(braid=projected))

    for kind,(slot,incoming,outgoing,row,seam) in zip(kinds,events,strict=True):
        before = order.copy()
        left = sum(len(packets[e]) for e in row[:slot])
        live_slot = sum(t in active for t in before[:left])
        if kind=='birth':
            block = packets[incoming[0]]
            movie.append(dict(birth=len(block),slot=live_slot))
            active.update(block)
        mark = len(braid)
        if len(outgoing)>1:
            nonfirst = {t for e in outgoing[1:] for t in packets[e]}
            idx = next(i for i,b in enumerate(bundles) if nonfirst.intersection(b))
            block = bundles[idx]
            assert nonfirst.issubset(block)
            local = {t for e in incoming for t in packets[e]}
            while idx+1<len(bundles) and bundles[idx+1][0] in local:
                move(idx+1)
                idx += 1
            # Put the inherited prefix last. Its children already occur in
            # output-port order. All other prefixes go to the first output.
            children = [[t for t in block if t in packets[e]] for e in outgoing]
            assert all(children) and sum(children,[])==block
            ptr = sum(len(b) for b in bundles[:idx])+len(children[0])
            fresh = []
            for child in children[1:]:
                images.append(joined(physical[ptr:ptr+len(child)]))
                fresh.append((len(images),))
                ptr += len(child)
            parent = expressions[idx]
            expressions[idx:idx+1] = [reduced(parent+inv(joined(fresh))),*fresh]
            bundles[idx:idx+1] = children
        record(before,braid[mark:])
        sizes = []
        j = 0
        for e in row:
            n = len(packets[e])
            start = j
            while n>0:
                n -= len(bundles[j])
                j += 1
            assert n==0 and set(sum(bundles[start:j],[]))==set(packets[e])
            sizes.append(j-start)
            if e in outgoing:
                edge_words[e] = joined(expressions[start:j])
        if kind=='death':
            block = packets[outgoing[0]]
            death_edges.append(outgoing[0])
            movie.append(dict(death=len(block),slot=live_slot))
            active.difference_update(block)
        before,mark = order.copy(),len(braid)
        for g in cable(seam,sizes):
            move(g)
        record(before,braid[mark:])

    assert all(len(b)==1 for b in bundles)
    for g in inv(braid):
        artin(expressions,g)
    inverse = dict(zip(start_order,expressions,strict=True))
    back = [inverse[t] for t in range(len(paths))]
    assert [substitute(w,images) for w in back]==[(i+1,) for i in range(len(paths))]
    assert [substitute(w,back) for w in images]==[(i+1,) for i in range(len(paths))]
    caps = [edge_words[e] for e in birth_edges+death_edges]
    target = [substitute(w,images) for w in caps]
    return dict(rank=len(paths),source_to_thread=images,thread_to_source=back,
                source_cap_words=caps,thread_cap_words=target,
                initial_threads=len(paths)-sum(len(packets[e]) for e in birth_edges),movie=movie)


def s3_count(width,steps):
    """Count homomorphisms from the swept Wirtinger presentation into S3."""
    group = list(permutations(range(3)))
    mul = [[group.index(tuple(a[i] for i in b)) for b in group] for a in group]
    inverses = [r.index(0) for r in mul]
    def peripheral(row):
        value = 0
        for g in row:
            value = mul[value][g]
        return value
    counts = Counter(product(range(6),repeat=width))
    for s in steps:
        slot,p,q = (s[key] for key in ('slot','input','output'))
        new = Counter()
        for row,count in counts.items():
            old = peripheral(row[slot:slot+p])
            if not q and old:
                continue
            for partial in product(range(6),repeat=max(q-1,0)):
                tail = (mul[inverses[peripheral(partial)]][old],) if q else ()
                live = list(row[:slot]+partial+tail+row[slot+p:])
                for g in s.get('seam',[]):
                    i = abs(g)-1
                    a,b = live[i:i+2]
                    live[i:i+2] = ((mul[mul[a][b]][inverses[a]],a) if g>0 else
                                    (b,mul[mul[inverses[b]][a]][b]))
                new[tuple(live)] += count
        counts = new
    return sum(counts.values())


def target_steps(movie):
    for e in movie:
        yield dict(slot=e.get('slot',0),input=e.get('death',0),output=e.get('birth',0),
                   seam=e.get('braid',[]))


def audit():
    from semistrict_surface_shared_edge import braid_image
    count = 0
    ports = [(0,2),(2,0),(2,1),(1,2),(2,2),(1,1)]
    for a,b,c in product(ports,repeat=3):
        width = 2
        steps = []
        for i,(p,q) in enumerate((a,b,c)):
            if p>width:
                break
            slot = (width-p if i%2 else 0)
            width += q-p
            steps.append(dict(slot=slot,input=p,output=q,seam=[(-1)**i] if width>1 else []))
        if len(steps)!=3:
            continue
        r = resolve_caps(dict(initial=2,steps=steps))
        # Independently build the Wirtinger presentation from the cap-only output,
        # putting a temporary meridian into each newly born strand. The cap words
        # can differ by a conjugation from those in the completed braid.
        row = [(i+1,) for i in range(r['initial_threads'])]
        labels = r['initial_threads']
        relators = []
        for event in r['movie']:
            if 'braid' in event:
                row = [substitute(w,row) for w in braid_image(len(row),event['braid'])]
            elif 'birth' in event:
                packet = [(labels+i+1,) for i in range(event['birth'])]
                row[event['slot']:event['slot']] = packet
                labels += len(packet)
                relators.append(joined(packet))
            else:
                slot = event['slot']
                relators.append(joined(row[slot:slot+event['death']]))
                del row[slot:slot+event['death']]
        assert labels==r['rank'] and len(relators)==len(r['source_cap_words'])
        # The exponent sums forget conjugations. Use multisets of strand
        # incidences, up to renumbering (actual starts versus auxiliary starts).
        def incidence(words):
            return sorted(sum(w.count(g)-w.count(-g) for w in words) for g in range(1,labels+1))
        assert incidence(relators)==incidence(r['thread_cap_words'])
        assert s3_count(2,steps)==s3_count(r['initial_threads'],target_steps(r['movie']))
        count += 1
    for twists,total in [(1,6),(2,18),(3,12)]:
        steps = [dict(slot=0,input=0,output=2),dict(slot=2,input=0,output=2,seam=[2]*twists),
                 dict(slot=0,input=2,output=0),dict(slot=0,input=2,output=0)]
        r = resolve_caps(dict(initial=0,steps=steps))
        assert s3_count(0,steps)==s3_count(r['initial_threads'],target_steps(r['movie']))==total
    print(f'{count} signed three-site movies passed both free-group inverse checks, cap-incidence '
          'replay and S3 counts; the unknot, Hopf and trefoil controls gave 6, 18 and 12.')


if __name__=='__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('input',nargs='?',type=Path)
    args = cli.parse_args()
    if args.input:
        print(json.dumps(resolve_caps(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
