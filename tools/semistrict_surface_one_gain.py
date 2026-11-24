"""Decide whether a directed degree-four comparison can use a single polygon prism."""
from argparse import ArgumentParser
from collections import defaultdict, deque
import json
from pathlib import Path
from random import Random

from semistrict_surface_polygon_windings import exchange, prism
from semistrict_surface_raw_movie_graph import raw_updates, read, steps
from semistrict_surface_signed_width_two import Movies, Presentation, Rule
from semistrict_surface_stationary_polygons import decide as stationary


def positive_steps(model, source, word):
    histories, windows = read(model, source, word)
    for v in raw_updates(model, word, histories, windows, len(word)):
        strict_swap = exchange(word, v, windows)
        yield v, strict_swap is None and prism(word, v) is not None
    for j, (p, k) in enumerate(word[:-2]):
        if p == 'swap' and k and word[j:j+3] == steps((k,k-1,k)):
            yield word[:j]+steps((k-1,k,k-1))+word[j+3:], False


def gain_options(model, source, first, second):
    """Newly preceding unit names must partition into entire live spectator wires."""
    from semistrict_surface_polygon_grades import resolution
    from semistrict_surface_transfer_cables import cables
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    widths, flow, graph, readings = resolution(source,(first,second),arities,'swap')
    units = cables(list(flow),graph,graph)
    def before(reading):
        wires = [(-1,i) for i in range(len(widths))]
        cuts = {}
        for i,p in reading:
            if p is None:
                wires[i:i+2] = reversed(wires[i:i+2])
            else:
                _, ins, outs = graph[p]
                cuts[p] = {u for e in wires[:i] for u in units[e]}
                wires[i:i+len(ins)] = outs
        return cuts
    a,b = map(before,readings)
    if any(not a[p] <= b[p] for p in a):
        return False, False
    ancestors = {}
    consumer = {}
    for p,(_,ins,_) in graph.items():
        past = {q for q,_ in ins if q != -1}
        ancestors[p] = past.union(*(ancestors[q] for q in past))
        consumer.update((e,p) for e in ins)
    changed = [p for p in a if a[p] != b[p]]
    singleton = len(changed) == 1
    multiple = len(changed) > 1
    for p in changed:
        gain = b[p]-a[p]
        choices = []
        for e, names in units.items():
            q = e[0]
            t = consumer.get(e)
            if q == p or p in ancestors.get(q,()) or t == p or t in ancestors[p]:
                continue
            bundle = set(names)
            if bundle <= gain:
                choices.append(bundle)
        if set().union(*choices) != gain:
            return False, False
        singleton = singleton and gain in choices
        multiple = multiple or set().union(*(u for u in choices if u != gain)) == gain
    return singleton, multiple


def decide(model, source, first, second, initial=None, forced_only=False):
    first, second = tuple(map(tuple, first)), tuple(map(tuple, second))
    result = stationary(model, source, first, second) if initial is None else initial
    if result['surface'] is not None:
        return dict(result, single_prism=False)
    singleton, multiple = gain_options(model, source, first, second)
    if not singleton:
        return dict(result, single_prism=False, surface=None if multiple else False)
    if multiple and forced_only:
        return result
    todo = deque([first])
    seen, tried = {first}, set()
    while todo:
        w = todo.popleft()
        for v, gain in positive_steps(model, source, w):
            if gain:
                if v not in tried and stationary(model, source, v, second)['mutual']:
                    return dict(surface=True, mutual=False, single_prism=True, before_prism=w, after_prism=v,
                                stationary_readings=len(seen))
                tried.add(v)
            elif v not in seen:
                seen.add(v)
                todo.append(v)
    return dict(surface=None if multiple else False, mutual=False, single_prism=False,
                stationary_readings=len(seen),
                prism_targets=len(tried), obstruction='no exposed positive prism with these stationary ends')


def checks():
    from semistrict_surface_raw_movie_graph import raw_compare
    from semistrict_surface_stationary_polygons import reversible_class
    s = ((0,'s'),)
    bubble = ((0,'b'), (0,'d'))
    ports = {'s': ('',''), 'b': ('','f'), 'd': ('f','')}
    def presentation(window):
        rules = [Rule(window, s, bubble), Rule(window, bubble, s)]
        return Movies(Presentation({'f': (0,0)}, ports, rules, {'s':0,'b':0}), window)
    model = presentation('')
    source = s*4
    w = steps((1,0,1))+((0,3),('swap',0),(0,0))
    v = steps((0,1,0))+((0,1),('swap',0),('swap',1),(0,4))
    yes = decide(model, source, w, v)
    assert yes['surface'] and not raw_compare(model, source, w, v)['raw']
    assert yes['before_prism'] in reversible_class(model, source, w)
    assert v in reversible_class(model, source, yes['after_prism'])
    assert (yes['after_prism'],True) in positive_steps(model, source, yes['before_prism'])
    padded = presentation('f')
    no = decide(padded, source, w, v)
    assert no['surface'] is False and no['prism_targets'] >= 0
    rng = Random(21)
    hits = checked = 0
    for model in (model, padded):
        # Compute the whole finite positive graph from each sample, including
        # paths with multiple gains, without consulting cuts to choose steps.
        grouped = defaultdict(set)
        for _ in range(550):
            h, word = source, ()
            for _ in range(rng.randrange(2,6)):
                allowed = [(('swap',i), model.swap(h,i,True)) for i in range(len(h)-1)]
                allowed.extend(((p,i), r[0]) for i in range(len(h)) for p in (0,1)
                               if (r := model.named(h,p,i)) is not None)
                op, h = rng.choice([(op,t) for op,t in allowed if t is not None])
                word += (op,)
            grouped[h].add(word)
        for group in grouped.values():
            words = sorted(group, key=repr)
            for first in words[::17]:
                reachable = {first}
                queue = deque([first])
                while queue:
                    for nxt, _ in positive_steps(model,source,queue.popleft()):
                        if nxt not in reachable:
                            reachable.add(nxt)
                            queue.append(nxt)
                others = set(rng.sample(words,min(6,len(words)))) | set(sorted(reachable,key=repr)[::3])
                for target in others:
                    grade = stationary(model,source,first,target)
                    if grade.get('temporal_gain') == 1:
                        assert decide(model,source,first,target,grade)['surface'] == (target in reachable)
                        hits += target in reachable
                        checked += 1
    # This gained spectator has several units, since a later merge uses it
    # together with P's output. Its descendants cannot be spectators at P.
    scalar = Movies(Presentation({}, {'s':('','')}, [Rule('',s,s), Rule('',s*2,s*3)],
                                 {'s':0}), '')
    w = ((0,0),('swap',0),(1,0))
    v = (('swap',0),(0,1),(1,0))
    weight = stationary(scalar,s*2,w,v)['temporal_gain']
    assert weight > 1 and gain_options(scalar,s*2,w,v) == (True,False)
    assert decide(scalar,s*2,w,v)['single_prism']
    a = ((0,0),('swap',0),('swap',1))
    b = (('swap',0),('swap',1),(0,2))
    assert gain_options(scalar,s*3,a,b) == (False,True)
    assert decide(scalar,s*3,a,b)['single_prism'] is False and raw_compare(scalar,s*3,a,b)['raw']
    # Compare one-polygon transfers with the independent signed packet solver,
    # adding identical positive winding and varying both exterior windows.
    from semistrict_surface_single_polygon import decide as signed
    signed_tests = 0
    single = ((0,0),('swap',1),('swap',0))
    shifted = (('swap',0),(0,1))
    for model in (presentation(''),padded):
        for a,b in ((single,shifted), ((('swap',0),(0,0)), ((0,1),('swap',0),('swap',1)))):
            for before in ((), steps((0,0)), steps((1,1)), steps((0,1,0))):
                for after in ((), steps((3,3))):
                    x,y = before+a+after, before+b+after
                    expected = signed(model,source,x,y,radius=4)['surface']
                    assert expected is not None and decide(model,source,x,y)['surface'] == expected
                    signed_tests += 1
    return dict(one_gain_checks=checked, positives=hits, exposed_prism_verified=True,
                padded_negative=no['stationary_readings'], forced_spectator_weight=weight,
                signed_comparisons=signed_tests)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--query', type=Path)
    args = parser.parse_args()
    if args.query:
        q = json.loads(args.query.read_text())
        if q.get('attachments'):
            raise ValueError('expected a 3-computad')
        rules = [Rule(r['path'],tuple(map(tuple,r['source'])),tuple(map(tuple,r['target'])))
                 for r in q['rules']]
        model = Movies(Presentation(q['edges'],q['marks'],rules,q.get('mark_roots')),q['start'])
        source = tuple(map(tuple,q['source']))
        model.pres.walk(model.start,source,q.get('vertex'))
        answer = decide(model,source,q['first'],q['second'])
    else:
        answer = checks()
    print(json.dumps(answer))
