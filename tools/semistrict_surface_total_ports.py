"""Two-column comparisons with arbitrary positive shared rules and left-private prisms."""
from argparse import ArgumentParser
from collections import defaultdict
import json
from pathlib import Path

from semistrict_surface_planar_cylinder import parse


def incidence(source,right,trace,ids):
    wires=[(-1,i) for i in range(len(source))]
    sides={e:int(x in right) for e,x in zip(wires,source)}
    graph={}
    words=defaultdict(list)
    for n,i,l,r in trace:
        ins=tuple(wires[i:i+len(l)])
        if n=='swap':
            f,e=ins
            words[e].append(f)
            words[f].append(e)
            wires[i:i+2]=[e,f]
        else:
            p=ids.setdefault((n,ins),len(ids))
            out=tuple((p,j) for j in range(len(r)))
            sides.update((e,int(x in right)) for e,x in zip(out,r))
            graph[p]=n,ins,out
            wires[i:i+len(l)]=out
    return wires,sides,graph,words


def compare(source,right,traces,anchored):
    ids={}
    a,b=[incidence(source,right,path,ids) for path in traces]
    if a[:3]!=b[:3]:
        return None
    _,sides,graph,now=a
    target=b[3]
    steps=[]
    for p,(name,all_in,all_out) in sorted(graph.items()):
        ins=[e for e in all_in if sides[e]==0]
        out=[e for e in all_out if sides[e]==0]
        private=(len(ins)==len(all_in) and len(out)==len(all_out) and name not in anchored)
        tail=None
        for e in ins:
            fixed=target.get(e,[])
            if now[e][:len(fixed)]!=fixed:
                return None
            more=now[e][len(fixed):]
            if tail is not None and more!=tail:
                return None
            tail=more
        if not private:
            if tail:
                return None
            continue
        for f in reversed(tail):
            for e in ins:
                assert now[e].pop()==f
            for e in out:
                assert f not in now[e]
                now[e].insert(0,f)
            i=now[f].index(ins[0])
            assert now[f][i:i+len(ins)]==ins
            now[f][i:i+len(ins)]=out
            steps.append((p,f))
    return steps if all(now[e]==target.get(e,[]) for e in sides) else None


def checks():
    from semistrict_surface_wire_words import exhaustive
    cases=[('BM',[('born','B','ax'),('unborn','ax','B'),('p','a','aa'),('rev','aM','Ma')],4,()),
           ('aB',[('die','a','M'),('born','B','xx'),('p','x','x'),('return','xM','Mx')],4,()),
           ('BM',[('left-birth','B','Ba'),('sink','a','B'),('split','a','xy'),('pin','M','M')],4,()),
           ('Baa',[('p','aa','xy'),('birth','B','aB'),('death','x','M'),('join','yM','B')],3,()),
           ('BB',[('birth','B','a'),('p','a','xy'),('right-only','B','BM'),('break','a','B')],4,()),
           ('Baa',[('update','a','a'),('gate','aB','Ba'),('new','B','Ma')],3,())]
    total=[0,0,0]
    for w,r,n,fixed in cases:
        value=exhaustive(tuple(w),[(k,tuple(l),tuple(t)) for k,l,t in r],set('BM'),n,fixed,solver=compare)
        total=[x+y for x,y in zip(total,value)]
    return dict(zip(('readings','comparisons','prism_diamonds'),total))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--query',type=Path)
    parser.add_argument('--agda-dir',type=Path)
    args=parser.parse_args()
    if args.query:
        q=json.loads(args.query.read_text())
        source,right=tuple(q['source']),set(q['right_letters'])
        rules=[(n,tuple(l),tuple(r)) for n,(l,r) in q['rules'].items()]
        anchored=set(q.get('anchored',()))
        if any(n=='swap' or not l or not r for n,l,r in rules):
            raise ValueError('rule sides must be nonempty')
        if not anchored<={n for n,l,r in rules if not right.intersection(l+r)}:
            raise ValueError('only left-only rules need an explicit anchored designation')
        w,u=parse(source,rules,right,q['first'])
        vword,v=parse(source,rules,right,q['second'])
        if w!=vword:
            raise ValueError('expected parallel readings')
        cert=compare(source,right,(u,v),anchored)
        result=dict(raw=cert is not None,surface=cert is not None,prisms=cert)
    else:
        result=checks()
    if args.agda_dir:
        from semistrict_surface_wire_words import agda_example
        agda_example(args.agda_dir,transfers=True)
    print(json.dumps(result))
