"""Produce and replay positive certificates for all-boundary mixed Gray reflection.

--cover accepts {"universe":[...],"subsets":[[...],...]} and emits the Gray
presentation for the EXACT COVER reduction. --verify replays a certificate
associated to --presentation without running integer feasibility.
"""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from pathlib import Path

from semistrict_surface_joint_labels import Catalogue, GapWords, positive_normal
from semistrict_surface_scalar_sites import coefficients


class Certificate(Catalogue):
    def __init__(self,data,proof=None):
        super().__init__(data)
        self.proof = proof
        self.log = []

    def accepts(self,v,path,h,delta):
        rows = sorted(self.rows(v,path,h))
        target = tuple(x for row in delta for x in row)
        if self.proof is None:
            result = coefficients(rows,target)
        else:
            i = len(self.log)
            if i>=len(self.proof):
                raise ValueError('incomplete certificate')
            result = self.proof[i]
            if result is not None:
                if not isinstance(result,list) or len(result)!=len(rows) or any(type(k)!=int or k<0 for k in result):
                    raise ValueError('invalid nonnegative coefficient vector')
                if any(sum(k*row[j] for k,row in zip(result,rows))!=x for j,x in enumerate(target)):
                    raise ValueError('coefficient vector does not give the required increment')
        self.log.append(result)
        return result is not None

    def run(self):
        result = self.solve()
        if self.proof is not None:
            if not result['reflects'] or len(self.log)!=len(self.proof):
                raise ValueError('certificate does not establish reflection at every boundary')
            return dict(verified=True,queries=len(self.log))
        if result['reflects']:
            result['memberships']=self.log
        return result


def cover(data):
    universe = list(data['universe'])
    names = {x:f'd{i}' for i,x in enumerate(universe)}
    if len(names)!=len(universe):
        raise ValueError('universe has repeated elements')
    def updates(xs):
        return [[names[x],0,1] for x in xs]
    def rule(n,a,b):
        return ['v','',[(0,'s')]*n,a,b]
    atoms = []
    for s in data['subsets']:
        if len(s)!=len(set(s)) or any(x not in names for x in s):
            raise ValueError('not a subset of the supplied universe')
        atoms.append(rule(1,[],updates(s)))
    atoms.extend([rule(2,[1],updates(universe)+[1]),rule(3,[2,1,2],[1,2,1])])
    return dict(edges={},rules={'s':['v','','']},unary={s:['s','s'] for s in names.values()},
                commutations=list(combinations(names.values(),2)),attachments=atoms)


def checks():
    from random import Random
    rng=Random(173)
    cases=good=certified=0
    for n in range(1,7):
        u=list(range(n))
        for _ in range(20):
            subsets=[rng.sample(u,rng.randint(1,n)) for _ in range(rng.randrange(8))]
            counts={0}
            for s in subsets:
                mask=sum(1<<i for i in s)
                counts.update([m|mask for m in counts if not m&mask])
            expected=(1<<n)-1 in counts
            data=cover(dict(universe=u,subsets=subsets))
            result=Certificate(data).run()
            assert result['reflects']==expected
            if expected:
                verified=Certificate(data,result['memberships']).run()
                certified+=verified['queries']
                good+=1
            cases+=1
    # Compare the streaming signature with its literal definition.
    words=['abbbab','abbba','bbbaba']
    m=GapWords({e:('v','v') for e in 'ab'},words)
    probed=0
    def state(w):
        sig=('',True,'')
        for e in w:
            sig=m.step(sig,e)
        return sig
    for k in range(11):
        for letters in product('ab',repeat=k):
            w=''.join(letters)
            p=max((t for t in m.substrings if w.startswith(t)),key=len)
            s=max((t for t in m.substrings if w.endswith(t)),key=len)
            assert state(w)==(p,w in m.substrings,s)
            probed+=1
    reps=m.paths('v','v')
    assert len({state(w) for w in reps})==len(reps)
    # Many binary loop words; the dictionary inspects only runs of a.
    sparse=GapWords({'a':('v','v'),'b':('v','v')},['a'*12])
    reduced=len(sparse.paths('v','v'))
    assert reduced==181
    data=cover(dict(universe=['a'],subsets=[['a']]))
    true=Certificate(data).run()['memberships']
    broken=[list(row) if row is not None else None for row in true]
    k=next(i for i,row in enumerate(broken) if row and any(row))
    broken[k]=[0]*len(broken[k])
    try:
        Certificate(data,broken).run()
    except ValueError:
        pass
    else:
        raise AssertionError('accepted a false membership')
    from semistrict_surface_shared_edge import braid_image
    nf_to_artin, artin_to_nf = {}, {}
    spellings = 0
    for length in range(8):
        for w in product((1,2,3),repeat=length):
            nf, artin = positive_normal(4,w), braid_image(4,w)
            assert nf_to_artin.setdefault(nf,artin)==artin and artin_to_nf.setdefault(artin,nf)==nf
            spellings+=1
    print(f'{cases} exact-cover instances agree with independent subset search ({good} positive); '
          f'{certified} membership records replayed. {probed} literal word signatures checked. '
          f'The length-12 unary guard on a binary graph has {reduced} nonempty gap classes. '
          f'{spellings} positive braid spellings agree with the Artin action.')


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--presentation',type=Path)
    group.add_argument('--cover',type=Path)
    parser.add_argument('--verify',type=Path)
    args=parser.parse_args()
    if args.verify and not args.presentation:
        parser.error('--verify requires --presentation')
    if args.cover:
        print(json.dumps(cover(json.loads(args.cover.read_text()))))
    elif args.presentation:
        proof=json.loads(args.verify.read_text())['memberships'] if args.verify else None
        if args.verify and not isinstance(proof,list):
            parser.error('verification requires a list of membership records')
        print(json.dumps(Certificate(json.loads(args.presentation.read_text()),proof).run()))
    else:
        checks()
