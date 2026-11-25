"""Degree-six cut words for independent rules on rank-three scalars.

JSON: ports lists [input size,output size] per event, through is a count.
A word entry gives after (zero-based fired events), pair (two [column,tip]
addresses), and optional signed multiple. Through i has column -1-i, tip 0.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import count, product
from pathlib import Path
import json


def add(vector,key,amount):
    vector[key] += amount
    if not vector[key]:
        del vector[key]


def push(normal,side,vector):
    if not vector:
        return
    if normal and normal[-1][0]==side:
        target = normal[-1][1]
        for key,value in vector.items():
            add(target,key,value)
        if not target:
            normal.pop()
    else:
        normal.append((side,vector.copy()))


def modes(column,side,i,ports):
    if column<0:
        return [((column,-1,0),1)]
    size = ports[column][side]
    if i+1<size:
        return [((column,side,i),1)]
    other = ports[column][1-side]
    total = [((column,-1,0),1)] if other else []
    return total+[((column,side,k),-1) for k in range(size-1)]


def normal_form(ports,through,word):
    if type(through) is not int or through<0 or any(len(p)!=2 or any(type(q) is not int or q<0 for q in p) for p in ports):
        raise ValueError('expected nonnegative through and port sizes')
    centre = Counter()
    factors = defaultdict(list)
    for entry in word:
        after = set(entry['after'])
        if not after<=set(range(len(ports))):
            raise ValueError('unknown fired event')
        addresses = [tuple(a) for a in entry['pair']]
        if len(addresses)!=2 or addresses[0]==addresses[1]:
            raise ValueError('expected two distinct live tips')
        for col,i in addresses:
            if not -through<=col<len(ports) or not 0<=i<(1 if col<0 else ports[col][int(col in after)]):
                raise ValueError('tip is absent at this cut')
        mult = entry.get('multiple',1)
        if type(mult) is not int:
            raise ValueError('expected integral pair multiplicity')
        if addresses[0]>addresses[1]:
            addresses.reverse()
            mult = -mult
        (a,i),(b,j) = addresses
        s,t = int(a in after),int(b in after)
        if a==b:
            add(centre,((a,s,i),(b,s,j)),mult)
            continue
        vector = Counter()
        for x,v in modes(a,s,i,ports):
            for y,w in modes(b,t,j,ports):
                active = x[1]>=0 and y[1]>=0 and s!=t and min(*ports[a],*ports[b])>=2
                if active:
                    add(vector,(x,y),v*w*mult)
                else:
                    add(centre,(x,y),v*w*mult)
        if vector:
            push(factors[a,b],s,vector)
    return dict(central=sorted(centre.items()), mixed=[
        dict(events=list(key),syllables=[(side,sorted(v.items())) for side,v in normal])
        for key,normal in sorted(factors.items()) if normal])


def inverse(word):
    return [dict(term,multiple=-term.get('multiple',1)) for term in reversed(word)]


def bracket(x,y):
    return x+y+inverse(x)+inverse(y)


def brunnian(d):
    def pair(side,i):
        return [dict(after=[side],pair=[[0,i],[1,i]])]
    w = bracket(pair(0,0),pair(1,0))
    for i in range(1,d):
        for side in (0,1):
            w = bracket(w,pair(side,i))
    return w


def prescribed(d,bound):
    """One nonidentity root in the normal closure of every shortlisted word."""
    ports = [[d,d],[d,d]]
    def key(w):
        # Every generator here uses two nonanchor tips at a mixed cut.
        factors = normal_form(ports,0,w)['mixed']
        return repr(factors) if factors else ''
    basis = [dict(after=[side],pair=[[0,i],[1,j]]) for side,i,j in product(range(2),range(d-1),range(d-1))]
    alphabet = basis+inverse(basis)
    words = {}
    for length in range(1,bound+1):
        for seq in product(alphabet,repeat=length):
            k = key(seq)
            if k:
                words.setdefault(k,list(seq))
    leaves = [brunnian(d),*words.values()]
    def combine(u,v):
        for length in count():
            for seq in product(alphabet,repeat=length):
                z = list(seq)
                candidate = bracket(u,z+v+inverse(z))
                if key(candidate):
                    return candidate
    while len(leaves)>1:
        leaves = [combine(leaves[i],leaves[i+1]) if i+1<len(leaves) else leaves[i]
                  for i in range(0,len(leaves),2)]
    return leaves[0],len(words)


def delete_tip(word,event,side,index):
    result = []
    for e in word:
        if int(event in e['after'])!=side:
            result.append(e)
            continue
        if [event,index] in e['pair']:
            continue
        result.append(dict(e,pair=[[c,i-int(c==event and i>index)] for c,i in e['pair']]))
    return result


def audit():
    # Every cut basis change commutes with the actual marker expansion to
    # either end, including when one expansion is empty.
    relations = 0
    for p,q,r,s in product(range(4),repeat=4):
        ports = [[p,q],[r,s]]
        for state in (0,1):
            old = [1] if state else []
            for j in range(ports[1][state]):
                left = [dict(after=old,pair=[[0,i],[1,j]]) for i in range(p)]
                right = [dict(after=[0,*old],pair=[[0,i],[1,j]]) for i in range(q)]
                assert normal_form(ports,0,left)==normal_form(ports,0,right)
                relations += 1
    for d in (2,3):
        ports = [[d,d],[d,d]]
        w = brunnian(d)
        result = normal_form(ports,0,w)
        assert not result['central'] and len(result['mixed'])==1
        for e,side,i in product(range(2),range(2),range(d)):
            small = [p.copy() for p in ports]
            small[e][side] -= 1
            assert normal_form(small,0,delete_tip(w,e,side,i))==dict(central=[],mixed=[])
    # Middle-cut modes of distinct event pairs commute even when they
    # share an event. Opposite mixed states for the same pair need not.
    def motion(after,a,b):
        return [dict(after=after,pair=[[a,0],[b,0]])]
    ports = [[2,2]]*3
    x,y,z = motion([0],0,1),motion([1],0,1),motion([1],1,2)
    assert normal_form(ports,0,bracket(x,z))==dict(central=[],mixed=[])
    assert normal_form(ports,0,bracket(x,y))['mixed']
    witness,shortlist = prescribed(2,2)
    assert normal_form([[2,2]]*2,0,witness)['mixed']
    for e,s,i in product(range(2),repeat=3):
        small = [[2,2],[2,2]]
        small[e][s] -= 1
        assert normal_form(small,0,delete_tip(witness,e,s,i))==dict(central=[],mixed=[])
    print(f'{relations} individual marker-to-port sphere transfers checked in the integral normal form.')
    print('Balanced two-rule witnesses at sizes two and three survive and vanish on every one-tip deletion.')
    print(f'The prescribed size-two comparison combines {shortlist} distinct short nonidentity words.')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--brunnian',type=int,metavar='D',help='emit the two-event comparison at size D')
    parser.add_argument('--prescribed',type=int,metavar='D',help='combine all nonidentity mixed words of length at most D at size D')
    args = parser.parse_args()
    if args.brunnian is not None or args.prescribed is not None:
        d = args.brunnian if args.prescribed is None else args.prescribed
        if d<2:
            parser.error('balanced size must be at least two')
        word = brunnian(d) if args.prescribed is None else prescribed(d,d)[0]
        print(json.dumps(dict(ports=[[d,d],[d,d]],through=0,word=word)))
    elif args.input:
        print(json.dumps(normal_form(**json.loads(args.input.read_text())),indent=2))
    else:
        audit()
