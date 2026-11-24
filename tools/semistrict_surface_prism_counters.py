"""Compile two-counter programs to literal positive scalar Gray movies.

--machine JSON expects start, halt, input (two naturals), and program mapping
states to ["inc", counter, next] or ["test", counter, zero, nonzero].
A nonzero test decrements. Counters are indexed 0 and 1. The raw query asks
for the cleaned halt configuration. All emitted queries have a surface filler.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from itertools import product
import json
from pathlib import Path

from semistrict_surface_positive_movies import moves, windows


BASE='abab'
X='X'
P='p'


def state(q):
    return 'q/'+q


def canonical(q,a,b):
    return (((X,0),)+((P,1),)*a+((X,0),(q,1),(X,2))+
            ((P,3),)*b+((X,2),))


def prefixes(h,word,labels):
    h=list(h)
    yield tuple(h)
    for x,i in word:
        if x==X:
            if not 0<=i<len(h)-1:
                raise ValueError('crossing outside history')
            h[i],h[i+1]=h[i+1],h[i]
        elif not 0<=i<len(h) or h[i]!=labels[x][0]:
            raise ValueError('misplaced unary label')
        yield tuple(h)


def instructions_for(machine):
    program=machine['program']
    stop=machine['halt']
    start=machine['start']
    if stop in program or start not in {*program,stop}:
        raise ValueError('expected a distinct halt with no outgoing instruction')
    if len(machine['input'])!=2 or any(type(x)!=int or x<0 for x in machine['input']):
        raise ValueError('expected two nonnegative inputs')
    instructions={state(q):op for q,op in program.items()}
    for op in instructions.values():
        if (not op or op[0] not in ('inc','test') or len(op)!=(3 if op[0]=='inc' else 4)
                or op[1] not in (0,1) or any(q not in {*program,stop} for q in op[2:])):
            raise ValueError('invalid instruction')
    instructions={q:(kind,k,*map(state,dest)) for q,(kind,k,*dest) in instructions.items()}
    instructions[state(stop)]=('test',0,'drain1',state(stop))
    instructions['drain1']=('test',1,'done','drain1')
    return instructions


def compile_machine(machine):
    start,stop=machine['start'],machine['halt']
    instructions=instructions_for(machine)
    names=(*instructions,'done')
    labels={P:'aa',**{q:'bb' for q in names}}
    rules=[]
    def add(kind,h,l,r):
        if list(prefixes(h,l,labels))[-1]!=list(prefixes(h,r,labels))[-1]:
            raise ValueError('nonparallel rule')
        rules.append((kind,h,l,r))
    for q,r in product(names,repeat=2):
        if q!=r:
            add('commute','b',((q,0),(r,0)),((r,0),(q,0)))
    for c,d in product('ab',repeat=2):
        for kind,l,r in windows(2,labels):
            label=next(x for x,_ in l if x!=X)
            side=0 if kind=='right' else 1
            pair=(c,d)
            if pair[side]==labels[label][0] and (label!=P or pair[1-side]!='b'):
                add('prism',c+d,r,l)
    def instr(q,k,r,action):
        h='ab' if k==0 else 'bab'
        i=k
        ctrl=1-k
        cross=((X,i),)
        middle=((P,i+1),)
        guard=cross*2 if action=='zero' else cross
        left=((q,ctrl),)+guard+(middle if action=='dec' else ())
        right=((r,ctrl),)+guard+(middle if action=='inc' else ())
        add(action,h,left,right)
    for q,(kind,k,*dest) in instructions.items():
        if kind=='inc':
            instr(q,k,dest[0],'inc')
        else:
            instr(q,k,dest[0],'zero')
            instr(q,k,dest[1],'dec')
    triple=((X,0),)*3
    add('shortcut','ab',((state(start),1),)+triple,((state(stop),1),)+triple)
    return dict(history=BASE,labels=labels,attachments=rules,
                source=canonical(state(start),*machine['input']),target=canonical('done',0,0))


def compile_two(machine):
    ins=instructions_for(machine)
    stop=state(machine['halt'])
    ins['init']=('test',0,stop,state(machine['start']))
    rules=[]
    cross=((X,0),)
    def mark(q,i=0):
        return ((q,i),)
    def add(kind,h,l,r):
        rules.append((kind,h,l,r))
    for q,(op,k,*dest) in ins.items():
        working=q
        if k:
            working='at/'+q
            add('go','aa',mark(q,1)+cross*2,cross*2+mark(working,1))
        def after(r):
            return 'back/'+r if k else r
        if op=='inc':
            add('inc','a',mark(working),mark(after(dest[0]))+mark(P))
        else:
            add('zero','aa',cross+mark(working,1)+cross,cross+mark(after(dest[0]),1)+cross)
            add('dec','a',mark(working)+mark(P),mark(after(dest[1])))
    returns=sorted({x for _,_,_,r in rules for x,_ in r if x.startswith('back/')})
    for q in returns:
        add('return','aa',cross*2+mark(q,1),mark(q[5:],1)+cross*2)
    states=sorted({x for _,_,l,r in rules for x,_ in l+r if x not in (X,P)})
    # All control codes have the same mass. A matching code exhausts all control
    # tokens, so a contextual rewrite can only select the current state.
    codes={q:('u',)*i+('v',)*(len(states)-1-i) for i,q in enumerate(states)}
    def expand(w):
        return tuple((y,i) for x,i in w for y in codes.get(x,(x,)))
    a,b=machine['input']
    src=cross+mark(P,1)*(a+1)+mark('init',1)+cross*2+mark(P,1)*b+cross
    dst=cross+mark('done',1)+cross*3
    out=[(kind,h,expand(l),expand(r)) for kind,h,l,r in rules]
    for x,y in product((P,'u','v'),repeat=2):
        if x!=y:
            out.append(('commute','a',mark(x)+mark(y),mark(y)+mark(x)))
    return dict(history='aa',labels={x:'aa' for x in (P,'u','v')},
                attachments=out,source=expand(src),target=expand(dst),codes=codes)


def chambers(word):
    """Count by crossing prefix length, input occurrence, and unary label."""
    bag=Counter()
    j=0
    for x,i in word:
        if x==X:
            if i!=0:
                raise ValueError('expected only the two-strand crossing')
            j+=1
        else:
            bag[j,i^(j%2),x]+=1
    return j,bag


class TwoSlots:
    """One raw step modulo all same-strand commutations and disjoint moves."""
    def __init__(self,rules):
        self.rules=[]
        for kind,h,l,r in rules:
            m,need=chambers(l)
            n,give=chambers(r)
            if m!=n:
                raise ValueError('different crossing counts')
            if (m,need)!=(n,give) or m:
                self.rules.append((kind,len(h),m,need,give))

    def placements(self,length):
        for kind,width,m,need,give in self.rules:
            for j in range(length-m+1):
                for pos in range(3-width):
                    def place(row):
                        return Counter({(j+k,(e+pos)^(j%2),x):v for (k,e,x),v in row.items()})
                    yield kind,j,m,place(need),place(give)

    def steps(self,length,bag):
        for (j,e,x),amount in bag.items():
            if amount and e^(j%2)==0:
                for k in (j-1,j+1):
                    if 0<=k<=length:
                        yield 'native',bag-Counter({(j,e,x):1})+Counter({(k,e,x):1})
        for kind,j,m,a,b in self.placements(length):
            if a<=bag:
                rest=bag-a
                if not any(j<k<j+m for k,_,_ in rest):
                    yield kind,rest+b

    def petri(self,data):
        length,start=chambers(data['source'])
        end_length,end=chambers(data['target'])
        if length!=end_length:
            return dict(source=[1],target=[0],transitions=[])
        keys=list(product(range(length+1),range(2),data['labels']))
        def vector(bag):
            return tuple(bag[k] for k in keys)
        edges=set()
        for _,_,m,a,b in self.placements(length):
            if m>1:
                raise ValueError('an applicable attachment spans two or more crossings')
            edges.add((vector(a),vector(b)))
        for j,e,x in keys:
            if e^(j%2)==0:
                for k in (j-1,j+1):
                    if 0<=k<=length:
                        edges.add((vector(Counter({(j,e,x):1})),vector(Counter({(k,e,x):1}))))
        return dict(source=vector(start),target=vector(end),transitions=sorted(edges))


class Literal:
    """Enumerate native moves and context placements in the four-slot hom."""
    def __init__(self,data):
        self.base=data['history']
        self.labels=data['labels']
        self.rules=defaultdict(list)
        for kind,h,l,r in data['attachments']:
            for base in range(len(self.base)-len(h)+1):
                left=tuple((x,i+base) for x,i in l)
                right=tuple((x,i+base) for x,i in r)
                self.rules[left[0]].append((kind,tuple(h),base,left,right))

    def steps(self,movie):
        yield from moves(self.base,movie,self.labels)
        hs=list(prefixes(self.base,movie,self.labels))
        for i,op in enumerate(movie):
            for kind,h,base,l,r in self.rules[op]:
                if hs[i][base:base+len(h)]==h and movie[i:i+len(l)]==l:
                    yield kind,movie[:i]+r+movie[i+len(l):]

    def instruction_steps(self,cfg):
        movie=canonical(*cfg)
        seen={movie}
        todo=deque([movie])
        outcomes=set()
        while todo:
            w=todo.popleft()
            for kind,v in self.steps(w):
                out=decode(v)
                if kind in ('inc','dec','zero','shortcut'):
                    assert kind!='shortcut'
                    outcomes.add(out)
                else:
                    assert out==cfg
                    if v not in seen:
                        seen.add(v)
                        todo.append(v)
        return outcomes,len(seen)


def decode(movie):
    perm=list(range(4))
    crossings=[0,0]
    counts=[0,0]
    ctrl=None
    for x,i in movie:
        if x==X:
            assert i in (0,2)
            crossings[i//2]+=1
            perm[i],perm[i+1]=perm[i+1],perm[i]
        elif x==P:
            counter=perm[i]//2
            assert perm[i]%2==0 and crossings[counter]==1
            counts[counter]+=1
        else:
            assert perm[i]==1 and ctrl is None
            ctrl=x
    assert crossings==[2,2] and ctrl is not None
    return ctrl,*counts


def net_from(data):
    labels=data['labels']
    if data['history']!='aa' or X in labels or any(v!='aa' for v in labels.values()):
        raise ValueError('expected two occurrences of a single scalar with unary loops')
    for face in (data['source'],data['target']):
        list(prefixes('aa',face,labels))
    commute=set()
    rules=[]
    for kind,h,l,r in data['attachments']:
        if h!='a'*len(h):
            raise ValueError('unknown scalar colour')
        if len(h)>2:
            continue
        l,r=tuple(map(tuple,l)),tuple(map(tuple,r))
        if list(prefixes(h,l,labels))[-1]!=list(prefixes(h,r,labels))[-1]:
            raise ValueError('nonparallel rule')
        if len(h)==1 and len(l)==2 and l==r[::-1]:
            commute.add((l[0][0],l[1][0]))
        rules.append((kind,h,l,r))
    if any((x,y) not in commute for x,y in product(labels,repeat=2) if x!=y):
        raise ValueError('supply both unary commutations at width one')
    return TwoSlots(rules).petri(data)


def compare_readings():
    cross=((X,0),)
    labels={P:'aa','u':'aa'}
    rules=[('commute','a',((x,0),(y,0)),((y,0),(x,0))) for x,y in product(labels,repeat=2) if x!=y]
    rules+=[('inc','a',(('u',0),),(('u',0),(P,0))),
            ('one','aa',cross+((P,1),),(('u',0),)+cross),
            ('two','aa',cross+((P,1),)+cross,cross+(('u',1),)+cross)]
    literal=Literal(dict(history='aa',labels=labels,attachments=rules))
    compiled=TwoSlots(rules)
    def key(word):
        length,bag=chambers(word)
        return length,tuple(sorted(bag.items()))
    groups=defaultdict(set)
    alphabet=(*cross,*product(labels,(0,1)))
    for n in range(5):
        for word in product(alphabet,repeat=n):
            got=groups[key(word)]
            for kind,next_word in literal.steps(word):
                if kind not in ('commute','exchange'):
                    got.add(key(next_word))
    for (length,items),got in groups.items():
        predicted={(length,tuple(sorted(v.items()))) for _,v in compiled.steps(length,Counter(dict(items)))}
        assert predicted==got,(items,predicted,got)
    return len(groups)


def checks():
    machine=dict(start='s',halt='h',input=[1,2],program={
        's':['test',0,'r','t'],'t':['inc',1,'s'],
        'r':['test',1,'h','u'],'u':['inc',0,'r']})
    data=compile_machine(machine)
    literal=Literal(data)
    count=readings=0
    for q in (*machine['program'],'h','drain1','done'):
        for a,b in product(range(3),repeat=2):
            s=state(q) if q not in ('drain1','done') else q
            cfg=(s,a,b)
            if q=='s':
                result=(state('t'),a-1,b) if a else (state('r'),a,b)
            elif q=='t':
                result=(state('s'),a,b+1)
            elif q=='r':
                result=(state('u'),a,b-1) if b else (state('h'),a,b)
            elif q=='u':
                result=(state('r'),a+1,b)
            elif q=='h':
                result=(s,a-1,b) if a else ('drain1',a,b)
            elif q=='drain1':
                result=(s,a,b-1) if b else ('done',a,b)
            else:
                result=None
            actual,n=literal.instruction_steps(cfg)
            assert actual==({result} if result is not None else set()),(cfg,actual,result)
            count+=1
            readings+=n
    two=compile_two(machine)
    net=TwoSlots(two['attachments'])
    def bag(q,a,b,j=1):
        out=Counter((j,0,x) for x in two['codes'][q])
        out.update({(1,0,P):a,(3,0,P):b})
        return +out
    configs=0
    for a,b in product(range(3),repeat=2):
        for q,op in instructions_for(machine).items():
            k=op[1]
            local='at/'+q if k else q
            if k:
                assert list(net.steps(4,bag(q,a,b)))==[('go',bag(local,a,b,3))]
            n=(a,b)[k]
            dest=op[2] if op[0]=='inc' or n==0 else op[3]
            v=[a,b]
            v[k]+=1 if op[0]=='inc' else -int(n>0)
            next_state='back/'+dest if k else dest
            actual=list(net.steps(4,bag(local,a,b,1+2*k)))
            assert len(actual)==1 and actual[0][1]==bag(next_state,*v,1+2*k)
            if k:
                assert list(net.steps(4,bag(next_state,*v,3)))==[('return',bag(dest,*v))]
            configs+=1
        assert list(net.steps(4,bag('init',a+1,b)))==[('dec',bag(state('s'),a,b))]
        assert list(net.steps(4,bag('done',a,b)))==[]
    assert chambers(two['source'])==(4,bag('init',2,2))
    assert chambers(two['target'])==(4,bag('done',0,0))
    return dict(two_slot_reading_classes=compare_readings(),two_slot_instruction_cases=configs,four_slot_configurations=count,literal_readings=readings,
                source=decode(data['source']),target=decode(data['target']))


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    inputs=parser.add_mutually_exclusive_group()
    inputs.add_argument('--machine',type=Path)
    inputs.add_argument('--one-crossing-net',type=Path)
    parser.add_argument('--slots',choices=(2,4),type=int,default=2)
    args=parser.parse_args()
    compiler=compile_two if args.slots==2 else compile_machine
    if args.machine:
        result=compiler(json.loads(args.machine.read_text()))
    elif args.one_crossing_net:
        result=net_from(json.loads(args.one_crossing_net.read_text()))
    else:
        result=checks()
    print(json.dumps(result))
