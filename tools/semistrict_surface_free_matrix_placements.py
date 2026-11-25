"""Read one-occurrence sheets in the integral matrix module of a free deck group.

Words are lists of signed, one-based generator indices. Input JSON specifies
rank, relators and word. With --sheet verify an integral placement. With
--modulus solve the finite matrix quotient and print a witnessing sheet.
--higman uses Higman's presentation and its first generator as target.
"""
from argparse import ArgumentParser
from collections import deque
from itertools import product
import json
from pathlib import Path


IDENTITY = (1,0,0,1)


def mul(left, right):
    a,b,c,d = left
    e,f,g,h = right
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def inv(matrix):
    a,b,c,d = matrix
    return d,-b,-c,a


def power(matrix, n):
    if n < 0:
        return power(inv(matrix), -n)
    value = IDENTITY
    while n:
        if n%2:
            value = mul(value,matrix)
        matrix = mul(matrix,matrix)
        n //= 2
    return value


def basis(rank):
    if rank < 2:
        raise ValueError('use a free rank of at least two')
    b = (1,0,2,1)
    u = mul((1,2,0,1), b)
    return [power(u,rank-1)]+[mul(mul(power(u,i),b),power(u,-i)) for i in range(rank-1)]


def value(letters, word):
    result = IDENTITY
    for i in word:
        if type(i) is not int or not 1 <= abs(i) <= len(letters):
            raise ValueError('word contains an invalid signed generator')
        mat = letters[abs(i)-1]
        result = mul(result,mat if i>0 else inv(mat))
    return result


def presentation(rank, relators, word):
    gens = basis(rank)
    return [(a,a) for a in gens]+[(value(gens,r),IDENTITY) for r in relators], value(gens,word)


def sheet_value(actions, sheet):
    left = value([g for g,_ in actions],sheet)
    right = value([h for _,h in actions],sheet)
    return mul(left,inv(right))


def residue_sheet(actions, target, modulus):
    if modulus < 1:
        raise ValueError('modulus must be positive')
    def reduce(m):
        return tuple(i%modulus for i in m)
    start, goal = reduce(IDENTITY),reduce(target)
    changes = []
    for i,(g,h) in enumerate(actions,1):
        changes.extend([(i,reduce(g),reduce(inv(h))),(-i,reduce(inv(g)),reduce(h))])
    queue = deque([start])
    parents = {start:None}
    while queue:
        state = queue.popleft()
        if state == goal:
            # An action on a state adds the corresponding letter on the left.
            word = []
            while parents[state]:
                state,letter = parents[state]
                word.append(letter)
            return word
        for letter,g,hi in changes:
            nxt = reduce(mul(mul(g,state),hi))
            if nxt not in parents:
                queue.append(nxt)
                parents[nxt] = state,letter
    return None


def induced_value(actions, word):
    """Apply the two ambient generators to the identity-coset step."""
    index = len(actions)-1
    slot, matrix = 0, IDENTITY
    for letter in reversed(word):
        sheet = 0
        if abs(letter)==1:
            nxt = (slot+letter)%index
            if letter==1 and nxt==0:
                sheet = 1
            if letter==-1 and slot==0:
                sheet = -1
            slot = nxt
        elif abs(letter)==2:
            sheet = slot+2 if letter>0 else -(slot+2)
        else:
            raise ValueError('ambient sheet words have only two generators')
        if sheet:
            g,h = actions[abs(sheet)-1]
            matrix = mul(mul(g,matrix),inv(h)) if sheet>0 else mul(mul(inv(g),matrix),h)
    return slot,matrix


def embed_sheet(actions, word):
    index = len(actions)-1
    out = []
    for letter in word:
        j = abs(letter)-2
        if j<0:
            out += [1 if letter>0 else -1]*index
        else:
            out += [-1]*j+[2 if letter>0 else -2]+[1]*j
    return out


def higman():
    rels = []
    for i in range(1,5):
        j = i%4+1
        rels.append([-i,j,i,-j,-j])
    return dict(rank=4,relators=rels,word=[1])


def audit():
    # For <a,b | b=1> scan a word into a product of conjugates of b
    # followed by its remaining power of a. Verify the full matrix identity,
    # not just its image in the cyclic quotient.
    actions, _ = presentation(2,[[2]],[])
    gens = basis(2)
    total = admitted = 0
    for length in range(6):
        for word in product((1,-1,2,-2), repeat=length):
            pos, sheet = 0,[]
            for letter in word:
                if abs(letter)==1:
                    pos += letter
                else:
                    d = [1 if pos>=0 else -1]*abs(pos)
                    sheet.extend(d+[3 if letter>0 else -3]+[-x for x in reversed(d)])
            assert mul(sheet_value(actions,sheet),power(gens[0],pos)) == value(gens,word)
            assert (sheet_value(actions,sheet)==value(gens,word)) == (pos==0)
            assert induced_value(actions,embed_sheet(actions,sheet)) == (0,sheet_value(actions,sheet))
            total += 1
            admitted += pos==0
    actions,target = presentation(**higman())
    assert any(abs(g[0]+g[3])>2 for g,_ in actions[4:])
    for modulus in range(2,19):
        witness = residue_sheet(actions,target,modulus)
        assert witness is not None
        assert induced_value(actions,embed_sheet(actions,witness)) == (0,sheet_value(actions,witness))
        assert all((a-b)%modulus==0 for a,b in zip(sheet_value(actions,witness),target))
    return total, admitted


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--higman',action='store_true')
    mode.add_argument('--input',type=Path)
    op=parser.add_mutually_exclusive_group()
    op.add_argument('--modulus',type=int)
    op.add_argument('--sheet',type=Path)
    args=parser.parse_args()
    if args.higman or args.input:
        actions,target=presentation(**(higman() if args.higman else json.loads(args.input.read_text())))
        if args.modulus is not None:
            witness=residue_sheet(actions,target,args.modulus)
            print(json.dumps(dict(modulus=args.modulus,sheet=witness)))
        elif args.sheet:
            actual=sheet_value(actions,json.loads(args.sheet.read_text()))
            print(json.dumps(dict(image=actual,target=target,fills=actual==target)))
        else:
            print(json.dumps(dict(actions=actions,target=target)))
    elif args.modulus is not None or args.sheet:
        parser.error('select --higman or --input')
    else:
        total,admitted=audit()
        print(f'{total} word factorizations checked ({admitted} integral placements); '
              'two-generator induction checked; Higman target reached modulo 2 through 18.')
