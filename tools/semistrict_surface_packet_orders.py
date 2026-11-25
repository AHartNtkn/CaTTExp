"""Decide signed two-birth schedule tracks in a plane with through strands.

A JSON query gives through, p, q and syllables. Each syllable names its last
packet ("A" or "B") and a pure braid on the grouped terminal row through,A,B.
"""
from argparse import ArgumentParser
from itertools import groupby, product
from pathlib import Path
import json

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import cyclic, inv, reduced
from semistrict_surface_scalar_leaves import swapped
from semistrict_surface_shared_edge import braid_image
from semistrict_surface_trefoil_mixed import substitute
from semistrict_surface_two_births import generators


class PacketOrders:
    def __init__(self, m, p, q):
        if any(type(s) is not int for s in (m,p,q)) or m < 0 or min(p,q) < 1:
            raise ValueError('expected a nonnegative through count and two positive packet sizes')
        self.n = m+p+q
        self.blocks = {'A': range(m,m+p), 'B': range(m+p,self.n)}
        self.row = tuple(range(self.n))
        self.through = range(m)

    def grouped(self, word, blocks, keep):
        # Compare the given restriction to its own unframed parallel expansion.
        keep = tuple(keep)
        sizes = {i: 1 for i in keep}
        for b in blocks:
            packet = self.blocks[b]
            sizes[packet[0]] = len(packet)
            for j in packet[1:]:
                del sizes[j]
        rebuilt = cable(restrict(self.n,word,sizes), sizes.values())
        projected = restrict(self.n,word,keep)
        return braid_image(len(keep),rebuilt) == braid_image(len(keep),projected)

    def read(self, last, word):
        if last not in self.blocks:
            raise ValueError('last packet must be A or B')
        if any(type(g) is not int or not 0 < abs(g) < self.n for g in word):
            raise ValueError('terminal braid letter outside the row')
        if swapped(self.row,word) != list(self.row):
            raise ValueError('the terminal braid must return all names')
        m = len(self.through)
        if braid_image(m,restrict(self.n,word,self.through)) != braid_image(m,()):
            raise ValueError('the through restriction must be trivial')
        first = 'A' if last == 'B' else 'B'
        early = [i for i in self.row if i not in self.blocks[last]]
        if not self.grouped(word,[last],self.row) or not self.grouped(word,[first],early):
            raise ValueError('the signed braid cannot be realized in this birth order')

    def tie(self, word):
        return self.grouped(word,('A','B'),self.row)

    def solve(self, syllables):
        path = []
        terminal = []
        for s in syllables:
            last, word = s['last'], tuple(s['braid'])
            self.read(last,word)
            path.append((last,word))
            terminal.extend(word)
        # The tie has the same terminal representation in either order.
        # Sliding a tie into its neighbour strictly shortens the path.
        while len(path) > 1:
            path = [(last,reduced(g for _,w in seq for g in w))
                    for last,seq in groupby(path,key=lambda s:s[0])]
            if len(path) == 1:
                break
            i = next((i for i,(_,w) in enumerate(path) if self.tie(w)),None)
            if i is None:
                break
            other = path[i-1 if i else 1][0]
            path[i] = (other,path[i][1])
        action = braid_image(self.n,terminal)
        trivial = action == braid_image(self.n,())
        amalgam_trivial = not path or len(path)==1 and braid_image(self.n,path[0][1])==braid_image(self.n,())
        assert trivial == amalgam_trivial
        return dict(fixes_terminal=trivial, reduced_syllables=path,
                    terminal_packet_curves={b:cyclic(substitute([i+1 for i in block],action))
                                            for b,block in self.blocks.items()})


def audit():
    count = 0
    for m,p,q in product((1,2),(2,3),(2,3)):
        model = PacketOrders(m,p,q)
        a,b = [tuple(x+m if x>0 else x-m for x in w)
               for w in (generators(p,q)[0],generators(p,q)[p])]
        # The last through strand turns about the whole A packet. Conjugating
        # just one order introduces spectator motion that forgetting it loses.
        turn = cable((m,m),[1]*m+[p,q])
        w = reduced(turn+a+inv(turn)+inv(a))
        without_through = restrict(model.n,w,range(m,model.n))
        assert braid_image(p+q,without_through)==braid_image(p+q,())
        model.read('B',w)
        assert not model.tie(w)
        try:
            model.read('A',w)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted a nonedge motion in the opposite order')
        def syllable(last,word):
            return dict(last=last,braid=word)
        for signs in product((1,-1),repeat=2):
            u,v = w if signs[0]>0 else inv(w), b if signs[1]>0 else inv(b)
            legs = [syllable('B',u),syllable('A',v),syllable('B',inv(u)),syllable('A',inv(v))]
            # A short witness with trivial projection after forgetting spectators.
            result = model.solve(legs)
            assert not result['fixes_terminal'] and len(result['reduced_syllables'])==4
            folded = [syllable('B',u),syllable('A',turn),syllable('B',inv(turn)+inv(u))]
            assert model.solve(folded)['fixes_terminal']
            count += 1
    print(f'{count} signed alternating commutators survive with through strands and vanish after forgetting them.')
    print('All tie transfers contract. The opposite order rejects each spectator-dependent nonedge.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs='?',type=Path)
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(PacketOrders(data['through'],data['p'],data['q']).solve(data['syllables']),indent=2))
    else:
        audit()
