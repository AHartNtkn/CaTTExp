"""Build a finite two-dimensional one-probe spine from a signed serial movie.

Input uses probe_movies JSON and an optional placement [gap,row,position].
A positive oriented edge label is one-based. Disk words are based attaching
loops after collapsing a maximal tree. They present the 2-complex, so empty
or duplicate relators count as cells.
"""
from argparse import ArgumentParser
from itertools import product
import json
from pathlib import Path

from semistrict_surface_component_braids import Partition
from semistrict_surface_history_group import exchange, inv, reduced
from semistrict_surface_probe_movies import movie


class Complex:
    def __init__(self):
        self.edges = []
        self.disks = []
        self.vertices = 0

    def vertex(self):
        self.vertices += 1
        return self.vertices-1

    def edge(self,a,b):
        self.edges.append((a,b))
        return len(self.edges)

    def cylinder(self,ends,paths):
        bridges = {v:self.edge(*p) for v,p in ends.items()}
        for a,b,left,right in paths:
            self.disks.append((ends[a][0],(*left,bridges[b],*inv(right),-bridges[a])))

    def presentation(self,base):
        forest = Partition()
        chords = []
        for i,(a,b) in enumerate(self.edges,1):
            if forest.at(a)==forest.at(b):
                chords.append((a,i))
            else:
                forest.unite(a,b)
        root = forest.at(base)
        numbers = {g:i for i,g in enumerate((g for a,g in chords if forest.at(a)==root),1)}
        words = [reduced(tuple(numbers[abs(g)]*(1 if g>0 else -1) for g in word if abs(g) in numbers))
                 for v,word in self.disks if forest.at(v)==root]
        return len(numbers),words


class Slice:
    def __init__(self,cx,width,rows,ports):
        self.rows = rows
        self.v = {}
        self.step = {}
        for q in range(width+1):
            self.v[0,q] = cx.vertex()
        for j,(offset,g) in enumerate(rows):
            incoming,outgoing = map(len,ports[g])
            next_width = width+outgoing-incoming
            for q in range(next_width+1):
                self.v[j+1,q] = cx.vertex()
            for q in range(width+1):
                corridors = [('L',q<=offset,q),('R',q>=offset+incoming,q+outgoing-incoming)]
                for side,allowed,destination in corridors:
                    if allowed:
                        edge = cx.edge(self.v[j,q],self.v[j+1,destination])
                        self.step[j,q,side] = destination,edge
            width = next_width

    def path(self,row,pos,sides):
        path = []
        for j,side in enumerate(sides,row):
            step = self.step.get((j,pos,side))
            if step is None:
                return None
            pos,edge = step
            path.append(edge)
        return pos,tuple(path)


def expanded(chart,side):
    rows = tuple(map(tuple,chart['diagram']))
    slot = chart['slot']
    p,_ = rows[slot]
    return rows[:slot]+tuple((p+q,g) for q,g in chart[side])+rows[slot+1:]


def site_cylinder(cx,width,ports,chart,left,right):
    # The joint slice supplies the indexing graph only; its two maps cross
    # each substituted block down the same exterior side.
    joint = Slice(Complex(),width,tuple(map(tuple,chart['diagram'])),ports)
    slot = chart['slot']
    counts = len(chart['input']),len(chart['output'])
    def row(j,n):
        return j if j<=slot else j+n-1
    ends = {(j,q):(left.v[row(j,counts[0]),q],right.v[row(j,counts[1]),q]) for j,q in joint.v}
    paths = []
    for (j,q,side),(z,_) in joint.step.items():
        pair = []
        for reading,n in zip((left,right),counts):
            reached,word = reading.path(row(j,n),q,[side]*(n if j==slot else 1))
            assert reached==z
            pair.append(word)
        paths.append(((j,q),(j+1,z),*pair))
    cx.cylinder(ends,paths)


def seam_cylinder(cx,left,right,letter):
    j = abs(letter)-1
    ends = {v:(a,right.v[v]) for v,a in left.v.items() if v[0]!=j+1}
    paths = []
    for (i,q,side),(z,edge) in left.step.items():
        if i not in (j,j+1):
            z2,new = right.step[i,q,side]
            assert z2==z
            paths.append(((i,q),(i+1,z),(edge,),(new,)))
    for i,q in ends:
        if i!=j:
            continue
        for sides in product('LR',repeat=2):
            # Positive exchange starts with the spatially right gate.
            spatial = sides[::-1] if letter>0 else sides
            if spatial==('L','R'):
                continue
            path = left.path(j,q,sides)
            if path is not None:
                z,word = path
                z2,new = right.path(j,q,sides[::-1])
                assert z2==z
                paths.append(((j,q),(j+2,z),word,new))
    cx.cylinder(ends,paths)


def presentation(data):
    if 'placement' in data:
        gap,row,pos = data['placement']
    else:
        probes = data.get('probes',[])
        if len(probes)>1:
            raise ValueError('select a component with placement when multiple probes are listed')
        gap,row,pos = probes[0] if probes else (0,0,0)
    group, = [c for c in movie(dict(data,probes=[[gap,row,pos]]),with_homology=True) if c['probes']]
    width = len(data['path'])
    ports = {g:(s,t) for g,(_,s,t) in data['gates'].items()}
    charts = data['charts']
    cx = Complex()
    current = Slice(cx,width,expanded(charts[0],'input'),ports)
    gaps = [current]
    for j,chart in enumerate(charts):
        if j:
            for letter in data['seams'][j-1]:
                following = Slice(cx,width,exchange(current.rows,letter,ports),ports)
                seam_cylinder(cx,current,following,letter)
                current = following
        assert current.rows==expanded(chart,'input')
        following = Slice(cx,width,expanded(chart,'output'),ports)
        site_cylinder(cx,width,ports,chart,current,following)
        gaps.append(following)
        current = following
    rank,faces = cx.presentation(gaps[gap].v[row,pos])
    return dict(generators=rank,faces=faces,betti=group['betti'])


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    print(json.dumps(presentation(json.loads(parser.parse_args().input.read_text())),indent=2))
