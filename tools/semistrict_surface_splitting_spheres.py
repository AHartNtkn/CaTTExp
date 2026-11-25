"""Compute one-probe sphere orbits for a compact core embedded in three-space.

Requires the Regina Python module. Input is {"core": finite_core_isoSig},
or {"pairs": b, "braid": signed_generators, "long": true}. The latter uses
a first unpaired strand at both ends and b adjacent cap pairs. With long
false all ends are paired and the three-space exterior has a puncture at
infinity. The core mode assumes the supplied connected manifold embeds in S^3.
"""
from argparse import ArgumentParser
from collections import deque
import json
from pathlib import Path

import regina

from semistrict_surface_probe_movies import configuration_betti, movie


def plat_link(pairs,braid,long):
    if type(pairs) is not int or pairs<0 or type(long) is not bool:
        raise ValueError('expected a nonnegative number of pairs and a boolean long flag')
    n = 2*pairs+int(long)
    if not n:
        raise ValueError('the link needs a component')
    order = list(range(n))
    crossings = []
    visits = [[] for _ in order]
    for index,g in enumerate(braid,1):
        if type(g) is not int or not 0<abs(g)<n:
            raise ValueError('crossing outside the strand list')
        i = abs(g)-1
        a,b = order[i:i+2]
        sign = 1 if g>0 else -1
        visits[a].append(sign*index)
        visits[b].append(-sign*index)
        crossings.append((a,b,sign))
        order[i:i+2] = b,a
    strand = {i:n+j for j,i in enumerate(order)}
    strand.update({b:a for a,b in list(strand.items())})
    cap = {0:n,n:0} if long else {}
    for i in range(int(long),n,2):
        for j in (i,i+n):
            cap[j],cap[j+1] = j+1,j
    orientation = {}
    components = []
    for i in range(n):
        if i in orientation:
            continue
        component = []
        start = i
        while True:
            stop = strand[start]
            bottom = min(start,stop)
            upward = start==bottom
            orientation[bottom] = 1 if upward else -1
            component.extend(visits[bottom] if upward else reversed(visits[bottom]))
            start = cap[stop]
            if start==i:
                break
        components.append(component)
    signs = [s*orientation[a]*orientation[b] for a,b,s in crossings]
    return regina.Link.fromData(signs,components)


def sides(tri,surface):
    # Closed spheres separate in S^3. Integrate their edge intersections
    # modulo two and read the two colours on the original boundary.
    graph = [[] for _ in tri.vertices()]
    for edge in tri.edges():
        a,b = (edge.vertex(i).index() for i in range(2))
        parity = surface.edgeWeight(edge.index()).pythonValue()%2
        graph[a].append((b,parity))
        graph[b].append((a,parity))
    colour = {0:0}
    pending = deque([0])
    while pending:
        a = pending.popleft()
        for b,parity in graph[a]:
            value = colour[a]^parity
            if b not in colour:
                colour[b] = value
                pending.append(b)
            elif colour[b]!=value:
                raise ValueError('nonseparating sphere is incompatible with the embedded-core input')
    return [colour[b.vertex(0).index()] for b in tri.boundaryComponents()]


def split_count(tri,proof):
    boundaries = tri.countBoundaryComponents()
    if not tri.isValid() or not tri.isOrientable() or not tri.isConnected() or tri.isIdeal() or not boundaries:
        raise ValueError('expected a connected compact orientable triangulation with real boundary')
    genus_zero = sum(b.eulerChar()==2 for b in tri.boundaryComponents())
    if genus_zero==boundaries:
        return boundaries-1
    if genus_zero:
        # Fill the spherical boundaries, preserving all positive-genus ones.
        tri.makeIdeal()
        tri.simplify()
        tri.truncateIdeal()
        tri.simplify()
        assert tri.countBoundaryComponents()==boundaries-genus_zero
        return genus_zero+split_count(tri,proof)
    if boundaries==1:
        return 0
    # Store the normal coordinates in precisely the simplex numbering
    # reconstructed by the certificate, including all local vertex orders.
    tri = regina.Triangulation3.fromIsoSig(tri.isoSig())
    surfaces = regina.NormalSurfaces(tri,regina.NormalCoords.Standard,regina.NormalList.Vertex)
    record = dict(core=tri.isoSig(),vertex_surfaces=surfaces.size())
    proof.append(record)
    for s in surfaces:
        if s.hasRealBoundary() or s.eulerChar()!=2 or not s.isConnected():
            continue
        partition = sides(tri,s)
        if len(set(partition))<2:
            continue
        record.update(boundary_sides=partition,normal=[n.pythonValue() for n in s.vector()])
        pieces = s.cutAlong().triangulateComponents()
        assert len(pieces)==2
        factors = []
        for piece in pieces:
            # The two original sides each have positive-genus boundary. Cap
            # their one new spherical cut boundary before testing either side.
            assert sum(b.eulerChar()==2 for b in piece.boundaryComponents())==1
            piece.simplify()
            piece.makeIdeal()
            piece.simplify()
            piece.truncateIdeal()
            piece.simplify()
            assert 0<piece.countBoundaryComponents()<boundaries
            factors.append(split_count(piece,proof))
        return 1+sum(factors)
    return 0


def analyze(data):
    m = data.get('probes',1)
    if type(m) is not int or m<0:
        raise ValueError('expected a nonnegative probe count')
    puncture = 0
    if 'core' in data:
        tri = regina.Triangulation3.fromIsoSig(data['core'])
    else:
        long = data.get('long',True)
        link = plat_link(data['pairs'],data['braid'],long)
        tri = link.complement()
        if tri.isIdeal():
            tri.truncateIdeal()
        tri.simplify()
        puncture = int(not long)
    proof = []
    first = tri.homology().rank()
    second = tri.homologyH2Z2()+puncture
    orbits = split_count(tri,proof)+puncture
    return dict(betti=[1,first,second],sphere_orbits=orbits,aspherical=orbits==0,
                pure_one_probe_higher_faithful=first==0 or orbits==0,
                last_particle_sphere_orbits=[orbits+i for i in range(m)],normal_checks=proof)


def audit():
    split = analyze(dict(pairs=1,braid=[]))
    hopf = analyze(dict(pairs=1,braid=[1,1]))
    assert split['betti']==hopf['betti']==[1,2,1]
    assert split['sphere_orbits']==1 and hopf['sphere_orbits']==0
    assert not split['pure_one_probe_higher_faithful'] and hopf['pure_one_probe_higher_faithful']
    record, = split['normal_checks']
    tri = regina.Triangulation3.fromIsoSig(record['core'])
    cert = regina.NormalSurface(tri,regina.NormalCoords.Standard,record['normal'])
    assert cert.isConnected() and not cert.hasRealBoundary() and cert.eulerChar()==2
    assert len(set(sides(tri,cert)))==2
    for n in [1,2,3]:
        r = analyze(dict(pairs=n-1,long=True,braid=[]))
        assert r['sphere_orbits']==n-1 and r['betti']==[1,n,n-1]
        r = analyze(dict(pairs=n,long=False,braid=[]))
        assert r['sphere_orbits']==n and r['betti']==[1,n,n]
    for g in (-1,1):
        for word in ([g,g],[g,g,2,-2],[-2,2,g,g]):
            assert analyze(dict(pairs=1,braid=word))['aspherical']
    ports = {g:['x','',''] for g in ['H','p','a','b']}
    joint = [(0,'p'),(0,'H')]
    block = [(0,'a'),(0,'b')]
    charts = [dict(diagram=joint,slot=1,input=a,output=b) for a,b in [([],block),(block,[])]]
    for word,expected in [([],split),([1,1],hopf)]:
        data = dict(vertex='x',path='',edges={},gates=ports,charts=charts,seams=[word],probes=[[0,0,0]])
        component, = movie(data,with_homology=True)
        assert component['betti']==expected['betti'] and component['event_groups']==[[0,1]]
    ball = regina.Example3.ball()
    ball_sig = ball.isoSig()
    for m in range(1,4):
        answer = analyze(dict(core=ball_sig,probes=m))
        ranks = configuration_betti(m,[0,0,0],lambda *_:False)
        assert sum(answer['last_particle_sphere_orbits'])==ranks[2]
    # A genuine spherical boundary alongside a torus exercises filling
    # before recursion without assuming how the cellulation was produced.
    solid = regina.Example3.lst(1,2)
    solid.puncture()
    assert analyze(dict(core=solid.isoSig()))['sphere_orbits']==1
    print('the split and Hopf movies both have Betti numbers (1,2,1); their sphere-orbit ranks are 1 and 0')
    print('normal sphere certificate replayed; long and closed unlinks through three components and six signed Hopf presentations checked')


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    args = parser.parse_args()
    if args.input:
        print(json.dumps(analyze(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
