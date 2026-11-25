"""Extract scalar face histories of a positioned point-site movie with closed ports.

Input is the chart and seam format of semistrict_surface_serial_gate_tracks.
Boundary records report when a host face inherits or releases nonempty ports.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_component_braids import Components, restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_movie_spine import expanded
from semistrict_surface_probe_movies import Faces
from semistrict_surface_scalar_leaves import gate_segments, swapped
from semistrict_surface_serial_gate_tracks import motion


def reading(data, rows, names):
    named = tuple((p,j) for (p,_),j in zip(rows,names,strict=True))
    ports = {j:data['gates'][g][1:] for (_,g),j in zip(rows,names,strict=True)}
    width = len(data['path'])
    parts = Components(named,ports,width)
    faces = Faces(named,ports,width)
    # Address a region at its fixed outer boundary, independently of the
    # components inside it. Rim and anchored corners also name unbounded faces.
    corners = {}
    def add(region, key):
        corners[region] = min(corners.get(region,key),key)
    for d,b in [(0,0),(len(rows),1)]:
        for k in range(faces.slices[d]+1):
            add(faces.spots[d,k], ('rim',b,k))
    core_at = {j:core for core,es in parts.skeleton.items() for j in es}
    for i,(p,j) in enumerate(named):
        for side,letters in enumerate(ports[j]):
            for k in range(len(letters)+1):
                region = faces.spots[i+side,p+k]
                if j not in core_at or region!=parts.face[core_at[j]]:
                    add(region,('gate',j,side,k))
    fields = {key:[] for key in corners.values()}
    for j in names:
        if j in parts.skeleton:
            fields[corners[parts.face[j]]].append(j)
    assert len(fields)==len(set(faces.spots.values()))
    return fields


def factors(data):
    if not data['charts']:
        if data['seams']:
            raise ValueError('seam without a site')
        return dict(factors=[], scalar_detection=True, blank_internal_ports=True)
    initial, final, _, _, steps = gate_segments(data)
    charts = data['charts']
    records = {}
    def record(face):
        if face not in records:
            records[face] = dict(face=face,steps=[],interval_braids=[[]],boundaries=[])
        return records[face]
    first = reading(data,expanded(charts[0],'input'),initial)
    for f,r in first.items():
        record(f)['initial'] = r
    for i,(ch,(pre,inputs,outputs,post)) in enumerate(zip(charts,steps,strict=True)):
        marker = -2-i
        if any(data['gates'][ch['diagram'][ch['slot']][1]][1:]):
            raise ValueError('expected a point site')
        tie = reading(data,ch['diagram'],[*pre,marker,*post])
        lo = reading(data,expanded(ch,'input'),[*pre,*inputs,*post])
        outnames = [*pre,*outputs,*post]
        hi = reading(data,expanded(ch,'output'),outnames)
        host, = [f for f,row in tie.items() if marker in row]
        for f in lo.keys() | hi.keys() | tie.keys():
            entry = record(f)
            if f==host:
                j = tie[f].index(marker)
                a = [n for n in lo[f] if n in inputs]
                b = [n for n in hi[f] if n in outputs]
                assert lo[f]==tie[f][:j]+a+tie[f][j+1:]
                assert hi[f]==tie[f][:j]+b+tie[f][j+1:]
                entry['steps'].append(dict(use=i,slot=j,input=a,output=b))
                entry['interval_braids'].append([])
            elif f not in tie:
                if f in lo:
                    entry['boundaries'].append(dict(death=i,points=lo[f]))
                if f in hi:
                    entry['boundaries'].append(dict(birth=i,points=hi[f]))
            else:
                assert tie[f]==lo[f]==hi[f]
        if i<len(data['seams']):
            seam = data['seams'][i]
            following = reading(data,expanded(charts[i+1],'input'),swapped(outnames,seam))
            for f,row in hi.items():
                word = restrict(len(outnames),seam,{j for j,n in enumerate(outnames) if n in row})
                assert swapped(row,word)==following[f]
                record(f)['interval_braids'][-1].extend(word)
    for f,r in hi.items():
        record(f)['final'] = r
    # Replay each local movie with its own actual lifetime endpoints.
    for entry in records.values():
        births = [b['points'] for b in entry['boundaries'] if 'birth' in b]
        deaths = [b['points'] for b in entry['boundaries'] if 'death' in b]
        row, = births + ([entry['initial']] if 'initial' in entry else [])
        last, = deaths + ([entry['final']] if 'final' in entry else [])
        for step,seam in zip(entry['steps'],entry['interval_braids']):
            row = swapped(row,seam)
            j = step['slot']
            assert row[j:j+len(step['input'])]==step['input']
            row[j:j+len(step['input'])] = step['output']
        assert swapped(row,entry['interval_braids'][-1])==last
    active = [v for v in records.values() if v['steps']]
    for entry in active:
        proper = [b for b in entry['boundaries'] if b['points']]
        entry['unforced_caps'] = []
        for boundary in proper:
            forward = 'birth' in boundary
            reached = set(boundary['points'])
            missing = []
            for step in (entry['steps'] if forward else reversed(entry['steps'])):
                needs, emits = (step['input'],step['output']) if forward else (step['output'],step['input'])
                if reached.intersection(needs):
                    reached.update(emits)
                else:
                    missing.append(step['use'])
            if missing:
                entry['unforced_caps'].append(dict(boundary=boundary, independent_uses=sorted(missing)))
    return dict(factors=active, scalar_detection=all(not f['unforced_caps'] for f in active),
                blank_internal_ports=all(not b['points'] for v in records.values()
                                                        for b in v['boundaries']))


def sample(nested, cross):
    gates={g:['x','',''] for g in ('z','u','v','h')}
    gates.update(B=['x','','ff'],D=['x','ff',''])
    rows, charts, seams = [(0,'h')], [], []
    def at(j,pos,old,new,seam=()):
        nonlocal rows
        if charts:
            rows = list(motion(tuple(rows),{g:(s,t) for g,(_,s,t) in gates.items()},seam))
            seams.append(seam)
        assert rows[j:j+len(old)]==[(pos+k,g) for k,g in old]
        chart=dict(diagram=rows[:j]+[(pos,'z')]+rows[j+len(old):],slot=j,input=old,output=new)
        charts.append(chart)
        rows[j:j+len(old)] = [(pos+k,g) for k,g in new]
    packet=[(0,'B')]+([(1,'u')] if nested else [])+[(0,'D')]
    at(0,0,[],packet)
    at(1,1,[],[(0,'u'),(0,'v')],cable(cross,[len(packet),1]))
    at(1,1,[(0,'v'),(0,'u')],[],(2,))
    at(0,0,packet,[])
    return dict(vertex='x',path='',edges={'f':['x','x']},gates=gates,charts=charts,seams=seams)


def audit():
    for cap in (False,True):
        for turns in range(-3,4):
            cross = (1 if turns>=0 else -1,)*(2*abs(turns))
            result=factors(sample(cap,cross))
            assert result['blank_internal_ports']!=cap
            outer,inner=sorted(result['factors'],key=lambda r:r['steps'][0]['use'])
            assert [s['use'] for s in outer['steps']]==[0,3]
            assert [s['use'] for s in inner['steps']]==[1,2]
            assert outer['interval_braids'][1]==list(cross)
            assert inner['interval_braids'][1]==[1]
            assert [len(b['points']) for b in inner['boundaries']]==[int(cap)]*2
            assert result['scalar_detection']!=cap
    # One occupied internal endpoint, an anchored split, and two final
    # deaths which can occur in either order. Dropping the closing lens
    # while retaining the opening cap preserves this local scalar factor.
    d = sample(True,())
    charts = []
    def change(diagram,j,old,new):
        pos = diagram[j][0]
        charts.append(dict(diagram=diagram,slot=j,input=[(0,g) for g in old],output=[(0,g) for g in new]))
    charts.append(d['charts'][0])
    change([(0,'B'),(1,'z'),(0,'D'),(0,'h')],1,'u','uv')
    change([(0,'B'),(1,'z'),(1,'v'),(0,'D'),(0,'h')],1,'u','')
    change([(0,'B'),(1,'z'),(0,'D'),(0,'h')],1,'v','')
    charts.append(dict(diagram=[(0,'z'),(0,'h')],slot=0,input=[(0,'B'),(0,'D')],output=[]))
    anchored=factors(dict(d,charts=charts,seams=[()]*4))
    assert anchored['scalar_detection'] and not anchored['blank_internal_ports']
    # Raw collision rank for two free events in a newly created empty face.
    dd=sample(False,())
    probe=dict(diagram=[(0,'B'),(1,'z'),(0,'D'),(0,'h')],slot=1,input=[],output=[])
    dd.update(charts=[dd['charts'][0],probe,probe,dd['charts'][-1]],seams=[()]*3)
    ff=factors(dd)
    assert ff['scalar_detection'] and [s['use'] for s in ff['factors'][1]['steps']]==[1,2]
    print('14 nested movies replayed: independent inner and outer signed braids, '
          'the two local cap uses, and empty versus occupied internal endpoints.')


if __name__=='__main__':
    cli=ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    args=cli.parse_args()
    if args.input:
        print(json.dumps(factors(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
