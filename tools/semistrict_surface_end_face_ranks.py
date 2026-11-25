"""Find the positive ranks attainable by dependent histories at two written ends.

Use the closed_returns rule format plus path (the spatial input word) and
initial, final (positioned planar 2-diagrams). Faces use zero-based row and gap.
"""
from argparse import ArgumentParser
import json
from pathlib import Path

from semistrict_surface_closed_returns import decide
from semistrict_surface_gate_forests import Presentation
from semistrict_surface_history_group import HistoryGroup
from semistrict_surface_probe_movies import Faces
from semistrict_surface_serial_gate_tracks import motion


def profile(data):
    initial, final = (tuple(map(tuple,data[k])) for k in ('initial','final'))
    base = Presentation(dict(data,diagram=initial,rules={}))
    start = base.sweep(data['vertex'],data['path'],initial)
    end = base.sweep(data['vertex'],data['path'],final)
    def empty():
        return dict(planar_path=None, faces=[], positive_ranks=[], maximum=0)
    if start!=end:
        raise ValueError('the two 2-diagrams have different spatial targets')
    if sorted(g for _,g in initial)!=sorted(g for _,g in final):
        return empty()
    if initial==final:
        path=()
    else:
        path=HistoryGroup(initial,base.ports).tree_paths.get(final)
        if path is None:
            return empty()
    assert motion(initial,base.ports,path)==final
    named=tuple((p,j) for j,(p,_) in enumerate(initial))
    faces=Faces(named,{j:base.ports[g] for j,(_,g) in enumerate(initial)},len(data['path']))
    active={}
    seen=set()
    output=[]
    spatial=data['path']
    for i in range(len(initial)+1):
        for gap in range(len(spatial)+1):
            region=faces.spots[i,gap]
            if region in seen:
                continue
            seen.add(region)
            holes=faces.holes[region]
            if not holes:
                continue
            vertex=data['vertex'] if gap==0 else data['edges'][spatial[gap-1]][1]
            if vertex not in active:
                active[vertex]=decide(dict(data,vertex=vertex),dependent=True)['positive_return']
            output.append(dict(row=i,gap=gap,object=vertex,children=holes,dependent_return=active[vertex]))
        if i<len(initial):
            p,g=initial[i]
            s,t=base.ports[g]
            spatial=spatial[:p]+t+spatial[p+len(s):]
    ranks=sorted({face['children'] for face in output if face['dependent_return']})
    return dict(planar_path=path, faces=output, positive_ranks=ranks,maximum=max(ranks,default=0))


def audit():
    # An x->y->x lens has three y-children. Outside it, two x-siblings
    # consist of the lens itself and a stationary scalar, on a nonempty path.
    gates={'B':['x','','fg'],'D':['x','fg',''],'s':['x','',''],'a':['y','',''],
           't':['x','',''],'b':['y','','']}
    row=[(0,'B'),(1,'a'),(1,'a'),(1,'a'),(0,'D'),(0,'s')]
    edges={'f':['x','y'],'g':['y','x'],'z':['x','x']}
    final=[(0,'s'),*row[:-1]]
    data=dict(vertex='x',path='z',edges=edges,gates=gates,initial=row,final=final,rules={})
    for want_x,want_y,expected in [(False,False,[]),(True,False,[2]),(False,True,[3]),(True,True,[2,3])]:
        data['rules']={}
        for yes,x,c in ((want_x,'x','t'),(want_y,'y','b')):
            if yes:
                data['rules'].update({x+'0':[x,[],[(0,c)]],x+'1':[x,[(0,c)],[]]})
        result=profile(data)
        assert result['positive_ranks']==expected and result['planar_path']
    from semistrict_surface_closed_port_group import solve
    for face in result['faces']:
        a,p,x=face['row'],face['gap'],face['object']
        c='t' if x=='x' else 'b'
        placed=row[:a]+[(p,'site')]+row[a:]
        charts=[dict(diagram=placed,slot=a,input=[],output=[(0,c)]),
                dict(diagram=placed,slot=a,input=[(0,c)],output=[])]
        group=solve(dict(data,gates=dict(gates,site=[x,'','']),charts=charts,seams=[()]))
        assert group['free_rank']==face['children']
    moved=[(0,'B'),(1,'a'),(1,'a'),(1,'a'),(0,'D'),(1,'s')]
    assert profile(dict(data,final=moved))['planar_path'] is None
    # Same object in two distinct empty-end gaps. One nonempty program
    # supplies both faces, even though their numbers of children differ.
    same=dict(data,edges={'f':['x','x'],'g':['x','x'],'z':['x','x']},
              gates={g:['x',s,t] for g,(_,s,t) in gates.items()},
              rules={'u':['x',[],[]]})
    assert profile(same)['positive_ranks']==[2,3]
    print('Verified rank spectra empty, {2}, {3}, and {2,3} at reordered written ends, '
          'a blocked change across an anchored wire, and repeated children at distinct face addresses.')


if __name__=='__main__':
    cli=ArgumentParser(description=__doc__)
    cli.add_argument('input',type=Path,nargs='?')
    args=cli.parse_args()
    if args.input:
        print(json.dumps(profile(json.loads(args.input.read_text())),indent=2))
    else:
        audit()
