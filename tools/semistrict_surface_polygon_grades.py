"""Bound positive polygon and cube steps on a fixed incidence diagram by two integer grades."""
from semistrict_surface_transfer_cables import wire_weights


def network(source,actions,ids,arities,swap):
    live = [(-1,i) for i in range(len(source))]
    graph,reading = {},[]
    for n,i in actions:
        if n==swap:
            left,right = live[i:i+2]
            reading.append((i,None))
            live[i:i+2] = right,left
        else:
            a,b = arities[n]
            ins = tuple(live[i:i+a])
            p = ids.setdefault((n,ins),len(ids))
            outs = tuple((p,j) for j in range(b))
            graph[p] = n,ins,outs
            live[i:i+a] = outs
            reading.append((i,p))
    return live,graph,reading


def measure(widths,weights,graph,reading):
    widths = list(widths)
    length = height = crossing_grade = 0
    for i,p in reading:
        prefix = sum(widths[:i])
        if p is None:
            a,b = widths[i:i+2]
            length += a*b
            # Sum of the zero-based crossing indices in the block shuffle.
            crossing_grade += prefix*a*b+a*b*(a+b-2)//2
            widths[i:i+2] = b,a
        else:
            _,ins,outs = graph[p]
            height += prefix
            widths[i:i+len(ins)] = [weights[e] for e in outs]
    return length,height,crossing_grade


def resolution(source,faces,arities,swap):
    ids = {}
    a,b = [network(source,face,ids,arities,swap) for face in faces]
    if a[:2]!=b[:2]:
        return None
    _,graph,_ = a
    initial = [(-1,i) for i in range(len(source))]
    edges = initial+[e for _,_,outs in graph.values() for e in outs]
    weights = wire_weights(edges,graph,graph)
    widths = [weights[e] for e in initial]
    return widths,weights,graph,(a[2],b[2])


def bound(model,source,first,second):
    arities = [(len(r.source),len(r.target)) for r in model.pres.rules]
    resolved = resolution(source,(first,second),arities,'swap')
    if resolved is None:
        return None
    widths,weights,graph,readings = resolved
    (length,h,j),(target,h1,j1) = [measure(widths,weights,graph,data) for data in readings]
    if target!=length or h1<h or j1<j:
        return None
    return dict(cable_width=sum(widths),weighted_crossings=length,
                prism_budget=h1-h,cube_budget=j1-j)


def checks():
    from itertools import product
    from semistrict_surface_signed_width_two import Movies,Presentation,Rule
    from semistrict_surface_raw_movie_graph import raw_compare,raw_updates,read
    from semistrict_surface_polygon_cabling import rectangle
    # Relative orientation and grade are independent of all exterior wires.
    block_tests = 0
    for a,b,c in product(range(1,7),repeat=3):
        def score(word):
            sizes = [a,b,c]
            letters = []
            for i in word:
                x,y = sizes[i:i+2]
                letters.extend(rectangle(sum(sizes[:i]),x,y))
                sizes[i:i+2] = y,x
            return sum(letters),len(letters)
        l,n = score((0,1,0))
        r,m = score((1,0,1))
        assert l+a*b*c==r and n==m
        block_tests += 1
    s = ((0,'a'),)
    rules = [Rule('',s,s*2),Rule('',s*2,s),Rule('',s,s)]
    model = Movies(Presentation({}, {'a':('','')},rules,{'a':0}),'')
    source = s*3
    faces = []
    todo = [(source,(),0,0)]
    while todo:
        h,word,n,c = todo.pop()
        faces.append(word)
        if n>=2 and c>=3:
            continue
        for i in range(len(h)):
            if c<3 and i+1<len(h):
                todo.append((h,word+(('swap',i),),n,c+1))
            if n<2:
                for rid in range(len(rules)):
                    result = model.named(h,rid,i)
                    if result:
                        todo.append((result[0],word+((rid,i),),n+1,c))
    verified = changing = 0
    for word in faces[::17]:
        histories,windows = read(model,source,word)
        for other in raw_updates(model,word,histories,windows,2):
            result = bound(model,source,word,other)
            assert result is not None
            directed = result['cube_budget']+result['prism_budget']
            assert bool(directed)==(bound(model,source,other,word) is None)
            changing += bool(directed)
            verified += 1
    # On the scalar base the signed history group is infinite. Every raw answer
    # at these three-strand boundaries still terminates by the integer grades.
    crosses = lambda w:tuple(('swap',i) for i in w)
    a = crosses((0,1,0))+((0,0),)
    b = crosses((1,0,1))+((0,0),)
    assert raw_compare(model,source,a,b)['raw']
    assert not raw_compare(model,source,b,a)['raw']
    # Repeated splits and joins share one connected chain of wire occurrences.
    chain = ((0,0),(1,0))*60
    score = bound(model,s,chain,chain)
    assert score['cable_width']==181
    return dict(cube_sizes=block_tests,literal_updates=verified,positive_grade_updates=changing,
                chain_polygons=len(chain),chain_resolution_width=score['cable_width'])


if __name__=='__main__':
    import json
    print(json.dumps(checks()))
