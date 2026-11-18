#!/usr/bin/env python3
"""Directed kernel-four computations over the exact finite r6 three-graph.

No unproved equality of paths is used. Model D consists only of the requested
right-region-first => left-region-first elementary interchange, recursively
expanded through the six r6 repair equations. Model DC additionally assumes
the stated inner-cube Coxeter cell, leftmost-first => rightmost-first.
All word intervals below are half-open, zero-based intervals.
"""
from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import combinations
import argparse
import json
import r6_endpoint_lifts_check as m


def interval(e):
    differing = [i for i,(a,b) in enumerate(zip(e[0],e[1])) if a != b]
    return min(differing), max(differing)+1


def setup():
    vertices, original, edges, all_edges, labels, repairs = m.make_graph()
    out = defaultdict(list)
    all_out = defaultdict(list)
    for e in sorted(edges): out[e[0]].append(e)
    for e in sorted(all_edges): all_out[e[0]].append(e)
    @lru_cache(None)
    def expand(e):
        if e in edges: return (e,)
        return tuple(x for f in repairs[e] for x in expand(f))
    return vertices, original, edges, all_edges, labels, repairs, out, all_out, expand


def disjoint_records(vertices, all_edges, all_out, labels, expand):
    by_routes = {}
    for w in sorted(vertices):
        for a,b in combinations(all_out[w],2):
            if interval(a)[0] > interval(b)[0]: a,b = b,a
            ai,aj = interval(a); bi,bj = interval(b)
            if aj > bi: continue
            target = a[1][:bi] + b[1][bi:bj] + a[1][bj:]
            left_after_right = (b[1],target,a[2])
            right_after_left = (a[1],target,b[2])
            assert left_after_right in all_edges, (a,b,left_after_right)
            assert right_after_left in all_edges, (a,b,right_after_left)
            neg = expand(b)+expand(left_after_right)
            pos = expand(a)+expand(right_after_left)
            assert neg[0][0] == pos[0][0] == w
            assert neg[-1][1] == pos[-1][1] == target
            assert m.signature(m.route_chain(neg,labels)) == m.signature(m.route_chain(pos,labels))
            r = dict(kind='disjoint',source=w,target=target,left=a,right=b,
                     left_interval=(ai,aj),right_interval=(bi,bj),
                     negative=neg,positive=pos,
                     expanded=any(e not in expand(e) for e in (a,b,left_after_right,right_after_left)))
            by_routes.setdefault((neg,pos),r)
    return list(by_routes.values())


def coxeter_records(vertices, edges, labels):
    by_end = {e[:2]:e for e in edges if e[2]=='I'}
    result=[]
    for w in sorted(vertices):
        for i in range(len(w)-2):
            if set(w[i:i+3]) != set('abc'): continue
            def make(places):
                route=[]; s=w
                for j in places:
                    j+=i
                    t=s[:j]+s[j+1]+s[j]+s[j+2:]
                    e=by_end.get((s,t))
                    if e is None: return None
                    route.append(e);s=t
                return tuple(route)
            neg,pos=make((0,1,0)),make((1,0,1))
            if neg is not None and pos is not None:
                assert neg[-1][1]==pos[-1][1]
                assert not m.route_chain(neg,labels) and not m.route_chain(pos,labels)
                result.append(dict(kind='coxeter',source=w,target=neg[-1][1],
                                   interval=(i,i+3),negative=neg,positive=pos))
    assert len(result)==8
    return result


def naturality_records(vertices, all_edges, labels, expand):
    """Conditional Gray naturality with one independent two-letter.

    The two-letter has hom1 degree one; the three-operation has hom1 degree
    two. The (2,1) tensor cell points I-first => operation-first; (1,2)
    points operation-first => I-first. These are additional four-data.
    """
    def support(letter):
        return {m.UPDATES[letter]} if letter in m.UPDATES else set(m.CROSSES[letter])
    def slide(word,position,destination):
        route=[]
        while position!=destination:
            j=position if position<destination else position-1
            target=word[:j]+word[j+1]+word[j]+word[j+2:]
            e=(word,target,'I')
            if e not in all_edges: return None
            route.append(e);word=target
            position += 1 if position<destination else -1
        return tuple(route)
    result={}
    for alpha in sorted(all_edges):
        w,t,_=alpha;i,j=interval(alpha)
        region=set().union(*(support(x) for x in w[i:j]))
        for position,destination,degree_pair in [(i-1,j-1,(2,1)),(j,i,(1,2))]:
            if position<0 or position>=len(w):continue
            z=w[position]
            if support(z)&region:continue
            before=slide(w,position,destination)
            after=slide(t,position,destination)
            if before is None or after is None:continue
            residual=(before[-1][1],after[-1][1],alpha[2])
            assert residual in all_edges,(alpha,z,residual)
            i_first=before+expand(residual)
            alpha_first=expand(alpha)+after
            neg,pos=(i_first,alpha_first) if degree_pair==(2,1) else (alpha_first,i_first)
            assert neg[0][0]==pos[0][0]==w
            assert neg[-1][1]==pos[-1][1]
            assert m.signature(m.route_chain(neg,labels))==m.signature(m.route_chain(pos,labels))
            result.setdefault((neg,pos),dict(kind='naturality',source=w,target=neg[-1][1],
                    alpha=alpha,independent_letter=z,degree_pair=degree_pair,
                    alpha_interval=(i,j),letter_position=position,
                    negative=neg,positive=pos))
    return list(result.values())


def all_paths(vertices,out):
    result=[]
    def visit(start,w,p):
        result.append((start,w,p))
        for e in out[w]: visit(start,e[1],p+(e,))
    for w in sorted(vertices): visit(w,w,())
    assert len(result)==40412
    return result


def closure_graph(paths,relations):
    index={(s,p):i for i,(s,t,p) in enumerate(paths)}
    patterns=defaultdict(list)
    for k,r in enumerate(relations): patterns[r['negative'][0]].append((tuple(r['negative']),tuple(r['positive']),k))
    adj=defaultdict(dict)
    parent=list(range(len(paths)))
    def root(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    for i,(s,t,p) in enumerate(paths):
        for cut,e in enumerate(p):
            for neg,pos,k in patterns[e]:
                if p[cut:cut+len(neg)]!=neg: continue
                q=p[:cut]+pos+p[cut+len(neg):]
                j=index[s,q]
                assert paths[j][1]==t
                adj[i].setdefault(j,(k,cut))
                parent[root(i)]=root(j)
    return index,adj,[root(i) for i in range(len(paths))]


def fibre_statistics(paths,labels,components,adj):
    fibres=defaultdict(list)
    for i,(s,t,p) in enumerate(paths):
        fibres[s,t,m.signature(m.route_chain(p,labels))].append(i)
    disconnected=[]
    for key,ids in fibres.items():
        count=len({components[i] for i in ids})
        if count>1: disconnected.append((key,ids,count))
    def minimal_pair(ids):
        i=min(ids,key=lambda i:(len(paths[i][2]),paths[i][2]))
        j=min((j for j in ids if components[j]!=components[i]),key=lambda j:(len(paths[j][2]),paths[j][2]))
        return i,j
    disconnected.sort(key=lambda x:(
        sum(len(paths[i][2]) for i in minimal_pair(x[1])),
        max(len(paths[i][2]) for i in minimal_pair(x[1])),x[0]))
    minimal=None
    if disconnected:
        key,ids,count=disconnected[0]
        i,j=minimal_pair(ids)
        minimal=dict(source=key[0],target=key[1],chain=m.chain_text(key[2]),
                     negative=paths[i][2],positive=paths[j][2],fibre_size=len(ids),components=count,
                     minimal_total_edges=len(paths[i][2])+len(paths[j][2]))
    return dict(path_count=len(paths),nonidentity_path_count=sum(bool(p) for s,t,p in paths),
                relation_instances=sum(len(x) for x in adj.values()),
                fibres=len(fibres),disconnected_fibres=len(disconnected),
                weak_components=len(set(components)),
                minimal_disconnected=minimal),fibres


def check_acyclic(adj,n):
    indeg=[0]*n
    for targets in adj.values():
        for j in targets:indeg[j]+=1
    todo=deque(i for i,d in enumerate(indeg) if not d);count=0
    while todo:
        i=todo.popleft();count+=1
        for j in adj.get(i,{}):
            indeg[j]-=1
            if not indeg[j]:todo.append(j)
    assert count==n,'The directed four-comparison graph has a cycle'


def sink_statistics(paths,out,labels,components):
    result=[]
    for target in sorted(w for w in out if not out[w]):
        ids=[i for i,(s,t,p) in enumerate(paths) if s==m.SOURCE and t==target]
        result.append(dict(target=target,paths=len(ids),
                           q3_chains=len({m.signature(m.route_chain(paths[i][2],labels)) for i in ids}),
                           weak_components=len({components[i] for i in ids})))
    assert len(result)==10
    return result


def reachability(adj,n):
    indeg=[0]*n
    for i,targets in adj.items():
        for j in targets: indeg[j]+=1
    todo=deque(i for i,d in enumerate(indeg) if not d)
    order=[]
    while todo:
        i=todo.popleft();order.append(i)
        for j in adj.get(i,{}):
            indeg[j]-=1
            if not indeg[j]: todo.append(j)
    assert len(order)==n, 'A directed four-cycle was found'
    reachable=[0]*n
    for i in reversed(order):
        bits=1<<i
        for j in adj.get(i,{}): bits |= reachable[j]
        reachable[i]=bits
    return reachable


def find_walk(adj,source,target):
    if source==target: return []
    previous={source:None};todo=deque([source])
    while todo:
        i=todo.popleft()
        for j,detail in sorted(adj.get(i,{}).items()):
            if j in previous: continue
            previous[j]=(i,detail)
            if j==target:
                result=[]
                while j!=source:
                    i,detail=previous[j]
                    result.append(dict(source=i,target=j,relation=detail[0],cut=detail[1]))
                    j=i
                return list(reversed(result))
            todo.append(j)
    return None


def cancellation_fork(paths,index,adj,components):
    p=(('bcrqap','brcqap','T'),('brcqap','bracqp','h_q'))
    q=(('bcrqap','bacrqp','mu'),('bacrqp','barcqp','T'),('barcqp','bracqp','I'))
    gamma=('bracqp','brcaqp','I')
    r=(('bcrqap','bacrqp','mu'),('bacrqp','bcarqp','I'),
       ('bcarqp','bcraqp','I'),('bcraqp','brcaqp','T'))
    pi,qi,ri,pg,qg=(index['bcrqap',z] for z in (p,q,r,p+(gamma,),q+(gamma,)))
    assert components[pi]!=components[qi]
    assert components[pg]==components[qg]
    assert not adj.get(pg) and not adj.get(qg)
    left,right=find_walk(adj,ri,pg),find_walk(adj,ri,qg)
    assert left is not None and right is not None and len(left)==len(right)==1
    return dict(P=p,Q=q,gamma=gamma,R=r,
                to_P_gamma=left,to_Q_gamma=right,
                terminal_P_gamma=True,terminal_Q_gamma=True)


def selected_padding(paths,index,adj,components,labels,vertices,edges,all_edges,repairs,cert):
    # Only raw S=>T routes can be the boundary of these selected four-lifts.
    keep=[i for i,(s,t,p) in enumerate(paths) if s==m.SOURCE and t==m.TARGET]
    old_to_new={old:new for new,old in enumerate(keep)}
    small_paths=[paths[i] for i in keep]
    small_adj={old_to_new[i]:{old_to_new[j]:v for j,v in targets.items()}
               for i,targets in adj.items() if i in old_to_new}
    assert all(j in old_to_new for i,targets in adj.items() if i in old_to_new for j in targets)
    reachable=reachability(small_adj,len(keep))
    small_index={(s,p):i for i,(s,t,p) in enumerate(small_paths)}
    ancestors=set(cert['ancestors'])
    contexts=m.prescribed_contexts(vertices,edges,all_edges,labels,repairs,ancestors)
    by_first=defaultdict(list)
    for k,c in enumerate(contexts): by_first[tuple(c['negative'][0])].append((k,c))
    w_instances=defaultdict(list)
    for i,(s,t,p) in enumerate(small_paths):
        for cut,e in enumerate(p):
            for k,c in by_first[e]:
                neg,pos=tuple(c['negative']),tuple(c['positive'])
                if p[cut:cut+len(neg)]!=neg: continue
                q=p[:cut]+pos+p[cut+len(neg):]
                j=small_index[s,q]
                w_instances[c['tensor_label']].append((i,j,k,cut))
    result=[]
    for a,b,k in cert['selected4']:
        ap=tuple(tuple(e) for e in cert['paths3'][a]['path'])
        bp=tuple(tuple(e) for e in cert['paths3'][b]['path'])
        ai,bi=small_index[m.SOURCE,ap],small_index[m.SOURCE,bp]
        directed=[];undirected=[]
        for u,v,c,cut in w_instances[cert['labels4'][k]]:
            if (reachable[ai]>>u)&1 and (reachable[v]>>bi)&1:
                pre=find_walk(small_adj,ai,u);post=find_walk(small_adj,v,bi)
                directed.append(dict(w_source=u,w_target=v,context_index=c,cut=cut,
                                     pre=pre,post=post,steps=len(pre)+len(post)))
            if components[keep[ai]]==components[keep[u]] and components[keep[v]]==components[keep[bi]]:
                undirected.append(dict(w_source=u,w_target=v,context_index=c,cut=cut))
        directed.sort(key=lambda r:(r['steps'],r['context_index'],r['cut'],r['w_source'],r['w_target']))
        result.append(dict(selected=(a,b,k),tensor_label=cert['labels4'][k],
                           status='fresh' if [a,b,k] in cert['fresh4'] else 'reused',
                           source=ai,target=bi,directed_count=len(directed),
                           undirected_count=len(undirected),
                           best=directed[0] if directed else None,
                           undirected_example=undirected[0] if undirected else None))
    fibre_groups=defaultdict(list)
    for i,(s,t,p) in enumerate(small_paths): fibre_groups[m.signature(m.route_chain(p,labels))].append(i)
    fibre_details=[]
    for sig,ids in sorted(fibre_groups.items()):
        minimal=[i for i in ids if not any(i!=j and ((reachable[j]>>i)&1) for j in ids)]
        maximal=[i for i in ids if not any(i!=j and ((reachable[i]>>j)&1) for j in ids)]
        fibre_details.append(dict(chain=m.chain_text(sig),paths=len(ids),components=len({components[keep[i]] for i in ids}),
                                  minimal=len(minimal),maximal=len(maximal)))
    return result, dict(paths=[p for s,t,p in small_paths],adjacency={i:dict(v) for i,v in small_adj.items()},
                        w_instances=dict(w_instances),contexts=contexts,fibres=fibre_details)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--json',default='r7_kernel4_certificate.json');args=parser.parse_args()
    vertices,original,edges,all_edges,labels,repairs,out,all_out,expand=setup()
    ds=disjoint_records(vertices,all_edges,all_out,labels,expand)
    cs=coxeter_records(vertices,edges,labels)
    ns=naturality_records(vertices,all_edges,labels,expand)
    route_key=lambda r:(r['negative'],r['positive'])
    assert set(map(route_key,cs)) <= set(map(route_key,ns))
    print('Disjoint records',len(ds),'expanded',sum(r['expanded'] for r in ds))
    print('Coxeter records',len(cs))
    print('Naturality records',len(ns))
    paths=all_paths(vertices,out)
    with open('r6_endpoint_lifts_certificate.json') as f: cert=json.load(f)
    data=dict(disjoint=ds,coxeter=cs,naturality=ns,models={})
    for name,relations in [('D',ds),('DC',ds+cs),('DCN',ds+cs+ns)]:
        index,adj,components=closure_graph(paths,relations)
        check_acyclic(adj,len(paths))
        stats,fibres=fibre_statistics(paths,labels,components,adj)
        stats['directed_acyclic']=True
        stats['sinks_from_source']=sink_statistics(paths,out,labels,components)
        padding,details=selected_padding(paths,index,adj,components,labels,vertices,edges,all_edges,repairs,cert)
        data['models'][name]=dict(statistics=stats,padding=padding,**details)
        if name=='DCN':
            data['minimal_cancellation_fork']=cancellation_fork(paths,index,adj,components)
        print(name,json.dumps(stats))
        print(name,'Padded fresh',[(r['selected'],r['best']['steps']) for r in padding if r['status']=='fresh' and r['best']])
        print(name,'Unpadded fresh',[(r['selected'],r['undirected_count']) for r in padding if r['status']=='fresh' and not r['best']])
        print(name,'Top weak components',sum(r['components'] for r in details['fibres']))
    with open(args.json,'w') as f:json.dump(data,f,indent=2)

if __name__=='__main__':main()
