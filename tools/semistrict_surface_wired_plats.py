"""Compile a signed bridge plat into the two-exception ordinary presentation.

Input is {pairs,braid,word} in the plat probe format. Use --movie for the
expanded gate rows and signed seams, or omit a file to replay the audit.
"""
from argparse import ArgumentParser
from itertools import permutations,product
import json
from pathlib import Path

from semistrict_surface_component_braids import restrict
from semistrict_surface_gate_forests import cable
from semistrict_surface_history_group import exchange
from semistrict_surface_movie_spine import expanded,presentation as spine
from semistrict_surface_plat_probes import decide,presentation,word_value
from semistrict_surface_probe_generators import cut_bound
from semistrict_surface_spherical_relations import simplify


# A,B,F are birth gates, D,G death gates. H,J,K are unary, M a merge and S a split.
ports = {'A':('','f'),'B':('','f'),'F':('','f'),'D':('f',''),'G':('f',''),
         'H':('f','f'),'J':('f','f'),'K':('f','f'),'M':('ff','f'),'S':('f','ff')}
cap = [(0,'','AD','',''),(0,'A','BH','','f'),(1,'H','JK','f','f'),
       (1,'J','FM','f','f'),(3,'K','SG','f','f'),(2,'MS','','ff','ff')]


def compile_plat(pairs,braid,certificate=False):
    presentation(pairs,braid)  # Validate strand indices even for empty words.
    gates,charts,seams = {},[],[]
    rows,pending = (),[]
    selected = set()
    def switch(letter):
        nonlocal rows
        moved = exchange(rows,letter,{g:(s,t) for g,(_,s,t) in gates.items()})
        if moved is None:
            raise ValueError('illegal gate exchange in compiled seam')
        rows = moved
        pending.append(letter)
    def change(slot,source,target,s,t):
        nonlocal rows,pending
        assert rows[slot:slot+len(source)]==source
        marker = 'site'+str(len(charts))
        gates[marker] = ['x',s,t]
        prefix,suffix = rows[:slot],rows[slot+len(source):]
        charts.append(dict(diagram=prefix+((0,marker),)+suffix,slot=slot,
                           input=source,output=target,loop=[]))
        if len(charts)>1:
            seams.append(pending)
        rows = prefix+target+suffix
        pending = []
    def move_mark(slot,to_death):
        old_b,old_d = rows[slot:slot+2]
        b,h,d = (name+'x'+str(len(charts)) for name in 'BHD')
        for colour,name in [('B',b),('H',h),('D',d)]:
            gates[name] = ['x',*ports[colour]]
        if to_death:
            assert old_b[1] in selected
            change(slot,(old_b,),((0,b),(0,h)),'','f')
            change(slot+1,((0,h),old_d),((0,d),),'f','')
        else:
            assert old_d[1] in selected
            change(slot+1,(old_d,),((0,h),(0,d)),'f','')
            change(slot,(old_b,(0,h)),((0,b),),'','f')
        selected.update((h,d if to_death else b))
    def run_cap(offset,reverse):
        names = {k:k+str(len(charts)) for k in ports}
        if reverse:
            # The two interval packets at this end may belong to different births.
            for slot,required in [(offset,0),(offset+2,1)]:
                if rows[slot+required][1] not in selected:
                    move_mark(slot,bool(required))
            for k,(_,g) in zip('BGFD',rows[offset:offset+4],strict=True):
                assert tuple(gates[g][1:])==ports[k]
                names[k] = g
        for k,g in names.items():
            gates[g] = ['x',*ports[k]]
        if reverse:
            switch(offset+2)
        selected.update(names[k] for k in 'ABD')
        for slot,old,new,s,t in reversed(cap) if reverse else cap:
            slot += offset
            # The extra birth enters on the left, the extra death leaves on
            # the right. The old end gates then lie in different intervals.
            source = tuple((int(k=='G'),names[k]) for k in old)
            target = tuple((int(k=='G'),names[k]) for k in new)
            if reverse:
                source,target = target,source
            change(slot,source,target,s,t)
        if not reverse:
            switch(-(offset+2))
    for _ in range(pairs):
        run_cap(len(rows),False)
    for letter in cable(braid,[2]*(2*pairs)):
        switch(letter)
    for _ in range(pairs):
        run_cap(0,True)
    assert not rows and not pending
    data = dict(vertex='x',path='',edges={'f':['x','x']},gates=gates,charts=charts,seams=seams)
    events,word = [],[]
    for i,c in enumerate(charts):
        sizes = tuple(sum(g in selected for _,g in c[side]) for side in ('input','output'))
        if sizes not in [(0,0),(1,1)]:
            events.append(sizes)
        if i<len(seams):
            row = expanded(c,'output')
            word.extend(restrict(len(row),seams[i],{j for j,(_,g) in enumerate(row) if g in selected}))
    assert events==[(0,2)]*pairs+[(2,0)]*pairs and list(braid)==word
    if certificate:
        return dict(selected=sorted(selected),events=events,braid=word)
    return data


def hom_count(rank,relations):
    identity = (0,1,2)
    return sum(all(word_value(w,images,3)==identity for w in relations)
               for images in product(permutations(identity),repeat=rank))


def audit():
    switches = 0
    for length in range(4):
        for braid in product((1,-1,2,-2,3,-3),repeat=length):
            compile_plat(2,braid,True)
            switches += 1
    print(f'Recovered the original marked cap pairs and exact braid on {switches} four-strand inputs.')
    for pairs,braid in [(1,[]),(2,[]),(2,[2]),(2,[2,2]),(2,[2,2,2]),
                        (2,[-2,-2,-2]),(3,[2,-4,3,1,-2])]:
        data = compile_plat(pairs,braid)
        assert cut_bound(data)['generator_bound']==pairs
        cx = spine(data)
        rank,relations,_ = simplify(cx['generators'],cx['faces'])
        compact = presentation(pairs,braid)
        # Count finite representations from the whole wired spine, independent
        # of the cap reduction and of the marked meridian word decision.
        actual = hom_count(rank,relations)
        assert actual==hom_count(pairs,compact)
        if pairs==2 and len(braid) in (2,3):
            test = decide(dict(pairs=2,braid=braid,word=[1,2,-1,-2]))
            assert test['raw_filler']==(len(braid)==2)
            assert actual==(18 if len(braid)==2 else 12)
        print(f'{pairs} bridges, braid {braid}: {len(data["charts"])} uses, {actual} homomorphisms to S3')


def typed(directory):
    from catt import comp2,infer,src,tgt
    from emit_agda import Emitter
    from semistrict_surface_box_exceptions import rules
    from semistrict_surface_box_ports import b,beside,d,fixed_context,h,m,one,raw_hom,raw_row,s
    from semistrict_surface_directed_power_queries import row_fit

    ctx,read,rule,_ = fixed_context(rules)
    enter,leave = read(beside(b,one)),read(beside(one,d))
    def stack(*cells):
        return raw_row(ctx,1,cells)
    def seq(*cells):
        return raw_row(ctx,2,cells)
    def cap_term(back):
        join = rule['join-left-unit-to-h',not back]
        fork = rule['fork-right-unit-to-h',not back]
        prepared = stack(stack(enter,read(m)),stack(read(s),leave))
        exposed = stack(enter,stack(read(m),read(s)),leave)
        steps = [rule['vertical',not back],stack(join,read(h)),stack(stack(enter,read(m)),fork),
                 row_fit(ctx,exposed,prepared) if back else row_fit(ctx,prepared,exposed),
                 stack(enter,rule['wire-pair',not back],leave)]
        middle = seq(*(steps[::-1] if back else steps))
        outer = [rule['empty-seed',back],comp2(ctx,1,rule['leaf-b',back],read(d)),
                 stack(read(b),middle,read(d))]
        return seq(*(outer[::-1] if back else outer))
    birth,death = cap_term(False),cap_term(True)
    blank,two = src(ctx,birth),tgt(ctx,birth)
    assert infer(ctx,death)==raw_hom(ctx,two,blank)
    left = stack(rule['leaf-b',False],read(d))
    right = stack(read(b),rule['leaf-d',True])
    transfer = seq(left,row_fit(ctx,tgt(ctx,left),src(ctx,right)),right)
    interval = stack(read(b),read(d))
    assert infer(ctx,transfer)==raw_hom(ctx,interval,interval)
    if directory:
        emitter = Emitter()
        emitter.check_type('birthOfTwoWiredIntervals',ctx,birth,raw_hom(ctx,blank,two))
        emitter.check_type('consumeTwoWiredIntervals',ctx,death,raw_hom(ctx,two,blank))
        emitter.check_type('transferMarkAlongInterval',ctx,transfer,raw_hom(ctx,interval,interval))
        (directory/'WiredPlatCaps.agda').write_text(emitter.module('WiredPlatCaps',__doc__.splitlines()[0]))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?')
    parser.add_argument('--movie',action='store_true')
    parser.add_argument('--selection',action='store_true')
    parser.add_argument('--agda-dir',type=Path)
    args = parser.parse_args()
    if args.input:
        query = json.loads(args.input.read_text())
        d = compile_plat(query['pairs'],query['braid'])
        if args.selection:
            result = compile_plat(query['pairs'],query['braid'],True)
        elif args.movie:
            result = d
        else:
            if 'sphere_degree' in query:
                from semistrict_surface_probe_spheres import plat
                answer = plat(query)
            else:
                answer = decide(query)
            result = dict(cut_bound=cut_bound(d)['generator_bound'],**answer)
        print(json.dumps(result,indent=2))
    else:
        audit()
        typed(args.agda_dir)
