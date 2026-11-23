"""Check the nonglobular 3-cell lift and the seam comparisons in Response 28."""
import argparse
from pathlib import Path
from tempfile import TemporaryDirectory

from semistrict_surface_exact_boundary import accepted, rejected, run


SEAMS = """import examples/eh-common

def h = coh [ x{p{a}m{b}q}y{f}z : comp[id(x),comp[p,f]] -> comp[comp[q,f],id(z)] ]
def hh = coh [ x{p{a}m{b}q}y{f{c}g}z : comp[id(x),comp[p,f]] -> comp[comp[q,g],id(z)] ]
def inflate = coh [ x{p{a}m{b}q}y{f}z : h(a,b,f) -> hh(a,b,id(f)) ]
def bridge_source = coh [ x{p{a}q}y{f{b}g}z : comp[id(x),comp[p,f]] -> comp[id(x),comp[q,g]] ]
def bridge_target = coh [ x{p{a}q}y{f{b}g}z : comp[comp[p,f],id(z)] -> comp[comp[q,g],id(z)] ]
def first [[l,a,r,s,b,t],[u,c,v]] = hh(comp[l,a,r],comp[s,b,t],comp[u,c,v])
def second [[l,a,r,s,b,t],[u,c,v]] = comp[bridge_source(l,u),hh(comp[a,comp[r,s]],b,c),bridge_target(t,v)]
def rect = coh [ [[l,a,r,s,b,t],[u,c,v]] : first(l,a,r,s,b,t,u,c,v) -> second(l,a,r,s,b,t,u,c,v) ]
def rect_inv = coh [ [[l,a,r,s,b,t],[u,c,v]] : second(l,a,r,s,b,t,u,c,v) -> first(l,a,r,s,b,t,u,c,v) ]

def cancel = coh [ x{f}y : comp[unitor_l_inv(f),unitor_l(f)] -> id(f) ]
def change_top = coh [ {f{m{e}n}g{b}q}{u{c}v} : hh(m,b,c) -> hh(n,b,c) ]
"""

CONTEXT = ('(x : *) (p : x -> x) (q : x -> x) (m : x -> x) '
           '(a : comp[p,q] -> m) (b : m -> comp[q,p]) (f : x -> x)')
ARGS = '(x,p,q,m,a,b,f)'
CONNECTORS = ('(unitor_l(comp[p,q]),a,unitor_l_inv(m),unitor_l(m),b,'
              'unitor_r_inv(comp[q,p]),unitor_l(f),id(f),unitor_l_inv(f))')
OLD = 'old' + ARGS
ADJUSTED = 'adjusted' + ARGS
EXTENDED = f'{CONTEXT} (z : {ADJUSTED} -> {ADJUSTED})'
FIT = 'fit(x,p,q,m,a,b,f,z)'

FITTED = f"""import Seams
def old {CONTEXT} = first{CONNECTORS}
def adjusted {CONTEXT} = second{CONNECTORS}
def forward {CONTEXT} : {OLD} -> {ADJUSTED} = rect{CONNECTORS}
def backward {CONTEXT} : {ADJUSTED} -> {OLD} = rect_inv{CONNECTORS}
def fit {EXTENDED} : {OLD} -> {OLD} = comp[forward{ARGS},z,backward{ARGS}]
"""

CLASSES = {
    'rectangle_forward': ('forward' + ARGS, 'id(h(a,b,f))'),
    'rectangle_backward': ('backward' + ARGS, 'id(h(a,b,f))'),
    'interior_cancel': ('cancel(m)', 'id(id(m))'),
    'stationary': ('inflate(a,b,f)', 'id(h(a,b,f))'),
    'top_move': ('change_top(id(a),b,id(f))', 'id(h(a,b,f))'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path, help='built checkout of Rice’s catt-strict')
    checkout = parser.parse_args().checkout.resolve()
    binary = checkout / 'target/release/catt_strict'
    with TemporaryDirectory() as folder:
        directory = Path(folder)
        (directory / 'examples').symlink_to(checkout / 'examples', target_is_directory=True)
        (directory / 'Seams.catt').write_text(SEAMS)
        (directory / 'Fitted.catt').write_text(FITTED)
        claims = [f'def {name} {CONTEXT} : {term} -> {target} = id({term})'
                  for name, (term, target) in CLASSES.items()]
        claims.append(f'def rehydrated {EXTENDED} : {FIT} -> z = id(z)')
        (directory / 'Classes.catt').write_text('\n'.join(['import Fitted', *claims, '']))
        (directory / 'Premature.catt').write_text(
            f'import Fitted\ndef direct {EXTENDED} : {OLD} -> {OLD} = z\n')
        (directory / 'OtherClass.catt').write_text(
            f'import Fitted\ndef different {EXTENDED} : {FIT} -> id({OLD}) = id({FIT})\n')
        accepted(run(binary, directory, 'Fitted.catt'), 'Fitted.catt', ['forward', 'backward', 'fit'])
        rejected(run(binary, directory, 'Premature.catt'), 'Premature.catt', 'direct')
        print('Weak CaTT accepted both comparisons and the fitted generator, and rejected direct use.')
        for mode in ('--su', '--sua'):
            accepted(run(binary, directory, 'Classes.catt', [mode]), 'Classes.catt',
                     [*CLASSES, 'rehydrated'])
            rejected(run(binary, directory, 'OtherClass.catt', [mode]), 'OtherClass.catt', 'different')
            print(f'{mode} verified all six classes and distinguished the generator from the identity.')


if __name__ == '__main__':
    main()
