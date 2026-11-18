from catt import *
from rc2 import *
from emit_agda import emit
# x, y, z, f, f' : x->y, a : f => f', g, g' : y->z, b : g => g'
G = (STAR, STAR, arr(STAR,v(0),v(1)), arr(STAR,v(0),v(1)), None)
G = [STAR, STAR, arr(STAR,v(0),v(1)), arr(STAR,v(0),v(1))]
G.append(arr(arr(STAR,v(0),v(1)), v(2), v(3)))           # a: 4
G += [STAR, arr(STAR,v(1),v(5)), arr(STAR,v(1),v(5))]     # z 5, g 6, g' 7
G.append(arr(arr(STAR,v(1),v(5)), v(6), v(7)))           # b: 8
G = tuple(G); check_ctx(G)
T = comp2(G, 1, comp2(G,0,v(4),v(6)), comp2(G,0,v(3),v(8)))
U = comp2(G, 1, comp2(G,0,v(2),v(8)), comp2(G,0,v(4),v(7)))
print(infer(G,T)==infer(G,U))
K = rc2_full(G, T, U)
print('exchange cell ok')
open('../src/CaTTExp/Generated/ExchangeTwoBigons.agda','w').write(emit('CaTTExp.Generated.ExchangeTwoBigons', G, K, arr(infer(G,T),T,U), 'Theorem A with one exchange move: two side-by-side bigons, built by tools/rc2.py.'))
