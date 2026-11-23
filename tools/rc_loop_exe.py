#!/usr/bin/env python3
"""rc_loop with a compiled driver.

Same rounds, tables and trust model as tools/rc_loop.py (every answer still
goes through the certified table check), but the `misses` expression is
evaluated by a program compiled with Agda's GHC backend (MAlonzo) instead of
Agda's type-checking-time normalizer, which keeps no sharing and can take
hours on large cone constructions (Horiz3). The program prints the list of
`Maybe Query` in the syntax agda_bridge.parse reads.

Usage: as rc_loop.py:
  CATT_SRC=src python3 tools/rc_loop_exe.py TABLE "EXPR" IMPORTS...
EXPR must have type List (Maybe Query) (ConeRC's Query) and may use TBL.
Set RC_WORKDIR for the build directory (the MAlonzo cache lives there).
"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rc_loop as L
import agda_bridge as B

PRINTER = r'''
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String; primShowNat; primStringToList; primStringFromList)
open import Agda.Builtin.Char using (Char)
open import CaTTExp.ConeRC using (Query)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}

DL : Set
DL = List Char → List Char

str : String → DL
str s rest = app (primStringToList s) rest
  where
  app : List Char → List Char → List Char
  app [] r = r
  app (c ∷ cs) r = c ∷ app cs r

_⊕_ : DL → DL → DL
(f ⊕ g) r = f (g r)
infixr 5 _⊕_

par : DL → DL
par d = str "(" ⊕ d ⊕ str ")"

-- Applications are printed bare where agda_bridge.parse expects an
-- application (list elements, after ▸ and ,ₛ, tuple components) and
-- parenthesized as arguments, as Agda prints normal forms.
mutual
  pTy : Ty → DL
  pTy ⋆ = str "⋆"
  pTy (arr A s t) = str "arr " ⊕ par (pTy A) ⊕ str " " ⊕ par (pTm s) ⊕ str " " ⊕ par (pTm t)

  pTm : Tm → DL
  pTm (var n) = str "var " ⊕ str (primShowNat n)
  pTm (coh G A σ) = str "coh " ⊕ par (pCtx G) ⊕ str " " ⊕ par (pTy A) ⊕ str " " ⊕ par (pSub σ)
  pTm _ = str "cst"

  pCtx : Ctx → DL
  pCtx ε = str "ε"
  pCtx (G ▸ A) = pCtx G ⊕ str " ▸ " ⊕ pTy A

  pSub : Sub → DL
  pSub ⟨⟩ = str "⟨⟩"
  pSub (σ ,ₛ t) = pSub σ ⊕ str " ,ₛ " ⊕ pTm t

pQ : Maybe Query → DL
pQ nothing = str "nothing"
pQ (just (G , A , t , u)) =
  str "just " ⊕ par (pCtx G ⊕ str " , " ⊕ pTy A ⊕ str " , " ⊕ pTm t ⊕ str " , " ⊕ pTm u)

pL : List (Maybe Query) → DL
pL [] = str "[]"
pL (q ∷ qs) = pQ q ⊕ str " ∷ " ⊕ pL qs

main : IO ⊤
main = putStrLn (primStringFromList (pL misses []))
'''

def driver(path, table, expr, imports):
    lines = ['module RCLoopDriver where', '',
             'open import CaTTExp.Prelude', 'open import CaTTExp.Pure hiding (build)',
             'import CaTTExp.Generated.%s as T' % table]
    lines += ['open import %s' % m for m in imports]
    lines += ['', 'TBL = T.rc', '', 'misses = %s' % expr, '', PRINTER]
    with open(path, 'w') as f:
        f.write('\n'.join(lines))

def list_maybe_query(path, expr):
    wd = os.path.dirname(os.path.abspath(path))
    env = dict(os.environ, LC_ALL='C.UTF-8')
    src = os.path.abspath(B.SRC)
    r = subprocess.run(['agda', '--compile', '--compile-dir=' + os.path.join(wd, 'build'),
                        '-i', src, '-i', wd, path, '+RTS', '-M12G', '-RTS'],
                       capture_output=True, text=True, env=env)
    if r.returncode != 0:
        raise RuntimeError('agda --compile failed:\n' + (r.stdout + r.stderr)[-3000:])
    exe = os.path.join(wd, 'build', 'RCLoopDriver')
    out = subprocess.run([exe], capture_output=True, text=True, env=env, check=True).stdout
    e = B.parse(out.strip())
    res = []
    for m in B.to_list(e):
        if m == ('con', 'nothing', ()):
            res.append(None)
            continue
        assert m[0] == 'con' and m[1] == 'just', m
        tup = m[2][0]
        G, A, t, u = tup[1]
        res.append((B.to_ctx(G), B.to_ty(A), B.to_tm(t), B.to_tm(u)))
    return res

L.driver = driver
L.list_maybe_query = list_maybe_query

if __name__ == '__main__':
    table, expr, imports = sys.argv[1], sys.argv[2], sys.argv[3:]
    wd = os.environ.get('RC_WORKDIR') or os.path.join('/tmp', 'rc_loop_exe')
    os.makedirs(wd, exist_ok=True)
    L.main(table, expr, imports, wd)
