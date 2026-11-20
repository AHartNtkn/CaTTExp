------------------------------------------------------------------------
-- Grafted arities (notes/relative-coherence.md §7.13(F), step F2).
--
-- A pasting arity is a Batanin tree; a leaf at depth d is a locally
-- maximal d-cell y.  Grafting a tree T at that leaf replaces y by the
-- pasting diagram of shape T in the hom over ∂y (T = node [leaf] is a
-- one-link column y → y′, node (leaf ∷ leaf ∷ []) a two-link string,
-- and deeper T carry comparisons of comparisons).
--
-- The level-j substitution step of lemma L acts with a root head on a
-- pasting of argument cells by forming the root in the grafted arity
-- and comparing there by the coherence rule.  This module checks only
-- the immediate part of that step (that the two composites of F2 have
-- equal strict normal forms is a paper argument, not checked here):
--
--   * the grafted arity is again a pasting context (`psGraft`), hence
--     globular (`graft-glob`), for every tree, leaf and grafted tree;
--   * the globular filler is total on it (`graft-fill`, from
--     GlobularTotal.FillTotal.fill-total): any two parallel terms with
--     the same strict normal form are joined by a certified coherence;
--   * grafting a leaf changes nothing (`graft-leaf`).
--
-- Everything is a corollary of PastingTrees.psOf and fill-total; no
-- postulates.  The raw-term recursion that *uses* these comparisons
-- (§7.13(F) F1–F4) is not formalised here.
------------------------------------------------------------------------
module CaTTExp.GraftedArity where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularTotal.PsOrd using (ps-glob)
open import CaTTExp.GlobularTotal.NfTyped using (Glob)
open import CaTTExp.GlobularTotal.FillTotal using (fill-total)
open import CaTTExp.GlobularFiller using (LT; nf; fillRaw)

------------------------------------------------------------------------
-- Leaf addresses and grafting.

mutual
  data Addr : Tree → Set where
    here  : Addr (node [])
    there : ∀ {ts} → ChildAddr ts → Addr (node ts)

  data ChildAddr : List Tree → Set where
    hd : ∀ {t ts} → Addr t → ChildAddr (t ∷ ts)
    tl : ∀ {t ts} → ChildAddr ts → ChildAddr (t ∷ ts)

mutual
  graftA : ∀ {A} → Addr A → Tree → Tree
  graftA here                 T = T
  graftA (there a)            T = node (graftL a T)

  graftL : ∀ {ts} → ChildAddr ts → Tree → List Tree
  graftL (hd {ts = ts} a) T = graftA a T ∷ ts
  graftL (tl {t = t} a)   T = t ∷ graftL a T

graft : (A : Tree) → Addr A → Tree → Tree
graft A a T = graftA a T

-- A string of r links: r composable cells one dimension up.
replicate : Nat → Tree → List Tree
replicate zero    t = []
replicate (suc r) t = t ∷ replicate r t

string : Nat → Tree
string r = node (replicate r leaf)

------------------------------------------------------------------------
-- The grafted arity is a pasting context, hence globular.

psGraft : ∀ A a T → ctxOf (graft A a T) ⊢ps
psGraft A a T = snd (psOf (graft A a T))

graft-glob : ∀ A a T → Glob (ctxOf (graft A a T))
graft-glob A a T = ps-glob (psGraft A a T)

-- The coherence rule in the grafted arity: certified comparisons.
graft-fill : ∀ A a T {u v B} →
             ctxOf (graft A a T) ⊢tm u ∶ B → ctxOf (graft A a T) ⊢tm v ∶ B →
             ∀ N n n′ → nf n (ctxOf (graft A a T)) u ≡ just N →
             nf n′ (ctxOf (graft A a T)) v ≡ just N →
             Σ Tm λ c → (fillRaw (ctxOf (graft A a T)) u v B ≡ just c)
                      × (ctxOf (graft A a T) ⊢tm c ∶ arr B u v)
graft-fill A a T du dv N n n′ eu ev =
  fill-total (graft-glob A a T) du dv N n n′ eu ev

------------------------------------------------------------------------
-- Grafting a leaf is the identity.

mutual
  graft-leaf : ∀ A (a : Addr A) → graft A a leaf ≡ A
  graft-leaf .(node []) here      = refl
  graft-leaf (node ts)  (there a) = cong node (graftL-leaf ts a)

  graftL-leaf : ∀ ts (a : ChildAddr ts) → graftL a leaf ≡ ts
  graftL-leaf (t ∷ ts) (hd a) = cong (λ u → u ∷ ts) (graft-leaf t a)
  graftL-leaf (t ∷ ts) (tl a) = cong (λ us → t ∷ us) (graftL-leaf ts a)

------------------------------------------------------------------------
-- Examples.

-- Two composable 1-cells; graft a two-link 2-string on the first.
ex-string : graft (node (leaf ∷ leaf ∷ [])) (there (hd here)) (string 2)
          ≡ node (node (leaf ∷ leaf ∷ []) ∷ leaf ∷ [])
ex-string = refl

-- A 2-cell arity; graft a column carrying a comparison of comparisons
-- (a 4-globe over the 2-cell): the result is the 4-disc whiskered.
ex-deep : graft (node (node (leaf ∷ []) ∷ leaf ∷ [])) (there (hd (there (hd here))))
                (node (node (leaf ∷ []) ∷ []))
        ≡ node (node (node (node (leaf ∷ []) ∷ []) ∷ []) ∷ leaf ∷ [])
ex-deep = refl

ex-deep-ps : ctxOf (node (node (node (node (leaf ∷ []) ∷ []) ∷ []) ∷ leaf ∷ [])) ⊢ps
ex-deep-ps = psGraft (node (node (leaf ∷ []) ∷ leaf ∷ [])) (there (hd (there (hd here))))
                     (node (node (leaf ∷ []) ∷ []))
