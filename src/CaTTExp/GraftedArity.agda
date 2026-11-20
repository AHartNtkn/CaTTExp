------------------------------------------------------------------------
-- Grafted arities (notes/relative-coherence.md §7.13(F), step F2).
--
-- A pasting arity is a Batanin tree; a leaf at depth d is a locally
-- maximal d-cell y.  Grafting a tree T at that leaf replaces y by the
-- pasting diagram of shape T in the hom over ∂y (T = node [leaf] is a
-- one-link column y → y′, node (leaf ∷ leaf ∷ []) a two-link string,
-- and deeper T carry comparisons of comparisons).
--
-- Grafting gives a pasting context, so parallel terms of equal normal
-- form admit a raw comparison there.  The distributor theorem below
-- computes the common strict normal form for arbitrary nested outer
-- and inner compositions on compatible labelled trees.  Different raw
-- boundary bracketings still require face corrections before graft-fill.
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

------------------------------------------------------------------------
-- Strict evaluation in a graft.  Each row labels the spatial slots of
-- the root.  Inner compositions take place above every cut of the root.

module Distributors where
  open import CaTTExp.GlobularFiller using (merge; bd)
  open import CaTTExp.GlobularTotal.TreeAlg using (Compat; WF; bd-merge-high)
  open import CaTTExp.GlobularTotal.MergeLaws using (merge-xch; merge-unitl)

  Row = Nat → LT

  data Frame : Set where
    slot : Nat → Frame
    join : Nat → Frame → Frame → Frame

  apply : Frame → Row → LT
  apply (slot i) ρ = ρ i
  apply (join j a b) ρ = merge j (apply a ρ) (apply b ρ)

  -- Only the cuts and slots actually used by this frame need checking.
  Above : Nat → Frame → Set
  Above k (slot _) = ⊤
  Above k (join j a b) = T (j <ℕ k) × Above k a × Above k b

  Fits : Nat → Frame → Row → Row → Set
  Fits k (slot i) ρ σ = Compat k (ρ i) (σ i)
  Fits k (join j a b) ρ σ = Fits k a ρ σ × Fits k b ρ σ

  compatible : ∀ k f ρ σ → Above k f → Fits k f ρ σ →
               Compat k (apply f ρ) (apply f σ)
  compatible k (slot i) ρ σ _ e = e
  compatible k (join j a b) ρ σ (p , pa , pb) (ea , eb) =
    trans (bd-merge-high true k j (apply a ρ) (apply b ρ) p)
    (trans (cong₂ (merge j) (compatible k a ρ σ pa ea)
                            (compatible k b ρ σ pb eb))
           (sym (bd-merge-high false k j (apply a σ) (apply b σ) p)))

  distribute : ∀ k f ρ σ → Above k f → Fits k f ρ σ →
               merge k (apply f ρ) (apply f σ) ≡
               apply f (λ i → merge k (ρ i) (σ i))
  distribute k (slot i) ρ σ _ _ = refl
  distribute k (join j a b) ρ σ (p , pa , pb) (ea , eb) =
    trans (merge-xch j k (apply a ρ) (apply b ρ) (apply a σ) (apply b σ)
                     p (compatible k a ρ σ pa ea))
          (cong₂ (merge j) (distribute k a ρ σ pa ea) (distribute k b ρ σ pb eb))

  data Pasting : Set where
    row : Row → Pasting
    paste : Nat → Pasting → Pasting → Pasting

  column : Pasting → Nat → LT
  column (row ρ) i = ρ i
  column (paste k a b) i = merge k (column a i) (column b i)

  by-rows : Frame → Pasting → LT
  by-rows f (row ρ) = apply f ρ
  by-rows f (paste k a b) = merge k (by-rows f a) (by-rows f b)

  Composable : Frame → Pasting → Set
  Composable f (row _) = ⊤
  Composable f (paste k a b) = Above k f × Fits k f (column a) (column b)
                             × Composable f a × Composable f b

  graft-distributes : ∀ f t → Composable f t → by-rows f t ≡ apply f (column t)
  graft-distributes f (row ρ) _ = refl
  graft-distributes f (paste k a b) (p , e , ca , cb) =
    trans (cong₂ (merge k) (graft-distributes f a ca) (graft-distributes f b cb))
          (distribute k f (column a) (column b) p e)

  -- In a one-slot action the other columns are higher identities.
  Constant : LT → Nat → Pasting → Set
  Constant x i (row ρ) = ρ i ≡ x
  Constant x i (paste k a b) = (∀ β → bd β k x ≡ x) × Constant x i a × Constant x i b

  constant-column : ∀ x i t → WF x → Constant x i t → column t i ≡ x
  constant-column x i (row ρ) w e = e
  constant-column x i (paste k a b) w (thin , ea , eb) =
    trans (cong₂ (merge k) (constant-column x i a w ea) (constant-column x i b w eb))
          (merge-unitl k x x (thin false) w (trans (thin true) (sym (thin false))))
