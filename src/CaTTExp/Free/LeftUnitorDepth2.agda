------------------------------------------------------------------------
-- Conjecture N, first case beyond BMOSV, machine-checked
-- (open-issues C7; notes/conjectures/naturality-arbitrary-depth.md §6,
-- "Partial progress: the left unitor at depth 2").
--
-- Q = (x, y, f : x → y), Y = all variables, c = λ_f : id_x ∗₀ f → f.
-- Q↑Y is the lax square `cyl D¹`. The naturality 3-cell has type
--
--   L := (λ_{f⁻} ∗₀ y↑) ∗₁ f↑   →   R := (id_x ∗₀ f)↑ ∗₁ (x↑ ∗₀ λ_{f⁺})
--
-- where (id_x ∗₀ f)↑ is the naturality term of the composite given by
-- the recursion of the conjecture file §3: K_comp (a depth-1 naturality
-- term for binary composition, built below from associators and
-- whiskerings) substituted with (id_x)↑ = ι for the first arrow.
--
-- The 3-cell is built by the sliding argument: the unitor is peeled off
-- the whiskering (F1), f↑ is slid through λ (F2: a coherence over the
-- 2-disc), the + side is compared over the chain x⁻ → x⁺ → y⁺ (F1),
-- and the remaining brackets are fixed by coherences over vertical
-- chains of 2-cells. Every cell is a coherence over a pasting context,
-- substituted, and the whole term is certified by the checker.
------------------------------------------------------------------------
module CaTTExp.Free.LeftUnitorDepth2 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Free.Builders
open import CaTTExp.Free.Cylinder

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- Generic coherences, as functions of typed arguments.

private
  tm : TT → Tm
  tm = fst

  -- Typed variables of a context.
  tv : Ctx → Nat → TT
  tv Γ i = var i , tyAt Γ i

  D1 D2 C2 C3 : Ctx
  D1 = ctxOf (disc 1)
  D2 = ctxOf (disc 2)
  C2 = ctxOf (node (leaf ∷ leaf ∷ []))
  C3 = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))

  -- The source/target of a typed 1-cell and the list x, y, f.
  cell1 : TT → List Tm
  cell1 (f , A) = flat (bdry A) ++ (f ∷ [])

  -- A coherence over the tree T with source s and target t (generic
  -- terms over ctxOf T), applied to the list ts.
  fill : Tree → TT → TT → List Tm → TT
  fill T s t ts = cohT T (arr (snd s) (fst s) (fst t)) ts

-- Left unitor λ_f : id_x ∗₀ f → f, for a typed 1-cell f.
lam : TT → TT
lam f = fill (disc 1) (idc (tv D1 0) ∗[ 0 ] tv D1 2) (tv D1 2) (cell1 f)

-- (id_x)↑ = ι : id_{x⁻} ∗₀ x↑ → x↑ ∗₀ id_{x⁺}, a coherence over the
-- disc (x⁻, x⁺, x↑).
iota : TT → TT
iota u = fill (disc 1) (idc (tv D1 0) ∗[ 0 ] tv D1 2) (tv D1 2 ∗[ 0 ] idc (tv D1 1)) (cell1 u)

-- Associator (f ∗₀ g) ∗₀ h → f ∗₀ (g ∗₀ h) and its inverse.
private
  c3 : Nat → TT
  c3 = tv C3
  c3f c3g c3h : TT
  c3f = c3 2
  c3g = c3 4
  c3h = c3 6
  -- list x, y, f, z, g, w, h for three composable typed 1-cells
  chain3 : TT → TT → TT → List Tm
  chain3 f g h = cell1 f ++ (tgt g ∷ fst g ∷ tgt h ∷ fst h ∷ [])
    where
    tgt : TT → Tm
    tgt (_ , arr _ _ t) = t
    tgt (_ , _)         = var 0

assoc assoc⁻ : TT → TT → TT → TT
assoc  f g h = fill (node (leaf ∷ leaf ∷ leaf ∷ []))
                 ((c3f ∗[ 0 ] c3g) ∗[ 0 ] c3h) (c3f ∗[ 0 ] (c3g ∗[ 0 ] c3h)) (chain3 f g h)
assoc⁻ f g h = fill (node (leaf ∷ leaf ∷ leaf ∷ []))
                 (c3f ∗[ 0 ] (c3g ∗[ 0 ] c3h)) ((c3f ∗[ 0 ] c3g) ∗[ 0 ] c3h) (chain3 f g h)

------------------------------------------------------------------------
-- The lax square Q↑Y = cyl D¹.
-- Levels: x⁻ 0, x⁺ 1, x↑ 2, y⁻ 3, y⁺ 4, y↑ 5, f⁻ 6, f⁺ 7, f↑ 8.

Sq : Ctx
Sq = cyl D1

private
  s : Nat → TT
  s = tv Sq
  x⁻ x⁺ x↑ y⁻ y⁺ y↑ f⁻ f⁺ f↑ : TT
  x⁻ = s 0 ; x⁺ = s 1 ; x↑ = s 2
  y⁻ = s 3 ; y⁺ = s 4 ; y↑ = s 5
  f⁻ = s 6 ; f⁺ = s 7 ; f↑ = s 8

-- The lax square is the one written in the conjecture file §2.3.
_ : Sq ≡ ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 3) (v 4)
          ▸ arr ⋆ (v 0) (v 3) ▸ arr ⋆ (v 1) (v 4)
          ▸ arr (arr ⋆ (v 0) (v 4)) (tm (f⁻ ∗[ 0 ] y↑)) (tm (x↑ ∗[ 0 ] f⁺))
_ = refl

------------------------------------------------------------------------
-- K_comp: a depth-1 naturality term for binary composition, over the
-- cylinder on the composable pair, as a function of the cylinder data
-- of the two arrows a : x → y and b : y → z:
--
--   (a⁻ ∗ b⁻) ∗ z↑ → a⁻ ∗ (b⁻ ∗ z↑) → a⁻ ∗ (y↑ ∗ b⁺) → (a⁻ ∗ y↑) ∗ b⁺
--                  → (x↑ ∗ a⁺) ∗ b⁺ → x↑ ∗ (a⁺ ∗ b⁺).

Kcomp : (a⁻ a⁺ a↑ b⁻ b⁺ b↑ x↑' y↑' z↑' : TT) → TT
Kcomp a⁻ a⁺ a↑ b⁻ b⁺ b↑ x↑' y↑' z↑' =
  (assoc a⁻ b⁻ z↑' ∗[ 1 ] (a⁻ ∗[ 0 ] b↑))
    ∗[ 1 ] ((assoc⁻ a⁻ y↑' b⁺ ∗[ 1 ] (a↑ ∗[ 0 ] b⁺)) ∗[ 1 ] assoc x↑' a⁺ b⁺)

-- (id_x ∗₀ f)↑ by the recursion: K_comp at a = id_x (with a↑ = ι), b = f.
idf↑ : TT
idf↑ = Kcomp (idc x⁻) (idc x⁺) (iota x↑) f⁻ f⁺ f↑ x↑ x↑ y↑

-- The two sides of the naturality cell of λ.
L R : TT
L = (lam f⁻ ∗[ 0 ] y↑) ∗[ 1 ] f↑
R = idf↑ ∗[ 1 ] (x↑ ∗[ 0 ] lam f⁺)

------------------------------------------------------------------------
-- The pieces.

private
  p q : TT
  p = f⁻ ∗[ 0 ] y↑
  q = x↑ ∗[ 0 ] f⁺

  -- Over the chain C2 = (x, y, f, z, g).
  c2 : Nat → TT
  c2 = tv C2
  c2f c2g : TT
  c2f = c2 2
  c2g = c2 4

  -- (F1) Step 1: λ_f ∗₀ g → α(id, f, g) ∗₁ λ_{f∗g}, over the chain
  -- x⁻ → y⁻ → y⁺.
  E1 : TT
  E1 = fill (node (leaf ∷ leaf ∷ []))
         (lam c2f ∗[ 0 ] c2g)
         (assoc (idc (c2 0)) c2f c2g ∗[ 1 ] lam (c2f ∗[ 0 ] c2g))
         (cell1 f⁻ ++ (fst y⁺ ∷ fst y↑ ∷ []))

  -- (F2) Step 2: λ is natural in its top argument: over the 2-disc
  -- (a, b, g⁻, g⁺, g↑ : g⁻ ⇒ g⁺), λ_{g⁻} ∗₁ g↑ → (id_a ∗₀ g↑) ∗₁ λ_{g⁺};
  -- substituted at g↑ ↦ f↑ : p ⇒ q.
  d2 : Nat → TT
  d2 = tv D2
  N : TT
  N = fill (disc 2)
        (lam (d2 2) ∗[ 1 ] d2 4)
        ((idc (d2 0) ∗[ 0 ] d2 4) ∗[ 1 ] lam (d2 3))
        (fst x⁻ ∷ fst y⁺ ∷ fst p ∷ fst q ∷ fst f↑ ∷ [])

  -- (F1) Step 3: over the chain x⁻ → x⁺ → y⁺,
  -- λ_{f∗g} → ((α⁻(id, f, g) ∗₁ (ι_f ∗₀ g)) ∗₁ α(f, id, g)) ∗₁ (f ∗₀ λ_g).
  Mgen : TT
  Mgen = ((assoc⁻ (idc (c2 0)) c2f c2g ∗[ 1 ] (iota c2f ∗[ 0 ] c2g))
            ∗[ 1 ] assoc c2f (idc (c2 1)) c2g)
         ∗[ 1 ] (c2f ∗[ 0 ] lam c2g)

  E3 : TT
  E3 = fill (node (leaf ∷ leaf ∷ []))
         (lam (c2f ∗[ 0 ] c2g)) Mgen
         (cell1 x↑ ++ (fst y⁺ ∷ fst f⁺ ∷ []))

  -- Vertical chains of 2-cells: the pasting context of n composable
  -- 2-cells between two 0-cells, and its substitution.
  vtree : Nat → Tree
  vtree n = node (node (go n) ∷ [])
    where
    go : Nat → List Tree
    go zero    = []
    go (suc k) = leaf ∷ go k

  -- x, y, s₁, t₁, c₁, t₂, c₂, … for typed 2-cells c₁, c₂, …
  vlist : List TT → List Tm
  vlist []              = []
  vlist ((c , A) ∷ cs) = flat (bdry A) ++ (c ∷ rest cs)
    where
    rest : List TT → List Tm
    rest []                       = []
    rest ((d , arr _ _ t) ∷ ds)  = t ∷ d ∷ rest ds
    rest ((d , _) ∷ ds)          = d ∷ rest ds

  vt : Nat → Nat → TT          -- the k-th 2-cell variable of vtree n
  vt n k = tv (ctxOf (vtree n)) (4 + k + k)

  -- (a ∗₁ b) ∗₁ c → a ∗₁ (b ∗₁ c)
  A3 : TT → TT → TT → TT
  A3 a b c = fill (vtree 3) ((vt 3 0 ∗[ 1 ] vt 3 1) ∗[ 1 ] vt 3 2)
                            (vt 3 0 ∗[ 1 ] (vt 3 1 ∗[ 1 ] vt 3 2))
                            (vlist (a ∷ b ∷ c ∷ []))

  -- c₀ ∗₁ (c₁ ∗₁ (((c₂ ∗₁ c₃) ∗₁ c₄) ∗₁ c₅))
  --   → ((c₀ ∗₁ c₁) ∗₁ ((c₂ ∗₁ c₃) ∗₁ c₄)) ∗₁ c₅
  A6 : TT → TT → TT → TT → TT → TT → TT
  A6 c₀ c₁ c₂ c₃ c₄ c₅ =
    fill (vtree 6)
      (w 0 ∗[ 1 ] (w 1 ∗[ 1 ] (((w 2 ∗[ 1 ] w 3) ∗[ 1 ] w 4) ∗[ 1 ] w 5)))
      (((w 0 ∗[ 1 ] w 1) ∗[ 1 ] ((w 2 ∗[ 1 ] w 3) ∗[ 1 ] w 4)) ∗[ 1 ] w 5)
      (vlist (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ c₅ ∷ []))
    where w = vt 6

  α₁ W β₁ β₂ β₃ β₄ : TT
  α₁ = assoc (idc x⁻) f⁻ y↑
  W  = idc x⁻ ∗[ 0 ] f↑
  β₁ = assoc⁻ (idc x⁻) x↑ f⁺
  β₂ = iota x↑ ∗[ 0 ] f⁺
  β₃ = assoc x↑ (idc x⁺) f⁺
  β₄ = x↑ ∗[ 0 ] lam f⁺

-- The composite 3-cell L → R:
--   L = (λ_{f⁻} ∗₀ y↑) ∗₁ f↑
--     → (α₁ ∗₁ λ_p) ∗₁ f↑                         (E1 ∗₁ f↑)
--     → α₁ ∗₁ (λ_p ∗₁ f↑)                         (A3)
--     → α₁ ∗₁ (W ∗₁ λ_q)                          (α₁ ∗₁ N)
--     → α₁ ∗₁ (W ∗₁ (((β₁ ∗₁ β₂) ∗₁ β₃) ∗₁ β₄))   (α₁ ∗₁ (W ∗₁ E3))
--     → ((α₁ ∗₁ W) ∗₁ ((β₁ ∗₁ β₂) ∗₁ β₃)) ∗₁ β₄  (A6)
--     = R.
K-λ : TT
K-λ = ((((E1 ∗[ 1 ] f↑)
          ∗[ 2 ] A3 α₁ (lam p) f↑)
          ∗[ 2 ] (α₁ ∗[ 1 ] N))
          ∗[ 2 ] (α₁ ∗[ 1 ] (W ∗[ 1 ] E3)))
          ∗[ 2 ] A6 α₁ W β₁ β₂ β₃ β₄

-- The claimed type: a 3-cell from L to R, i.e. the type a_c → b_c of
-- Conjecture N for c = λ_f with all variables selected.
K-λ-type : Ty
K-λ-type = arr (snd L) (fst L) (fst R)

------------------------------------------------------------------------
-- Certified derivations.

-- K_comp is a naturality term for binary composition: over the
-- cylinder on the composable pair (levels: x 0–2, y 3–5, a 6–8,
-- z 9–11, b 12–14) it has type (a⁻ ∗ b⁻) ∗ z↑ → x↑ ∗ (a⁺ ∗ b⁺).
private
  P↑ : Ctx
  P↑ = cyl C2
  pv : Nat → TT
  pv = tv P↑

Kcomp-generic : TT
Kcomp-generic = Kcomp (pv 6) (pv 7) (pv 8) (pv 12) (pv 13) (pv 14) (pv 2) (pv 5) (pv 11)

Kcomp-type : Ty
Kcomp-type = arr (arr ⋆ (v 0) (v 10))
                 (fst ((pv 6 ∗[ 0 ] pv 12) ∗[ 0 ] pv 11))
                 (fst (pv 2 ∗[ 0 ] (pv 7 ∗[ 0 ] pv 13)))

_ : snd Kcomp-generic ≡ Kcomp-type
_ = refl

Kcomp-wf : P↑ ⊢tm fst Kcomp-generic ∶ Kcomp-type
Kcomp-wf = certify P↑ Kcomp-generic

-- ι is the naturality term of the identity: over the cylinder on a
-- point (x⁻, x⁺, x↑) it has type id_{x⁻} ∗₀ x↑ → x↑ ∗₀ id_{x⁺}.
ι-wf : cyl (ctxOf (disc 0)) ⊢tm fst (iota (tv (cyl (ctxOf (disc 0))) 2))
                              ∶ snd (iota (tv (cyl (ctxOf (disc 0))) 2))
ι-wf = certify (cyl (ctxOf (disc 0))) (iota (tv (cyl (ctxOf (disc 0))) 2))

-- The two sides are well-typed 2-cells of the lax square ...
L-wf : Sq ⊢tm fst L ∶ snd L
L-wf = certify Sq L

R-wf : Sq ⊢tm fst R ∶ snd R
R-wf = certify Sq R

-- ... and the depth-2 naturality cell of the left unitor is a
-- well-typed 3-cell L → R.
_ : snd K-λ ≡ K-λ-type
_ = refl

K-λ-wf : Sq ⊢tm fst K-λ ∶ K-λ-type
K-λ-wf = certify Sq K-λ

-- Negative checks. The checker distinguishes the cell's direction, and
-- the lax square is not a pasting context, so L → R is not a single
-- coherence over it: the construction above is needed.
_ : checks Sq (fst K-λ , arr (snd L) (fst R) (fst L)) ≡ false
_ = refl

_ : checks Sq (coh Sq K-λ-type (idₛ Sq) , K-λ-type) ≡ false
_ = refl
