------------------------------------------------------------------------
-- Conjecture N for the associator over three arrows with every
-- variable selected (depth 2), machine-checked
-- (open-issues C1b / C7; notes/conjectures/naturality-arbitrary-depth.md
-- §7 case 1 and the researcher response §3).
--
-- Q = (x, y, f, z, g, w, h), Y = all variables, c = α_{f,g,h}. The
-- cylinder Q↑Y is `cyl` of the three-arrow chain (a ladder of three
-- lax squares). The naturality 3-cell has type
--
--   L := (α⁻ ∗₀ w↑) ∗₁ (f ∗ (g ∗ h))↑  →  R := ((f ∗ g) ∗ h)↑ ∗₁ (x↑ ∗₀ α⁺)
--
-- where the naturality terms of the composites are given by the
-- recursion of the conjecture file §3 from the depth-1 term K_comp
-- (LeftUnitorDepth2): (g ∗ h)↑ = K_comp[g, h], (f ∗ (g ∗ h))↑ =
-- K_comp[f, g ∗ h], and so on.
--
-- Construction (the sliding argument of the conjecture file §6, with
-- three cylinder cells):
--   1. distribute the whiskerings over the inner K_comp (F1);
--   2. rebracket to a flat vertical composite (F1);
--   3. slide each cylinder cell f↑, g↑, h↑ from L's whiskering to R's
--      by naturality of the associator in its top argument (F2);
--   4. regroup into four segments separated by the cylinder cells;
--   5. each segment lies along one path through the ladder, a chain of
--      four arrows, where L's and R's segments are parallel full terms
--      (F1; the last one is the pentagon);
--   6. undo steps 1–2 on R's side.
-- Each step is a coherence over a pasting context, substituted, and
-- the composite is certified by the checker.
------------------------------------------------------------------------
module CaTTExp.Free.AssociatorDepth2 where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Free.Builders
open import CaTTExp.Free.Cylinder
open import CaTTExp.Free.LeftUnitorDepth2 using (assoc; assoc⁻; Kcomp)

private
  tv : Ctx → Nat → TT
  tv Γ i = var i , tyAt Γ i

  cell1 : TT → List Tm
  cell1 (f , A) = flat (bdry A) ++ (f ∷ [])

  tgt : TT → Tm
  tgt (_ , arr _ _ t) = t
  tgt (_ , _)         = var 0

  -- A coherence over T from s to t (generic over ctxOf T), applied to ts.
  fill : Tree → TT → TT → List Tm → TT
  fill T s t ts = cohT T (arr (snd s) (fst s) (fst t)) ts

  -- The same coherence, unsubstituted: coh_{T, s → t}[id] in ctxOf T.
  genFill : Tree → TT → TT → Ctx × TT
  genFill T s t = ctxOf T , (coh (ctxOf T) ty₀ (idₛ (ctxOf T)) , ty₀)
    where ty₀ = arr (snd s) (fst s) (fst t)

  leaves : Nat → List Tree
  leaves zero    = []
  leaves (suc n) = leaf ∷ leaves n

  -- x, y, s₁, t₁, c₁, t₂, c₂, … for vertically composable typed 2-cells
  vlist : List TT → List Tm
  vlist []              = []
  vlist ((c , A) ∷ cs) = flat (bdry A) ++ (c ∷ rest cs)
    where
    rest : List TT → List Tm
    rest []                      = []
    rest ((d , arr _ _ t) ∷ ds) = t ∷ d ∷ rest ds
    rest ((d , _) ∷ ds)         = d ∷ rest ds

  len' : ∀ {A : Set} → List A → Nat
  len' []       = 0
  len' (_ ∷ xs) = suc (len' xs)

  nth : List TT → Nat → TT
  nth []       _       = var 0 , ⋆
  nth (x ∷ _)  zero    = x
  nth (_ ∷ xs) (suc n) = nth xs n

------------------------------------------------------------------------
-- Bracketings of vertical composites.

data BT : Set where
  at  : Nat → BT
  _⊙_ : BT → BT → BT
infixr 5 _⊙_

-- Right-nested composite of the atoms i, i+1, …, i+n−1 (n ≥ 1).
rn : Nat → Nat → BT
rn i zero          = at i
rn i (suc zero)    = at i
rn i (suc (suc n)) = at i ⊙ rn (suc i) (suc n)

interp : BT → List TT → TT
interp (at i)  cs = nth cs i
interp (a ⊙ b) cs = interp a cs ∗[ 1 ] interp b cs

private
  -- The generic atoms of the vertical chain of n 2-cells.
  vgen : Nat → List TT
  vgen n = go 0 n
    where
    Vn = ctxOf (node (node (leaves n) ∷ []))
    go : Nat → Nat → List TT
    go i zero    = []
    go i (suc k) = tv Vn (4 + i + i) ∷ go (suc i) k

-- The coherence between two bracketings of the same n atoms.
rebr : Nat → BT → BT → List TT → TT
rebr n b₁ b₂ cs = fill (node (node (leaves n) ∷ [])) (interp b₁ (vgen n)) (interp b₂ (vgen n)) (vlist cs)

------------------------------------------------------------------------
-- The ladder Q↑Y.
-- Levels: x 0–2, y 3–5, f 6–8, z 9–11, g 12–14, w 15–17, h 18–20
-- (each as ⁻, ⁺, ↑).

C3 : Ctx
C3 = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))

Lad : Ctx
Lad = cyl C3

private
  l : Nat → TT
  l = tv Lad
  x⁻ x⁺ x↑ y⁻ y⁺ y↑ f⁻ f⁺ f↑ z⁻ z⁺ z↑ g⁻ g⁺ g↑ w⁻ w⁺ w↑ h⁻ h⁺ h↑ : TT
  x⁻ = l 0  ; x⁺ = l 1  ; x↑ = l 2
  y⁻ = l 3  ; y⁺ = l 4  ; y↑ = l 5
  f⁻ = l 6  ; f⁺ = l 7  ; f↑ = l 8
  z⁻ = l 9  ; z⁺ = l 10 ; z↑ = l 11
  g⁻ = l 12 ; g⁺ = l 13 ; g↑ = l 14
  w⁻ = l 15 ; w⁺ = l 16 ; w↑ = l 17
  h⁻ = l 18 ; h⁺ = l 19 ; h↑ = l 20

  _∙_ : TT → TT → TT
  a ∙ b = a ∗[ 0 ] b
  infixl 7 _∙_

-- Naturality terms of the composites, by the recursion.
gh↑ fg↑ f-gh↑ fg-h↑ : TT
gh↑   = Kcomp g⁻ g⁺ g↑ h⁻ h⁺ h↑ y↑ z↑ w↑
fg↑   = Kcomp f⁻ f⁺ f↑ g⁻ g⁺ g↑ x↑ y↑ z↑
f-gh↑ = Kcomp f⁻ f⁺ f↑ (g⁻ ∙ h⁻) (g⁺ ∙ h⁺) gh↑ x↑ y↑ w↑
fg-h↑ = Kcomp (f⁻ ∙ g⁻) (f⁺ ∙ g⁺) fg↑ h⁻ h⁺ h↑ x↑ z↑ w↑

-- The two sides of the naturality cell of α (conjecture file §2.2).
L R : TT
L = (assoc f⁻ g⁻ h⁻ ∙ w↑) ∗[ 1 ] f-gh↑
R = fg-h↑ ∗[ 1 ] (x↑ ∙ assoc f⁺ g⁺ h⁺)

------------------------------------------------------------------------
-- The atoms.

private
  -- K_comp's bracketing of its five atoms.
  kshape : BT
  kshape = (at 0 ⊙ at 1) ⊙ ((at 2 ⊙ at 3) ⊙ at 4)

  -- Atoms of (g ∗ h)↑ and (f ∗ g)↑.
  a₁ a₂ a₃ a₄ a₅ a'₁ a'₂ a'₃ a'₄ a'₅ : TT
  a₁ = assoc g⁻ h⁻ w↑ ; a₂ = g⁻ ∙ h↑ ; a₃ = assoc⁻ g⁻ z↑ h⁺
  a₄ = g↑ ∙ h⁺        ; a₅ = assoc y↑ g⁺ h⁺
  a'₁ = assoc f⁻ g⁻ z↑ ; a'₂ = f⁻ ∙ g↑ ; a'₃ = assoc⁻ f⁻ y↑ g⁺
  a'₄ = f↑ ∙ g⁺        ; a'₅ = assoc x↑ f⁺ g⁺

  -- L = (α⁻ ∗ w↑) ∗₁ K_comp[f, gh]: six atoms, the third being
  -- f⁻ ∗₀ (g ∗ h)↑.
  Lshape : BT
  Lshape = at 0 ⊙ ((at 1 ⊙ at 2) ⊙ ((at 3 ⊙ at 4) ⊙ at 5))

  αw b₁ b₂ b₃ b₄ b₅ : TT
  αw = assoc f⁻ g⁻ h⁻ ∙ w↑
  b₁ = assoc f⁻ (g⁻ ∙ h⁻) w↑
  b₂ = f⁻ ∙ gh↑
  b₃ = assoc⁻ f⁻ y↑ (g⁺ ∙ h⁺)
  b₄ = f↑ ∙ (g⁺ ∙ h⁺)
  b₅ = assoc x↑ f⁺ (g⁺ ∙ h⁺)

  -- R = K_comp[fg, h] ∗₁ (x↑ ∗ α⁺): six atoms, the fourth being
  -- (f ∗ g)↑ ∗₀ h⁺.
  Rshape : BT
  Rshape = ((at 0 ⊙ at 1) ⊙ ((at 2 ⊙ at 3) ⊙ at 4)) ⊙ at 5

  e₁ e₂ e₃ e₄ e₅ xα : TT
  e₁ = assoc (f⁻ ∙ g⁻) h⁻ w↑
  e₂ = (f⁻ ∙ g⁻) ∙ h↑
  e₃ = assoc⁻ (f⁻ ∙ g⁻) z↑ h⁺
  e₄ = fg↑ ∙ h⁺
  e₅ = assoc x↑ (f⁺ ∙ g⁺) h⁺
  xα = x↑ ∙ assoc f⁺ g⁺ h⁺

------------------------------------------------------------------------
-- The steps.

private
  -- vertical-chain atom variables and generic typed variables of trees
  gv : Tree → Nat → TT
  gv T = tv (ctxOf T)

  -- 1. Distribute f⁻ ∗₀ − over (g ∗ h)↑, and − ∗₀ h⁺ over (f ∗ g)↑.
  TDL TDR : Tree
  TDL = node (leaf ∷ node (leaves 5) ∷ [])
  TDR = node (node (leaves 5) ∷ leaf ∷ [])

  θL θR : List TT
  θL = gv TDL 6 ∷ gv TDL 8 ∷ gv TDL 10 ∷ gv TDL 12 ∷ gv TDL 14 ∷ []
  θR = gv TDR 4 ∷ gv TDR 6 ∷ gv TDR 8 ∷ gv TDR 10 ∷ gv TDR 12 ∷ []

  mapT : (TT → TT) → List TT → List TT
  mapT f []       = []
  mapT f (x ∷ xs) = f x ∷ mapT f xs

  as as' : List TT
  as  = a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ a₅ ∷ []
  as' = a'₁ ∷ a'₂ ∷ a'₃ ∷ a'₄ ∷ a'₅ ∷ []

  DL : TT
  DL = fill TDL (gv TDL 2 ∙ interp kshape θL)
                (interp (rn 0 5) (mapT (gv TDL 2 ∙_) θL))
                (cell1 f⁻ ++ dropL 1 (vlist as))

  DR⁻ : TT     -- reversed: from the distributed form back to (f ∗ g)↑ ∗₀ h⁺
  DR⁻ = fill TDR (interp (rn 0 5) (mapT (_∙ gv TDR 14) θR))
                 (interp kshape θR ∙ gv TDR 14)
                 (vlist as' ++ (fst w⁺ ∷ fst h⁺ ∷ []))

  -- 3. Slides (F2): naturality of the associator in its top argument.
  T₁ T₂ T₃ : Tree
  T₁ = node (leaf ∷ leaf ∷ node (leaf ∷ []) ∷ [])
  T₂ = node (leaf ∷ node (leaf ∷ []) ∷ leaf ∷ [])
  T₃ = node (node (leaf ∷ []) ∷ leaf ∷ leaf ∷ [])

  slide₁ slide₂ slide₃ : TT
  slide₁ = fill T₁ (f ∙ (g ∙ θ))
                   ((assoc⁻ f g u ∗[ 1 ] ((f ∙ g) ∙ θ)) ∗[ 1 ] assoc f g u')
                   (cell1 f⁻ ++ (fst z⁻ ∷ fst g⁻ ∷ flat' h↑))
    where f = gv T₁ 2 ; g = gv T₁ 4 ; u = gv T₁ 6 ; u' = gv T₁ 7 ; θ = gv T₁ 8
          flat' : TT → List Tm
          flat' (c , A) = dropL 1 (flat (bdry A)) ++ (c ∷ [])
  slide₂ = fill T₂ (f ∙ (θ ∙ h))
                   ((assoc⁻ f u h ∗[ 1 ] ((f ∙ θ) ∙ h)) ∗[ 1 ] assoc f u' h)
                   (cell1 f⁻ ++ dropL 1 (flat (bdry (snd g↑))) ++ (fst g↑ ∷ fst w⁺ ∷ fst h⁺ ∷ []))
    where f = gv T₂ 2 ; u = gv T₂ 4 ; u' = gv T₂ 5 ; θ = gv T₂ 6 ; h = gv T₂ 8
  slide₃ = fill T₃ (θ ∙ (g ∙ h))
                   ((assoc⁻ u g h ∗[ 1 ] ((θ ∙ g) ∙ h)) ∗[ 1 ] assoc u' g h)
                   (flat (bdry (snd f↑)) ++ (fst f↑ ∷ fst z⁺ ∷ fst g⁺ ∷ fst w⁺ ∷ fst h⁺ ∷ []))
    where u = gv T₃ 2 ; u' = gv T₃ 3 ; θ = gv T₃ 4 ; g = gv T₃ 6 ; h = gv T₃ 8

  -- 5. Segment comparisons (F1) over chains of four arrows.
  T₄ : Tree
  T₄ = node (leaves 4)

  chain4 : TT → TT → TT → TT → List Tm
  chain4 a b c d = cell1 a ++ (tgt b ∷ fst b ∷ tgt c ∷ fst c ∷ tgt d ∷ fst d ∷ [])

  Seg : Set
  Seg = TT → TT → TT → TT → List TT

  P₀ Q₀ P₁ Q₁ P₂ Q₂ P₃ Q₃ : Seg
  P₀ a b c d = (assoc a b c ∙ d) ∷ assoc a (b ∙ c) d ∷ (a ∙ assoc b c d) ∷ assoc⁻ a b (c ∙ d) ∷ []
  Q₀ a b c d = assoc (a ∙ b) c d ∷ []
  P₁ a b c d = assoc a b (c ∙ d) ∷ (a ∙ assoc⁻ b c d) ∷ assoc⁻ a (b ∙ c) d ∷ []
  Q₁ a b c d = assoc⁻ (a ∙ b) c d ∷ (assoc a b c ∙ d) ∷ []
  P₂ a b c d = assoc a (b ∙ c) d ∷ (a ∙ assoc b c d) ∷ assoc⁻ a b (c ∙ d) ∷ assoc⁻ (a ∙ b) c d ∷ []
  Q₂ a b c d = (assoc⁻ a b c ∙ d) ∷ []
  P₃ a b c d = assoc (a ∙ b) c d ∷ assoc a b (c ∙ d) ∷ []
  Q₃ a b c d = (assoc a b c ∙ d) ∷ assoc a (b ∙ c) d ∷ (a ∙ assoc b c d) ∷ []

  segS segT : Seg → TT
  segS P = interp (rn 0 (len' (P ga gb gc gd))) (P ga gb gc gd)
    where ga = gv T₄ 2 ; gb = gv T₄ 4 ; gc = gv T₄ 6 ; gd = gv T₄ 8
  segT = segS

  compare : Seg → Seg → TT → TT → TT → TT → TT
  compare P Q a b c d = fill T₄ (segS P) (segT Q) (chain4 a b c d)

  F₀ F₁ F₂ F₃ : TT
  F₀ = compare P₀ Q₀ f⁻ g⁻ h⁻ w↑
  F₁ = compare P₁ Q₁ f⁻ g⁻ z↑ h⁺
  F₂ = compare P₂ Q₂ f⁻ y↑ g⁺ h⁺
  F₃ = compare P₃ Q₃ x↑ f⁺ g⁺ h⁺

  -- Atoms and bracketings along the way.
  atoms10 atoms16 atoms10R : List TT
  atoms10  = αw ∷ b₁ ∷ mapT (f⁻ ∙_) as ++ (b₃ ∷ b₄ ∷ b₅ ∷ [])
  c₁ c₂ c₃ : TT
  c₁ = (f⁻ ∙ g⁻) ∙ h↑
  c₂ = (f⁻ ∙ g↑) ∙ h⁺
  c₃ = (f↑ ∙ g⁺) ∙ h⁺
  atoms16  = P₀ f⁻ g⁻ h⁻ w↑ ++ (c₁ ∷ P₁ f⁻ g⁻ z↑ h⁺ ++ (c₂ ∷ P₂ f⁻ y↑ g⁺ h⁺ ++ (c₃ ∷ P₃ x↑ f⁺ g⁺ h⁺)))
  atoms10R = Q₀ f⁻ g⁻ h⁻ w↑ ++ (c₁ ∷ Q₁ f⁻ g⁻ z↑ h⁺ ++ (c₂ ∷ Q₂ f⁻ y↑ g⁺ h⁺ ++ (c₃ ∷ Q₃ x↑ f⁺ g⁺ h⁺)))

  replace : Nat → TT → List TT → List TT
  replace _       y []       = []
  replace zero    y (_ ∷ xs) = y ∷ xs
  replace (suc n) y (x ∷ xs) = x ∷ replace n y xs

  S2 S4 G16 G7 G10R SR : BT
  S2   = at 0 ⊙ ((at 1 ⊙ rn 2 5) ⊙ ((at 7 ⊙ at 8) ⊙ at 9))
  S4   = at 0 ⊙ at 1 ⊙ at 2 ⊙ ((at 3 ⊙ at 4) ⊙ at 5) ⊙ at 6
         ⊙ ((at 7 ⊙ at 8) ⊙ at 9) ⊙ at 10 ⊙ at 11 ⊙ (((at 12 ⊙ at 13) ⊙ at 14) ⊙ at 15)
  G16  = rn 0 4 ⊙ at 4 ⊙ rn 5 3 ⊙ at 8 ⊙ rn 9 4 ⊙ at 13 ⊙ rn 14 2
  G7   = rn 0 7
  G10R = at 0 ⊙ at 1 ⊙ (at 2 ⊙ at 3) ⊙ at 4 ⊙ at 5 ⊙ at 6 ⊙ rn 7 3
  SR   = ((at 0 ⊙ at 1) ⊙ ((at 2 ⊙ rn 3 5) ⊙ at 8)) ⊙ at 9

  step₁ step₂ step₃ step₄ step₅ step₆ step₇ : TT
  step₁ = interp Lshape (αw ∷ b₁ ∷ DL ∷ b₃ ∷ b₄ ∷ b₅ ∷ [])
  step₂ = rebr 10 S2 (rn 0 10) atoms10
  step₃ = interp (rn 0 10) (replace 3 slide₁ (replace 5 slide₂ (replace 8 slide₃ atoms10)))
  step₄ = rebr 16 S4 G16 atoms16
  step₅ = interp G7 (F₀ ∷ c₁ ∷ F₁ ∷ c₂ ∷ F₂ ∷ c₃ ∷ F₃ ∷ [])
  step₆ = rebr 10 G10R SR atoms10R
  step₇ = interp Rshape (e₁ ∷ e₂ ∷ e₃ ∷ DR⁻ ∷ e₅ ∷ xα ∷ [])

-- The naturality 3-cell of the associator, L → R.
K-α : TT
K-α = step₁ ∗[ 2 ] step₂ ∗[ 2 ] step₃ ∗[ 2 ] step₄ ∗[ 2 ] step₅ ∗[ 2 ] step₆ ∗[ 2 ] step₇

K-α-type : Ty
K-α-type = arr (snd L) (fst L) (fst R)

-- Individual steps, for diagnosis.
steps : List TT
steps = step₁ ∷ step₂ ∷ step₃ ∷ step₄ ∷ step₅ ∷ step₆ ∷ step₇ ∷ []

------------------------------------------------------------------------
-- Typecheck-time certificates for every coherence the construction
-- uses, in its own pasting context (unsubstituted). These are small;
-- the assembled 3-cell K-α (about 3.6·10⁵ syntax nodes) is too large for
-- Agda's typecheck-time normaliser and is certified by running the same
-- certified checker compiled (tools/run/RunAssoc.agda).

module Generic where
  private
    sl₁ sl₂ sl₃ : Ctx × TT
    sl₁ = genFill T₁ (f ∙ (g ∙ θ)) ((assoc⁻ f g u ∗[ 1 ] ((f ∙ g) ∙ θ)) ∗[ 1 ] assoc f g u')
      where f = gv T₁ 2 ; g = gv T₁ 4 ; u = gv T₁ 6 ; u' = gv T₁ 7 ; θ = gv T₁ 8
    sl₂ = genFill T₂ (f ∙ (θ ∙ h)) ((assoc⁻ f u h ∗[ 1 ] ((f ∙ θ) ∙ h)) ∗[ 1 ] assoc f u' h)
      where f = gv T₂ 2 ; u = gv T₂ 4 ; u' = gv T₂ 5 ; θ = gv T₂ 6 ; h = gv T₂ 8
    sl₃ = genFill T₃ (θ ∙ (g ∙ h)) ((assoc⁻ u g h ∗[ 1 ] ((θ ∙ g) ∙ h)) ∗[ 1 ] assoc u' g h)
      where u = gv T₃ 2 ; u' = gv T₃ 3 ; θ = gv T₃ 4 ; g = gv T₃ 6 ; h = gv T₃ 8

  cells : List (Ctx × TT)
  cells =
      genFill TDL (gv TDL 2 ∙ interp kshape θL) (interp (rn 0 5) (mapT (gv TDL 2 ∙_) θL))
    ∷ genFill TDR (interp (rn 0 5) (mapT (_∙ gv TDR 14) θR)) (interp kshape θR ∙ gv TDR 14)
    ∷ sl₁ ∷ sl₂ ∷ sl₃
    ∷ genFill T₄ (segS P₀) (segT Q₀)
    ∷ genFill T₄ (segS P₁) (segT Q₁)
    ∷ genFill T₄ (segS P₂) (segT Q₂)
    ∷ genFill T₄ (segS P₃) (segT Q₃)
    ∷ genRebr 10 S2 (rn 0 10)
    ∷ genRebr 16 S4 G16
    ∷ genRebr 10 G10R SR
    ∷ []
    where
    genRebr : Nat → BT → BT → Ctx × TT
    genRebr n b₁ b₂ = genFill (node (node (leaves n) ∷ [])) (interp b₁ (vgen n)) (interp b₂ (vgen n))

  allCheck : List (Ctx × TT) → Bool
  allCheck []              = true
  allCheck ((Γ , t) ∷ cs) = checks Γ t ∧ allCheck cs

  _ : allCheck cells ≡ true
  _ = refl
