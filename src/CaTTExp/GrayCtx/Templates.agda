------------------------------------------------------------------------
-- The repaired Gray rule of ledger D3 (notes/conjectures/answered/
-- gray-tensor-of-contexts-rule-2026-11-18.md), for one globe factor
-- D¹, in both factor orders:
--
--   right:  M ⊗ D¹   (generator x ⊗ e, a first),
--   left:   D¹ ⊗ M   (generator e ⊗ x, the project's convention).
--
-- * (B) boundary templates: a type B over U_{p,1} (the cylinder prefix
--   `diskPre`) is accepted iff, for every k < p + 1 and sign ε, the
--   k-dimensional free variables of its k-endpoint ε are exactly the
--   support of the tensor-atom row θ^ε_k (`checkB`).
-- * (C) coherence templates: a term C over T₁P = P ⊗ D¹ is accepted iff
--   it has type B_{p,1}[Θ_{h,e}] and its top-dimensional free
--   variables are exactly {z ⊗ e : z ∈ Var_p(P)} (`checkC`).
-- * The translation ⟦t, y⟧ and the context T₁M with x_y : B[Θ_{x,y}]
--   (equations (5)–(8) of the answer), for any context M whose
--   coherence terms have templates in the table `Ctmpl`.
--
-- The B-templates are the explicit disk types TsE of
-- CaTTExp.GrayCtx.NaturalExplicit (proved well typed for every p in
-- CaTTExp.GrayCtx.NaturalAll). The table of C-templates holds binary
-- composition of 1-cells. Everything here is raw syntax; the checks are
-- in CaTTExp.GrayCtx.Checks.Templates.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Templates where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left; Comp₂T)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.GrayCtx.NaturalExplicit using (TsE)
open import CaTTExp.GrayCtx.NaturalAll using (cylE)
open import CaTTExp.GrayCtx.Elab using (vcomp; assoc; assoc⁻; _▹_; _◃_; tyOf)

------------------------------------------------------------------------
-- Lists and finite sets.

private
  mapL : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  range : Nat → List Nat
  range zero    = []
  range (suc n) = range n ++ (n ∷ [])

  filterL : (Nat → Bool) → List Nat → List Nat
  filterL p []       = []
  filterL p (x ∷ xs) = if p x then x ∷ filterL p xs else filterL p xs

------------------------------------------------------------------------
-- Signed, dimension-indexed free variables.

-- FV_k(t) in Γ.
fvK : Ctx → Nat → Tm → List Nat
fvK Γ k t = filterL (λ x → dimV Γ x ==ℕ k) (fvTm t)

-- bd_k^ε(A): the k-dimensional ε-endpoint of a type A (k < dim A).
bdK : Nat → Bool → Ty → Maybe Tm
bdK k sg ⋆           = nothing
bdK k sg (arr B s t) = if dim B ==ℕ k then just (if sg then t else s) else bdK k sg B

-- ε = false for −, true for +.
neg : Bool → Bool
neg = not

------------------------------------------------------------------------
-- The tensor-atom rows of D^p ⊗ D¹ (right) and D¹ ⊗ D^p (left), as
-- levels of the layout of `diskPre` (copy a, copy b, generators;
-- N = 2p + 1 levels per copy).

-- The level of a_i^ε in D^p (a_p^± = a_p).
lvA : Nat → Nat → Bool → Nat
lvA p i sg = if i ==ℕ p then dbl p else (if sg then suc (dbl i) else dbl i)

-- b₀^ε ⊗ a  /  a ⊗ b₀^ε : copy b for ε = +.
copyAt : Nat → Bool → Nat → Nat
copyAt p sg v = if sg then suc (dbl p) + v else v

-- e ⊗ a  /  a ⊗ e : the generator block.
genAt : Nat → Nat → Nat
genAt p v = suc (dbl p) + (suc (dbl p) + v)

parity : Nat → Bool          -- (−1)^i = −1
parity zero          = false
parity (suc zero)    = true
parity (suc (suc i)) = parity i

flipIf : Bool → Bool → Bool
flipIf b sg = if b then neg sg else sg

-- θ^ε_k for k < p + 1.
theta : Side → Nat → Nat → Bool → List Nat
-- right, a first: a_k^ε ⊗ b₀^{(−1)^k ε}  +  a_{k−1}^ε ⊗ e
theta right p zero    sg = copyAt p (flipIf (parity 0) sg) (lvA p 0 sg) ∷ []
theta right p (suc k) sg = copyAt p (flipIf (parity (suc k)) sg) (lvA p (suc k) sg) ∷ genAt p (lvA p k sg) ∷ []
-- left, b first: b₀^ε ⊗ a_k^ε  +  e ⊗ a_{k−1}^{−ε}
theta left  p zero    sg = copyAt p sg (lvA p 0 sg) ∷ []
theta left  p (suc k) sg = copyAt p sg (lvA p (suc k) sg) ∷ genAt p (lvA p k (neg sg)) ∷ []

-- Rule (B) for a candidate type B over U = U_{p,1}.
checkB : Side → Nat → Ctx → Ty → Bool
checkB sd p U B = (dim B ==ℕ suc p) ∧ all row (range (suc p))
  where
  row1 : Nat → Bool → Bool
  row1 k sg with bdK k sg B
  ... | just t  = ≈? (fvK U k t) (theta sd p k sg)
  ... | nothing = false
  row : Nat → Bool
  row k = row1 k false ∧ row1 k true

-- The B-templates: B_{p,1} = TsE sd p over diskPre (TsE sd) p.
Btmpl : Side → Nat → Ty
Btmpl = TsE

Uctx : Side → Nat → Ctx
Uctx sd p = diskPre (TsE sd) p

------------------------------------------------------------------------
-- The faces of a cell, in disk order: levels 2i, 2i+1 are the
-- i-dimensional source and target, 2p is the cell itself.

faces : Tm → Ty → List Tm
faces x A = go A ++ (x ∷ [])
  where
  go : Ty → List Tm
  go ⋆           = []
  go (arr B s t) = go B ++ (s ∷ t ∷ [])

fromList : List Tm → Sub
fromList ts = go ⟨⟩ ts
  where
  go : Sub → List Tm → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ t) ts

subList : Sub → List Tm
subList ⟨⟩       = []
subList (σ ,ₛ t) = subList σ ++ (t ∷ [])

------------------------------------------------------------------------
-- The translation ⟦t, y⟧ for y ∈ {0, 1, e} (the vertices and the edge
-- of D¹), into a layout with N = len M levels per copy, given a table
-- of C-templates.

data Y : Set where
  y0 y1 ye : Y

module Tr (Ctmpl : Ctx → Ty → Maybe Tm) (N : Nat) where
  mutual
    tr : Tm → Y → Maybe Tm
    tr (var x)     y0 = just (var x)
    tr (var x)     y1 = just (var (N + x))
    tr (var x)     ye = just (var (N + (N + x)))
    tr (coh P A σ) y0 = trS σ y0 >>= λ σ' → just (coh P A σ')
    tr (coh P A σ) y1 = trS σ y1 >>= λ σ' → just (coh P A σ')
    tr (coh P A σ) ye =
      Ctmpl P A >>= λ C →
      trS σ y0 >>= λ σ₀ → trS σ y1 >>= λ σ₁ → trS σ ye >>= λ σₑ →
      just (C [ fromList (subList σ₀ ++ subList σ₁ ++ subList σₑ) ]tm)
    tr (cst ())    _

    trS : Sub → Y → Maybe Sub
    trS ⟨⟩       y = just ⟨⟩
    trS (σ ,ₛ t) y = trS σ y >>= λ σ' → tr t y >>= λ t' → just (σ' ,ₛ t')

  private
    mapM : List Tm → Y → Maybe (List Tm)
    mapM []       y = just []
    mapM (t ∷ ts) y = tr t y >>= λ t' → mapM ts y >>= λ ts' → just (t' ∷ ts')

  -- Θ_{x,e}: the substitution U_{p,1} → T₁M for a p-cell x : A.
  Θe : Tm → Ty → Maybe Sub
  Θe x A =
    let fs = faces x A in
    mapM fs y0 >>= λ f₀ → mapM fs y1 >>= λ f₁ → mapM (dropLast fs) ye >>= λ fₑ →
    just (fromList (f₀ ++ f₁ ++ fₑ))
    where
    dropLast : List Tm → List Tm
    dropLast []           = []
    dropLast (_ ∷ [])     = []
    dropLast (t ∷ u ∷ ts) = t ∷ dropLast (u ∷ ts)

  -- The type of x_y.
  trTy : Ty → Y → Maybe Ty
  trTy ⋆           y = just ⋆
  trTy (arr A s t) y = trTy A y >>= λ A' → tr s y >>= λ s' → tr t y >>= λ t' → just (arr A' s' t')

------------------------------------------------------------------------
-- T₁M: copies 0 and 1 of M, then x_e : B_{p,1}[Θ_{x,e}] for each x.

module T1 (sd : Side) (Ctmpl : Ctx → Ty → Maybe Tm) where
  T1 : Ctx → Maybe Ctx
  T1 M = layer y0 M >>= λ Γ₀ → layer y1 M >>= λ Γ₁ → gens M >>= λ Γₑ →
         just (Γ₀ ++C (Γ₁ ++C Γₑ))
    where
    open Tr Ctmpl (len M)
    _++C_ : Ctx → Ctx → Ctx
    Γ ++C ε       = Γ
    Γ ++C (Δ ▸ A) = (Γ ++C Δ) ▸ A
    layer : Y → Ctx → Maybe Ctx
    layer y ε       = just ε
    layer y (Γ ▸ A) = layer y Γ >>= λ Γ' → trTy A y >>= λ A' → just (Γ' ▸ A')
    gens : Ctx → Maybe Ctx
    gens ε       = just ε
    gens (Γ ▸ A) = gens Γ >>= λ Γ' → Θe (var (len Γ)) A >>= λ θ →
                   just (Γ' ▸ (Btmpl sd (dim A) [ θ ]ty))

------------------------------------------------------------------------
-- C-templates. Binary composition of 1-cells, h = f ; g over
-- P = (a, b, f, c, g), in T₁P = cylE sd P: copies at 0–4 and 5–9,
-- generators e_a = 10, e_b = 11, e⊗f = 12, e_c = 13, e⊗g = 14.

Comp₂P : Ctx
Comp₂P = ctxOf Comp₂T

compA : Ty
compA = arr ⋆ (var 0) (var 3)

compC : Side → Maybe Tm
compC sd = go sd
  where
  Q = cylE sd Comp₂P
  f₀ = var 2 ; g₀ = var 4 ; f₁ = var 7 ; g₁ = var 9
  ea = var 10 ; eb = var 11 ; ef = var 12 ; ec = var 13 ; eg = var 14
  go : Side → Maybe Tm
  -- left, e⊗x : x₀ ; e_t ⇒ e_s ; x₁.  (f₀;g₀);e_c ⇒ e_a;(f₁;g₁)
  go left =
    assoc Q f₀ g₀ ec >>= λ s₁ → (Q ◃ f₀) eg >>= λ s₂ →
    assoc⁻ Q f₀ eb g₁ >>= λ s₃ → (Q ▹ ef) g₁ >>= λ s₄ →
    assoc Q ea f₁ g₁ >>= λ s₅ → vcomp Q (s₁ ∷ s₂ ∷ s₃ ∷ s₄ ∷ s₅ ∷ [])
  -- right, x⊗e : e_s ; x₁ ⇒ x₀ ; e_t.  e_a;(f₁;g₁) ⇒ (f₀;g₀);e_c
  go right =
    assoc⁻ Q ea f₁ g₁ >>= λ s₁ → (Q ▹ ef) g₁ >>= λ s₂ →
    assoc Q f₀ eb g₁ >>= λ s₃ → (Q ◃ f₀) eg >>= λ s₄ →
    assoc⁻ Q f₀ g₀ ec >>= λ s₅ → vcomp Q (s₁ ∷ s₂ ∷ s₃ ∷ s₄ ∷ s₅ ∷ [])

-- The table: the only coherence it knows is binary composition of
-- 1-cells, in its canonical form (as produced by `vcomp`).
Ctmpl : Side → Ctx → Ty → Maybe Tm
Ctmpl sd P A = if (P ==Ctx Comp₂P) ∧ (A ==Ty compA) then compC sd else nothing

-- Rule (C) for a template C of the generic operation h = coh P A id of
-- dimension p: C has type B_{p,1}[Θ_{h,e}] in T₁P, and its top
-- free variables are exactly the generators z ⊗ e of the p-cells z of P.
checkC : Side → Ctx → Ty → Tm → Bool
checkC sd P A C with T1.T1 sd (Ctmpl sd) P
... | nothing = false
... | just Q  = typeOK ∧ ≈? (fvK Q (suc p) C) tops
  where
  N = len P
  p = dim A
  open Tr (Ctmpl sd) N
  idP : Sub
  idP = fromList (mapL var (range N))
  h = coh P A idP
  typeOK : Bool
  typeOK with Θe h A | tyOf Q C
  ... | just θ | just B = B ==Ty (Btmpl sd p [ θ ]ty)
  ... | _      | _      = false
  tops : List Nat
  tops = mapL (λ z → N + (N + z)) (filterL (λ z → dimV P z ==ℕ p) (range N))

-- Rule (C) for the template in the table.
compOK : Side → Bool
compOK sd with compC sd
... | just C  = checkC sd Comp₂P compA C
... | nothing = false
