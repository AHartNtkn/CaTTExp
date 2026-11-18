------------------------------------------------------------------------
-- Cylinder contexts Γ↑ = Γ ⊗ D¹ for globular contexts
-- (open-issues C3, C7; notes/free-objects-proofs.md §2;
-- notes/conjectures/naturality-arbitrary-depth.md §2).
--
-- A context is *globular* when the source and target of every variable
-- are variables (pasting contexts, the loop, spheres, ...). For such Γ
-- and Y = all variables, the cylinder context needs no naturality
-- terms K: each variable x : A at level i becomes
--
--   x⁻ : A[in⁻]   (level 3i),   x⁺ : A[in⁺]   (level 3i+1),
--   x↑ : a_x → b_x               (level 3i+2),
--
-- with a_x = (…((x⁻ ∗₀ (τⁿx)↑) ∗₁ (τⁿ⁻¹x)↑) …) ∗ₙ₋₁ (τx)↑ and
--      b_x = (σx)↑ ∗ₙ₋₁ ( … ((σⁿ⁻¹x)↑ ∗₁ ((σⁿx)↑ ∗₀ x⁺)) … ).
--
-- `cyl` is that construction as a function on syntax. Well-formedness
-- of the result (Lemma 1 of the conjecture file) is certified by the
-- checker on each example below. Lemma 2 of free-objects-proofs.md
-- (cylinders commute with context extension: the three variables added
-- for x : A are those of the disc cylinder pulled back along τ_A↑) is
-- checked by `refl` on instances only, including the non-pasting loop;
-- the general statement is proved on paper.
------------------------------------------------------------------------
module CaTTExp.Free.Cylinder where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Free.Builders

------------------------------------------------------------------------
-- The two end renamings.

in⁻ in⁺ : Nat → Sub
in⁻ n = ⟪ map (λ j → var (j + j + j)) (range n) ⟫
in⁺ n = ⟪ map (λ j → var (suc (j + j + j))) (range n) ⟫

lvl : Tm → Nat
lvl (var i) = i
lvl _       = 0

tyAt : Ctx → Nat → Ty
tyAt Γ i with lookup Γ i
... | just A  = A
... | nothing = ⋆

------------------------------------------------------------------------
-- a_x, b_x and x↑ for the variable at level i of Γ. The fuel bounds
-- the dimension; boundary variables have strictly lower dimension.

mutual
  up : Nat → Ctx → Nat → TT
  up fuel Γ i = var (suc (suc (i + i + i))) , cylTy fuel Γ i

  cylTy : Nat → Ctx → Nat → Ty
  cylTy fuel Γ i =
    let a = aT fuel Γ i
        b = bT fuel Γ i
    in arr (snd a) (fst a) (fst b)

  aT : Nat → Ctx → Nat → TT
  aT fuel Γ i =
    let A = tyAt Γ i in
    aSteps fuel Γ 0 (bdry A) (var (i + i + i) , A [ in⁻ (len Γ) ]ty)

  bT : Nat → Ctx → Nat → TT
  bT fuel Γ i =
    let A = tyAt Γ i in
    bSteps fuel Γ 0 (bdry A) (var (suc (i + i + i)) , A [ in⁺ (len Γ) ]ty)

  -- acc ∗ⱼ (tⱼ)↑ for j = 0, 1, …
  aSteps : Nat → Ctx → Nat → List (Tm × Tm) → TT → TT
  aSteps zero       Γ j _              acc = acc
  aSteps (suc fuel) Γ j []             acc = acc
  aSteps (suc fuel) Γ j ((_ , t) ∷ bs) acc =
    aSteps (suc fuel) Γ (suc j) bs (acc ∗[ j ] up fuel Γ (lvl t))

  -- (sⱼ)↑ ∗ⱼ acc for j = 0, 1, …
  bSteps : Nat → Ctx → Nat → List (Tm × Tm) → TT → TT
  bSteps zero       Γ j _              acc = acc
  bSteps (suc fuel) Γ j []             acc = acc
  bSteps (suc fuel) Γ j ((s , _) ∷ bs) acc =
    bSteps (suc fuel) Γ (suc j) bs (up fuel Γ (lvl s) ∗[ j ] acc)

------------------------------------------------------------------------
-- The cylinder context.

dimFuel : Ctx → Nat
dimFuel Γ = suc (dimCtx Γ)

cylVar : Ctx → Nat → Ty
cylVar Γ i = cylTy (dimFuel Γ) Γ i

cyl : Ctx → Ctx
cyl ε       = ε
cyl (Γ ▸ A) =
  cyl Γ ▸ A [ in⁻ (len Γ) ]ty ▸ A [ in⁺ (len Γ) ]ty ▸ cylVar (Γ ▸ A) (len Γ)

------------------------------------------------------------------------
-- Examples: the cylinder contexts are well formed (certified).

private
  v : Nat → Tm
  v = var

D⁰ D¹ D² Pair Loop Loop² : Ctx
D⁰   = ctxOf (disc 0)
D¹   = ctxOf (disc 1)
D²   = ctxOf (disc 2)
Pair = ctxOf (node (leaf ∷ leaf ∷ []))
-- The loop (x, e : x → x) and a 2-loop on it (α : e ⇒ e): not pasting
-- contexts, but globular.
Loop  = ε ▸ ⋆ ▸ arr ⋆ (v 0) (v 0)
Loop² = Loop ▸ arr (arr ⋆ (v 0) (v 0)) (v 1) (v 1)

cyl-D⁰ : cyl D⁰ ⊢ctx
cyl-D⁰ = certifyCtx (cyl D⁰)

cyl-D¹ : cyl D¹ ⊢ctx
cyl-D¹ = certifyCtx (cyl D¹)

cyl-D² : cyl D² ⊢ctx
cyl-D² = certifyCtx (cyl D²)

cyl-Pair : cyl Pair ⊢ctx
cyl-Pair = certifyCtx (cyl Pair)

cyl-Loop : cyl Loop ⊢ctx
cyl-Loop = certifyCtx (cyl Loop)

cyl-Loop² : cyl Loop² ⊢ctx
cyl-Loop² = certifyCtx (cyl Loop²)

-- The cylinder on the 2-disc has the expected top cell
-- α↑ : (α⁻ ∗₀ y↑) ∗₁ g↑ → f↑ ∗₁ (x↑ ∗₀ α⁺)   (levels: α⁻ 12, α⁺ 13).
private
  c2v : Nat → TT
  c2v i = var i , tyAt (cyl D²) i

_ : lastTy (cyl D²) ≡
    arr (snd ((c2v 12 ∗[ 0 ] c2v 5) ∗[ 1 ] c2v 11))
        (fst ((c2v 12 ∗[ 0 ] c2v 5) ∗[ 1 ] c2v 11))
        (fst (c2v 8 ∗[ 1 ] (c2v 2 ∗[ 0 ] c2v 13)))
_ = refl

------------------------------------------------------------------------
-- Lemma 2 of free-objects-proofs.md on instances: the whole extension
-- (x⁻ : A[in⁻], x⁺ : A[in⁺], x↑ : a_x → b_x) that `cyl` adds for a new
-- variable x : A is the extension (d⁻, d⁺, d↑) of the disc cylinder,
-- substituted along τ_A↑ (the cylinder of the substitution classifying
-- A), extended by x⁻, x⁺.

-- The last three types of a context.
last3 : Ctx → Ty × Ty × Ty
last3 (Γ ▸ A ▸ B ▸ C) = A , B , C
last3 _               = ⋆ , ⋆ , ⋆

sub3 : Ty × Ty × Ty → Sub → Ty × Ty × Ty
sub3 (A , B , C) σ = A [ σ ]ty , B [ σ ]ty , C [ σ ]ty

-- Loop: e : x → x. τ_A↑ sends the D¹-cylinder variables
-- (x⁻ x⁺ x↑ y⁻ y⁺ y↑ f⁻ f⁺) to (x⁻ x⁺ x↑ x⁻ x⁺ x↑ e⁻ e⁺).
_ : last3 (cyl Loop) ≡
    sub3 (last3 (cyl D¹)) ⟪ v 0 ∷ v 1 ∷ v 2 ∷ v 0 ∷ v 1 ∷ v 2 ∷ v 3 ∷ v 4 ∷ [] ⟫
_ = refl

-- 2-loop: α : e ⇒ e. τ_A↑ sends the D²-cylinder variables
-- (x y f g, each as ⁻ ⁺ ↑, then α⁻ α⁺) to (x x e e, ..., α⁻ α⁺).
_ : last3 (cyl Loop²) ≡
    sub3 (last3 (cyl D²)) ⟪ v 0 ∷ v 1 ∷ v 2 ∷ v 0 ∷ v 1 ∷ v 2
                          ∷ v 3 ∷ v 4 ∷ v 5 ∷ v 3 ∷ v 4 ∷ v 5
                          ∷ v 6 ∷ v 7 ∷ [] ⟫
_ = refl

-- Composable pair: g : y → z is pulled back from D¹ along
-- (x y f) ↦ (y z g), i.e. levels (3 4 5 9 10 11 12 13).
_ : last3 (cyl Pair) ≡
    sub3 (last3 (cyl D¹)) ⟪ v 3 ∷ v 4 ∷ v 5 ∷ v 9 ∷ v 10 ∷ v 11 ∷ v 12 ∷ v 13 ∷ [] ⟫
_ = refl
