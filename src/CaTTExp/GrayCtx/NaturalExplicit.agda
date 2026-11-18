------------------------------------------------------------------------
-- The disk cylinder types T_m of CaTTExp.GrayCtx.Natural, written out
-- with the derived whiskering rules of CaTTExp.Derived instead of the
-- elaborator (no fuel, every m).
--
-- For x of dimension m with source s and target t, the generator x⊗e
-- has type
--
--     X_{m+1}(x_ε) → Y_{m+1}(x_ε′)
--
-- where X = srcW, Y = tgtW are two families of whiskerings,
--
--     L_d c = L′_{d−1} c ▹_{d−2} (t_{d−2} ⊗ e)
--     R_d c = (s_{d−2} ⊗ e) ◃_{d−2} R′_{d−1} c       (L_0 = L_1 = id, R too)
--
-- with L′ = R, R′ = L for Γ ⊗ D¹ (right) and L′ = L, R′ = R for
-- D¹ ⊗ Γ (left); X = L′, Y = R′. The copy (a = 0, b = 1) of the
-- cell each whiskering applies to is `cpy`. Checks.NaturalAgree checks
-- that this agrees with the elaborator for m ≤ 5, both sides;
-- CaTTExp.GrayCtx.NaturalAll proves it well typed for every m.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.NaturalExplicit where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left; odd)
open import CaTTExp.GrayCtx.Natural
open import CaTTExp.Derived
open import CaTTExp.DerivedBoundary

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

srcTm tgtTm : Ty → Tm
srcTm (arr _ s _) = s
srcTm ⋆           = var 0
tgtTm (arr _ _ t) = t
tgtTm ⋆           = var 0

data Which : Set where
  L R : Which

nxt : Side → Which → Which
nxt right L = R
nxt right R = L
nxt left  w = w

srcW tgtW : Side → Which
srcW sd = nxt sd L
tgtW sd = nxt sd R

-- The copy that the whiskering W_d applies to: true for copy b.
cpy : Side → Which → Nat → Bool
cpy right L d       = odd d
cpy right R zero    = false
cpy right R (suc d) = odd d
cpy left  L _       = false
cpy left  R _       = true

-- A context Γ laid out as a disk cylinder prefix with N levels per copy.
module G (sd : Side) (Γ : Ctx) (N : Nat) where
  tyE : Tm → Ty
  tyE (var i)     = tyAt Γ i
  tyE (coh _ A σ) = A [ σ ]ty
  tyE (cst ())

  cell : Bool → Nat → Tm
  cell b y = var (if b then N + y else y)

  gen : Nat → Tm
  gen v = var (N + (N + v))

  -- c ▹ₖ h, k = dim h − 1.
  rwE : Tm → Tm → Tm
  rwE c h = let C = tyE c ; H = tyE h ; k = pred (dim H) in
            coh (BK k (dim C ∸ suc k)) (wK k (dim C ∸ suc k)) (σR c C (tgtTm H) h)

  -- h ◃ₖ c, k = dim h − 1 (for dim c = dim h, the composite h ;ₖ c).
  lwE : Tm → Tm → Tm
  lwE h c = let C = tyE c ; H = tyE h ; k = pred (dim H) in
            coh (LK k (dim C ∸ suc k)) (lK k (dim C ∸ suc k)) (σL k (dim C ∸ suc k) h (srcTm H) c C)

  whiskE : Which → Nat → Tm → Tm
  whiskE _ zero          c = c
  whiskE _ (suc zero)    c = c
  whiskE L (suc (suc d)) c = rwE (whiskE (nxt sd L) (suc d) c) (gen (suc (dbl d)))
  whiskE R (suc (suc d)) c = lwE (gen (dbl d)) (whiskE (nxt sd R) (suc d) c)

  -- The two sides of the type of y⊗e, y a cell of dimension q.
  Sc Tc : Nat → Nat → Tm
  Sc q y = whiskE (srcW sd) (suc q) (cell (cpy sd (srcW sd) (suc q)) y)
  Tc q y = whiskE (tgtW sd) (suc q) (cell (cpy sd (tgtW sd) (suc q)) y)

  -- The type of x⊗e for the top cell x (level 2m) of D^m.
  topTy : Nat → Ty
  topTy m = arr (tyE (Sc m (dbl m))) (Sc m (dbl m)) (Tc m (dbl m))

-- T_m, given the T_j for j < m.
StepTy : Side → (Nat → Ty) → Nat → Ty
StepTy sd Ts m = G.topTy sd (diskPre Ts m) (suc (dbl m)) m

diskTysE : Side → Nat → List Ty
diskTysE sd zero    = StepTy sd (λ _ → ⋆) 0 ∷ []
diskTysE sd (suc k) = let Ls = diskTysE sd k in snocL Ls (StepTy sd (nth Ls) (suc k))

TsE : Side → Nat → Ty
TsE sd m = nth (diskTysE sd m) m
