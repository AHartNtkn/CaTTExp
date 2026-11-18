------------------------------------------------------------------------
-- The cylinder Γ ⊗ D¹ (and D¹ ⊗ Γ) of a *globular* context, defined
-- disk by disk (ledger item D13).
--
-- For a variable x of dimension m of Γ, the classifying map
-- χ_x : D^m → Γ sends the generic m-cell to x. The generator x⊗e is
-- given the type of the top generator of D^m ⊗ D¹, renamed along
-- χ_x ⊗ D¹. So the elaborator runs only on disks, once per dimension,
-- and every other generator type is a renaming of a disk one.
--
-- CaTTExp.GrayCtx.NaturalWF proves that this context is well formed
-- for every well-formed globular Γ of dimension ≤ k, given that the
-- top generator types of the disks D⁰ … D^k are well typed. The disk
-- facts are certified for k ≤ 5 by CaTTExp.GrayCtx.Checks.Natural,
-- which also checks that the result agrees syntactically with
-- `cyl sd 1` on every tested globular context.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Natural where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.CylGen using (Side; right; left; module Gen)
open import Agda.Builtin.Nat using (_*_)

------------------------------------------------------------------------
-- Renaming along a function on levels.

mutual
  rnTy : (Nat → Nat) → Ty → Ty
  rnTy f ⋆           = ⋆
  rnTy f (arr A t u) = arr (rnTy f A) (rnTm f t) (rnTm f u)

  rnTm : (Nat → Nat) → Tm → Tm
  rnTm f (var i)     = var (f i)
  rnTm f (coh Δ A σ) = coh Δ A (rnSub f σ)
  rnTm f (cst k)     = cst k

  rnSub : (Nat → Nat) → Sub → Sub
  rnSub f ⟨⟩       = ⟨⟩
  rnSub f (σ ,ₛ t) = rnSub f σ ,ₛ rnTm f t

------------------------------------------------------------------------
-- Contexts given by their types at each level.

mkCtx : Nat → (Nat → Ty) → Ctx
mkCtx zero    g = ε
mkCtx (suc n) g = mkCtx n g ▸ g n

orStar : Maybe Ty → Ty
orStar (just A) = A
orStar nothing  = ⋆

tyAt : Ctx → Nat → Ty
tyAt Γ i = orStar (lookup Γ i)

------------------------------------------------------------------------
-- Disks. D^m has levels 0 … 2m: the pair (2k, 2k+1) is the source and
-- target of dimension k, and 2m is the generic m-cell.

dbl : Nat → Nat
dbl zero    = zero
dbl (suc k) = suc (suc (dbl k))

half : Nat → Nat
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

aL : Nat → Ty
aL zero    = ⋆
aL (suc k) = arr (aL k) (var (dbl k)) (var (suc (dbl k)))

aD : Nat → Ty
aD d = aL (half d)

Disk : Nat → Ctx
Disk m = mkCtx (suc (dbl m)) aD

------------------------------------------------------------------------
-- Classifying maps in a globular context.

srcT tgtT : Ty → Nat
srcT (arr _ (var s) _) = s
srcT _                 = zero
tgtT (arr _ _ (var t)) = t
tgtT _                 = zero

src tgt dimV : Ctx → Nat → Nat
src Γ x  = srcT (tyAt Γ x)
tgt Γ x  = tgtT (tyAt Γ x)
dimV Γ x = dim (tyAt Γ x)

-- χ_x on the levels of D^k, for x of dimension k.
chiK : Ctx → Nat → Nat → Nat → Nat
chiK Γ zero    x d = x
chiK Γ (suc k) x d =
  if d ==ℕ suc (suc (dbl k)) then x
  else (if d ==ℕ suc (dbl k) then tgt Γ x
  else chiK Γ k (src Γ x) d)

chi : Ctx → Nat → Nat → Nat
chi Γ x = chiK Γ (dimV Γ x) x

-- Globular: every type is ⋆ or has variables as source and target.
globTy : Ty → Bool
globTy ⋆                       = true
globTy (arr _ (var _) (var _)) = true
globTy _                       = false

globular : Ctx → Bool
globular ε       = true
globular (Γ ▸ A) = globular Γ ∧ globTy A

------------------------------------------------------------------------
-- The cylinder of Γ, given the types Ts j of the top generators of the
-- disk cylinders D^j ⊗ D¹. Layout as in Cylinder (p = 1): copy 0,
-- copy 1, then the generators, each block in the order of Γ.

-- χ ⊗ D¹ on levels: D^m ⊗ D¹ (M = 2m+1 levels per block) into Γ ⊗ D¹.
hmap : Nat → Nat → (Nat → Nat) → Nat → Nat
hmap N M χ j =
  if j <ℕ M then χ j
  else (if j <ℕ (M + M) then (N + χ (j ∸ M))
  else (N + (N + χ ((j ∸ M) ∸ M))))

gN : (Nat → Ty) → Ctx → Nat → Ty
gN Ts Γ i =
  if i <ℕ N then tyAt Γ i
  else (if i <ℕ (N + N) then rnTy (λ y → N + y) (tyAt Γ (i ∸ N))
  else gen ((i ∸ N) ∸ N))
  where
  N = len Γ
  gen : Nat → Ty
  gen x = rnTy (hmap N (suc (dbl (dimV Γ x))) (chi Γ x)) (Ts (dimV Γ x))

cylWith : (Nat → Ty) → Ctx → Ctx
cylWith Ts Γ = mkCtx (len Γ + (len Γ + len Γ)) (gN Ts Γ)

-- D^m ⊗ D¹ without its top generator: the context of Ts m.
diskPre : (Nat → Ty) → Nat → Ctx
diskPre Ts m = mkCtx (suc (dbl m) + (suc (dbl m) + dbl m)) (gN Ts (Disk m))

------------------------------------------------------------------------
-- The disk types, computed by the elaborator of Cylinder. A failure of
-- the elaborator gives ⋆; Checks.Natural certifies that this does not
-- happen for m ≤ 5 (the result agrees with `cyl` on the disks).

nth : List Ty → Nat → Ty
nth []       _       = ⋆
nth (A ∷ _)  zero    = A
nth (_ ∷ As) (suc n) = nth As n

snocL : List Ty → Ty → List Ty
snocL As A = As ++ (A ∷ [])

diskTy : Side → (Nat → Ty) → Nat → Ty
diskTy sd Ts m = orStar (Gen.genTy sd (Disk m) 1 0 (diskPre Ts m) (dbl m))

-- [T₀, …, T_k].
diskTys : Side → Nat → List Ty
diskTys sd zero    = diskTy sd (λ _ → ⋆) 0 ∷ []
diskTys sd (suc k) = let L = diskTys sd k in snocL L (diskTy sd (nth L) (suc k))

-- T_m.
TsF : Side → Nat → Ty
TsF sd m = nth (diskTys sd m) m

-- Γ ⊗ D¹ (right) and D¹ ⊗ Γ (left), for globular Γ.
cylN : Side → Ctx → Ctx
cylN sd Γ = cylWith (nth (diskTys sd (dimCtx Γ))) Γ
