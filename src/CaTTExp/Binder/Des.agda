------------------------------------------------------------------------
-- The destructors (DES) of spec §3.3 as a binder interface (ledger
-- S26e, E4):
--
--   Γ ⊢ t inv    Γ ⊢ t : u → v
--   ──────────────────────────────────────────────────────── (DES)
--   Γ ⊢ t⁻ˡ : v → u      Γ ⊢ t⁻ʳ : v → u
--   Γ ⊢ λ_t : t⁻ˡ ; t → id_v      Γ ⊢ ρ_t : t ; t⁻ʳ → id_u
--
-- for t an n-cell, n ≥ 1. Each destructor at each dimension is a
-- former with an empty telescope and selector 0:
--
--   linv n, rinv n, unitL n, unitR n      (n ≥ 1, the dimension of t)
--
-- Its arguments inhabit the n-disk Dⁿ (the boundary of t, then t),
-- written with bound variables, whose top entry t is marked inv. So
-- the premise `Γ ⊢ t inv` is the kernel's mark premise on that entry,
-- decided by the kernel's `mark` parameter (CaTTExp.Binder.TypingWith).
-- The result types are those of (DES): t⁻ˡ ; t and t ; t⁻ʳ are the
-- standard composite of n-cells over Dⁿ ∨ Dⁿ, and id_v the standard
-- identity, both coherences over pasting contexts. The cell argument of
-- every destructor is its top entry 2n (CaTTExp.Gray.DesSide's
-- `cellArg`).
--
-- There are no equations (no β or η), as in the spec. (DES-inv), "the
-- destructors are inv", belongs to the mark judgment, not to this
-- interface.
--
-- The construction is over any set B of formers into which DES injects
-- (`inj`), so that DES can sit beside other binders (INIT). `desBinders`
-- is DES alone.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Embed using (Binders)

module CaTTExp.Binder.Des where

data DesKind : Set where
  linvK rinvK unitLK unitRK : DesKind

-- A destructor: its kind and the dimension of its cell argument.
data DesF : Set where
  des : DesKind → Nat → DesF

pattern linv n  = des linvK n
pattern rinv n  = des rinvK n
pattern unitL n = des unitLK n
pattern unitR n = des unitRK n

private
  kcode : DesKind → Nat
  kcode linvK  = 0
  kcode rinvK  = 1
  kcode unitLK = 2
  kcode unitRK = 3

  kdecode : Nat → DesKind
  kdecode 0 = linvK
  kdecode 1 = rinvK
  kdecode 2 = unitLK
  kdecode _ = unitRK

  kdecode-code : ∀ k → kdecode (kcode k) ≡ k
  kdecode-code linvK  = refl
  kdecode-code rinvK  = refl
  kdecode-code unitLK = refl
  kdecode-code unitRK = refl

  T∧ : ∀ {a b} → T (a ∧ b) → T a × T b
  T∧ {true} p = tt , p

_==D_ : DesF → DesF → Bool
des k n ==D des l m = (kcode k ==ℕ kcode l) ∧ (n ==ℕ m)

==D-sound : ∀ b c → T (b ==D c) → b ≡ c
==D-sound (des k n) (des l m) p =
  let (a , b) = T∧ {kcode k ==ℕ kcode l} p in
  cong₂ des (trans (sym (kdecode-code k)) (trans (cong kdecode (==ℕ-sound _ _ a)) (kdecode-code l)))
            (==ℕ-sound n m b)

==D-refl : ∀ b → T (b ==D b)
==D-refl (des k n) with kcode k ==ℕ kcode k | ==ℕ-refl (kcode k)
... | true | _ = ==ℕ-refl n

-- The position of the cell argument of a destructor at dimension n.
cellArgD : DesF → Maybe Nat
cellArgD (des _ n) = just (n + n)

------------------------------------------------------------------------
-- The construction.

module DesConstruction (K B : Set) (inj : DesF → B) where

  open Syntax K B

  -- Disks with free variables (bodies of coherences). Dⁿ has 2n + 1
  -- entries; its top entry 2n has type `tyD n`.
  tyD : Nat → Ty
  tyD zero    = ⋆
  tyD (suc n) = arr (tyD n) (var (n + n)) (var (suc (n + n)))

  diskD : Nat → Ctx
  diskD zero    = ε ▸ ⋆
  diskD (suc n) = diskD n ▸ tyD n ▸ tyD (suc n)

  -- Composition of (n+1)-cells α : f → g, β : g → h, over the pasting
  -- context Dⁿ⁺¹ ∨ Dⁿ⁺¹ = Dⁿ⁺¹, h, β (f = 2n, g = 2n+1, α = 2n+2,
  -- h = 2n+3, β = 2n+4).
  compPC : Nat → Ctx
  compPC n = diskD (suc n) ▸ tyD n ▸ arr (tyD n) (var (suc (n + n))) (var (3 + (n + n)))

  -- bd: the boundary below f (2n terms).
  comp : Nat → Sub → Tm → Tm → Tm → Tm → Tm → Tm
  comp n bd f g α h β =
    coh (compPC n) (arr (tyD n) (var (n + n)) (var (3 + (n + n))))
        (bd ,ₛ f ,ₛ g ,ₛ α ,ₛ h ,ₛ β)

  -- The identity (n+1)-cell on an n-cell f.
  idc : Nat → Sub → Tm → Tm
  idc n bd f = coh (diskD n) (arr (tyD n) (var (n + n)) (var (n + n))) (bd ,ₛ f)

  -- Disks with bound variables (argument telescopes).
  b0 : Nat → Tm
  b0 = bvar 0

  -- The first k bound variables.
  bvs : Nat → Sub
  bvs zero    = ⟨⟩
  bvs (suc k) = bvs k ,ₛ b0 k

  tyB : Nat → Ty
  tyB zero    = ⋆
  tyB (suc n) = arr (tyB n) (b0 (n + n)) (b0 (suc (n + n)))

  diskB : Nat → Ctx
  diskB zero    = ε ▸ ⋆
  diskB (suc n) = diskB n ▸ tyB n ▸ tyB (suc n)

  -- D^{n+1} with its top entry marked inv.
  argsD : Nat → Ctx
  argsD n = diskB n ▸ tyB n ▸[ minv ∷ [] ] tyB (suc n)

  isε : Ctx → Bool
  isε ε = true
  isε _ = false

  ----------------------------------------------------------------------
  -- The interface. A destructor at dimension suc n has cell t = 2n+2,
  -- t : u → v with u = 2n, v = 2n+1, over the boundary bvs (2n).

  side : DesF → Nat → Ctx → Bool
  side (des _ zero)    y Δ = false
  side (des _ (suc n)) y Δ = (y ==ℕ 0) ∧ isε Δ

  args : DesF → Nat → Ctx → Ctx
  args (des _ zero)    y Δ = ε
  args (des _ (suc n)) y Δ = argsD n

  -- The destructor of kind k applied to the arguments themselves.
  self : DesKind → Nat → Tm
  self k n = bnd (inj (des k (suc n))) 0 ε (bvs (3 + (n + n)))

  res : DesF → Nat → Ctx → Ty
  res (des _ zero) y Δ = ⋆
  res (linv (suc n)) y Δ = arr (tyB n) (b0 (suc (n + n))) (b0 (n + n))
  res (rinv (suc n)) y Δ = arr (tyB n) (b0 (suc (n + n))) (b0 (n + n))
  res (unitL (suc n)) y Δ =
    arr (arr (tyB n) (b0 (suc (n + n))) (b0 (suc (n + n))))
        (comp n (bvs (n + n)) (b0 (suc (n + n))) (b0 (n + n)) (self linvK n)
                              (b0 (suc (n + n))) (b0 (suc (suc (n + n)))))
        (idc n (bvs (n + n)) (b0 (suc (n + n))))
  res (unitR (suc n)) y Δ =
    arr (arr (tyB n) (b0 (n + n)) (b0 (n + n)))
        (comp n (bvs (n + n)) (b0 (n + n)) (b0 (suc (n + n))) (b0 (suc (suc (n + n))))
                              (b0 (n + n)) (self rinvK n))
        (idc n (bvs (n + n)) (b0 (n + n)))

desBinders : (K : Set) → Binders K
desBinders K = record
  { B         = DesF
  ; _==B_     = _==D_
  ; ==B-sound = ==D-sound
  ; bside     = side
  ; bargs     = args
  ; bres      = res
  }
  where open DesConstruction K DesF (λ b → b)
