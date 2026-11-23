------------------------------------------------------------------------
-- Chapter 6's universal filler uni as operation heads, beside lim and
-- the universal cone (spec §1.6, §6.2; ledger S27 (e)).
--
-- Spec §1.6: uni^w_{Γ,n} and its comparison components uni^y_{Γ,n} have
-- as arity the generic horn H_n(Γ): Γ, the apex c : ⋆ and the horn
-- variables of Horn_n(Γ, id; c). A use Θ ⊢ uni^w[σ] with
-- σ : Horn_n(Γ, γ; c) is h[(γ, c, σ)].
--
-- The horn is a parameter, like the cone shape of CaTTExp.Binder.LimHeads:
-- `ushape Γ n` returns one pure context U (a `UShape`) laid out as
--
--   Cone(Γ; L)  |  the h horn entries  |  w  |  the components y …
--
-- in which the limit L and the cone cells λ are *variables* (the
-- cone context of §5.4 over Γ), the horn entries are Horn_n's (c, ∂w,
-- the Tr_n variables not over the boundary, whose boundary variables
-- are already F(∂w)), w is J1's cell and the components are J2's, the
-- new variables of Tr_{n+1}. This is exactly how CaTTExp.Lim.Horn builds
-- J2₀ and J2₁. The heads then read U against the universal cone:
--
--   arity of uni_{Γ,n}:  Γ, then the horn entries,
--   uni^w (selector 0):  the type of w,
--   uni^y (selector j+1): the type of component j,
--
-- each with L := lim_Γ[id], λ_g := λ_{Γ,g}[id], w := uni^w[id] and the
-- earlier components := uni^y[id] substituted (`ρ`). Horn entries
-- listed in `marked` are marked inv in the arity, so the kernel's mark
-- premise asks σ for their inv derivations (§6.2, "σ must supply inv
-- derivations"). J2's conclusion that every uni^y[σ] is itself inv is a
-- rule of the mark judgment, not of typing, and is not stated here.
--
-- Validity is decided: Γ and U are well-formed pure contexts, U starts
-- with the cone shape over Γ, and the selector is in range. The family
-- is a HeadSpec, so it has BinderLaws (substitution, weakening, the
-- certified checker and its completeness) and rule (op), with nothing
-- proved about horns. The horn shapes that exist in Agda (the arrow,
-- n ≤ 1) are the instance in CaTTExp.Binder.UniHeadsExamples.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
import CaTTExp.Binder.Syntax as Syn
open import CaTTExp.Binder.HeadSpec using (HeadSpec)
open import CaTTExp.Binder.LimHeads

module CaTTExp.Binder.UniHeads where

record UShape : Set where
  constructor ush
  field
    ctx    : P.Ctx       -- Cone(Γ; L), horn entries, w, components
    horn   : Nat         -- the number of horn entries
    marked : List Nat    -- levels in ctx of the marked horn entries

data LUF : Set where
  base : LimF → LUF
  uniF : P.Ctx → Nat → LUF

_==U_ : LUF → LUF → Bool
base a   ==U base b   = a ==L b
uniF Γ n ==U uniF Δ m = (Γ P.==Ctx Δ) ∧ (n ==ℕ m)
_        ==U _        = false

==U-sound : ∀ a b → T (a ==U b) → a ≡ b
==U-sound (base a)   (base b)   p = cong base (==L-sound a b p)
==U-sound (uniF Γ n) (uniF Δ m) p =
  cong₂ uniF (P.==Ctx-sound Γ Δ (∧-fst p)) (==ℕ-sound n m (∧-snd {Γ P.==Ctx Δ} p))

module UniConstruction (K B : Set) (inj : LUF → B)
  (shape : P.Ctx → Maybe P.Ctx) (ushape : P.Ctx → Nat → Maybe UShape) where

  open Syn K B
  open PureEmb K B
  module LC = LimConstruction K B (λ l → inj (base l)) shape
  open LC using (limId; legId; dropR; shapeOK)

  -- The substitution of length k whose entry i is f i.
  tab : Nat → (Nat → Tm) → Sub
  tab zero    f = ⟨⟩
  tab (suc k) f = tab k f ,ₛ f k

  -- Γ has nΓ entries, the cone context p, the horn h.
  module At (Γ : P.Ctx) (n p h : Nat) where
    nΓ : Nat
    nΓ = P.len Γ

    uniId : Nat → Tm
    uniId y = bnd (inj (uniF Γ n)) y ε (fresh 0 (nΓ + h))

    -- Entry i of U, read against the universal cone and the filler.
    ρi : Nat → Tm
    ρi i with i <ℕ nΓ
    ... | true  = var i
    ... | false with i ==ℕ nΓ
    ...   | true  = limId Γ
    ...   | false with i <ℕ p
    ...     | true  = legId Γ (i ∸ suc nΓ)
    ...     | false with i <ℕ (p + h)
    ...       | true  = var (nΓ + (i ∸ p))
    ...       | false = uniId (i ∸ (p + h))

    ρ : Nat → Sub
    ρ k = tab k ρi

  -- The shape data at (Γ, n), when both shapes are given.
  data Data : Set where
    dat : (Kc U : P.Ctx) (h : Nat) (ms : List Nat) → Data

  getData : P.Ctx → Nat → Maybe Data
  getData Γ n with shape Γ | ushape Γ n
  ... | just Kc | just (ush U h ms) = just (dat Kc U h ms)
  ... | _       | _                 = nothing

  -- The arity: Γ, then the h horn entries starting at level p of U.
  hornCtx : P.Ctx → Nat → (U : P.Ctx) → Nat → List Nat → Nat → Nat → Ctx
  hornCtx Γ n U h ms p zero    = peCtx Γ
  hornCtx Γ n U h ms p (suc k) =
    hornCtx Γ n U h ms p k ▸[ if elem (p + k) ms then minv ∷ [] else [] ] entry
    where
    open At Γ n p h
    entry : Ty
    entry with P.lookup U (p + k)
    ... | just A  = peTy A [ ρ (P.len U) ]ty
    ... | nothing = ⋆

  uctx : P.Ctx → Nat → Ctx
  uctx Γ n with getData Γ n
  ... | just (dat Kc U h ms) = hornCtx Γ n U h ms (P.len Kc) h
  ... | nothing              = ε

  uty : P.Ctx → Nat → Nat → Ty
  uty Γ n y with getData Γ n
  ... | nothing = ⋆
  ... | just (dat Kc U h ms) with P.lookup U (P.len Kc + h + y)
  ...   | just A  = peTy A [ At.ρ Γ n (P.len Kc) h (P.len U) ]ty
  ...   | nothing = ⋆

  uok : P.Ctx → Nat → Nat → Bool
  uok Γ n y with getData Γ n
  ... | nothing = false
  ... | just (dat Kc U h ms) =
    shapeOK Γ Kc ∧ is-just (P.checkCtx U) ∧
    (P.len Kc <ℕ suc (P.len U)) ∧
    (dropR (P.len U ∸ P.len Kc) U P.==Ctx Kc) ∧
    ((P.len Kc + h + y) <ℕ P.len U)

  hctx : LUF → Nat → Ctx
  hctx (base l)   y = LC.hctx l y
  hctx (uniF Γ n) y = uctx Γ n

  hty : LUF → Nat → Ty
  hty (base l)   y = LC.hty l y
  hty (uniF Γ n) y = uty Γ n y

  hok : LUF → Nat → Bool
  hok (base l)   y = LC.hok l y
  hok (uniF Γ n) y = uok Γ n y

uniSpec : (K : Set) (shape : P.Ctx → Maybe P.Ctx) (ushape : P.Ctx → Nat → Maybe UShape) → HeadSpec K
uniSpec K shape ushape = record
  { H         = LUF
  ; _==H_     = _==U_
  ; ==H-sound = ==U-sound
  ; hctx      = hctx
  ; hty       = hty
  ; hok       = hok
  }
  where open UniConstruction K LUF (λ b → b) shape ushape
