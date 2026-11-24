------------------------------------------------------------------------
-- The generic diagram η_Γ (spec §7.2, rule (GEN); ledger S26k step 2)
-- as heads beside the free object ⟦Γ⟧ (CaTTExp.Binder.FreeObj) and
-- the point object ⊤, a head with lim_ε's rule (spec §6.6; it has no
-- terminality or uni here):
--
--   Γ ⊢
--   ─────────────────────── (GEN)
--   Θ ⊢ η_Γ : Γ ⇒ ⟦Γ⟧
--
-- A diagram Γ ⇒ C is read through elements (spec §6.6): an object
-- entry of Γ goes to an element ⊤ → C, an arrow entry to a 2-cell
-- between elements, and so on, one dimension up. So η_Γ is one head per
-- entry j of Γ, η_{Γ,j}, with no arguments, whose type is the
-- suspension of entry j's type with the suspension's two new objects
-- sent to ⊤ and ⟦Γ⟧ and the earlier entries to the earlier generators:
--
--   η_{Γ,j} : (ΣA_j)[⊤, ⟦Γ⟧, η_{Γ,0}, …, η_{Γ,j−1}]
--
-- the same pattern as the universal cone's legs (CaTTExp.Binder.
-- LimHeads, λ_{Γ,g} at the cone context). The suspension is pure
-- CaTT's (CaTTExp.Suspension), so the coherences in Γ's types become
-- coherences in the hom 𝒦(⊤, ⟦Γ⟧).
--
-- Γ is a pure context (unmarked), carried by the head as lim carries
-- its base. ⟦Γ⟧ in the type is FreeObj's head itself, on the telescope
-- Γ (closed into bound variables): there is one free-object former.
-- ⊤ is a head with lim_ε's rule (arity ε, type ⋆; as
-- `MultimapCells.unit`).
--
-- Side condition of η_{Γ,j}: Γ ⊢ (decided by pure CaTT's checker), j
-- an entry of Γ, no telescope, and the type closed and locally closed
-- (decided, as HeadSpec does).
--
-- Not here: LIFT (S26k step 3).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Pure as P
import CaTTExp.Binder.Syntax as Syntax
import CaTTExp.Binder.Close as Close
open import CaTTExp.Binder.Embed using (Binders)
open import CaTTExp.Binder.FreeObj using (FreeF; free; _==Fr_; ==Fr-sound; module FreeConstruction)
open import CaTTExp.Binder.LimHeads using (module PureEmb)
open import CaTTExp.Suspension P.∅ using (Σty)

module CaTTExp.Binder.GenHeads where

data GenF : Set where
  frF  : FreeF → GenF
  unit : GenF
  gen  : P.Ctx → GenF

_==Gn_ : GenF → GenF → Bool
frF a ==Gn frF b = a ==Fr b
unit  ==Gn unit  = true
gen Γ ==Gn gen Δ = Γ P.==Ctx Δ
_     ==Gn _     = false

==Gn-sound : ∀ a b → T (a ==Gn b) → a ≡ b
==Gn-sound (frF a) (frF b) p = cong frF (==Fr-sound a b p)
==Gn-sound unit    unit    _ = refl
==Gn-sound (gen Γ) (gen Δ) p = cong gen (P.==Ctx-sound Γ Δ p)
==Gn-sound (frF _) unit    ()
==Gn-sound (frF _) (gen _) ()
==Gn-sound unit    (frF _) ()
==Gn-sound unit    (gen _) ()
==Gn-sound (gen _) (frF _) ()
==Gn-sound (gen _) unit    ()

-- The construction, over any former set into which GenF injects.
module GenConstruction (K B : Set) (inj : GenF → B) where

  open Syntax K B
  open Close K B using (clTel)
  open PureEmb K B
  open FreeConstruction K B (λ f → inj (frF f)) public

  isεC : Ctx → Bool
  isεC ε = true
  isεC _ = false

  -- ⊤, with lim_ε's rule.
  topT : Tm
  topT = bnd (inj unit) 0 ε ⟨⟩

  -- ⟦Γ⟧ on a pure context: FreeObj's head on Γ closed into a telescope.
  freeP : P.Ctx → Tm
  freeP Γ = ⟦ clTel 0 (peCtx Γ) ⟧

  -- η_{Γ,j}.
  genId : P.Ctx → Nat → Tm
  genId Γ j = bnd (inj (gen Γ)) j ε ⟨⟩

  -- The substitution from ΣΓ's first 2 + j entries: N ↦ ⊤, S ↦ ⟦Γ⟧,
  -- entry i < j ↦ η_{Γ,i}.
  genSub : P.Ctx → Nat → Sub
  genSub Γ zero    = ⟨⟩ ,ₛ topT ,ₛ freeP Γ
  genSub Γ (suc j) = genSub Γ j ,ₛ genId Γ j

  -- The type of η_{Γ,j}.
  genTy : P.Ctx → Nat → Ty
  genTy Γ j with P.lookup Γ j
  ... | just A  = peTy (Σty A) [ genSub Γ j ]ty
  ... | nothing = ⋆

  sideG : GenF → Nat → Ctx → Bool
  sideG (frF f) y Δ = sideF f y Δ
  sideG unit    y Δ = isεC Δ ∧ (y ==ℕ 0)
  sideG (gen Γ) j Δ =
    isεC Δ ∧ is-just (P.checkCtx Γ) ∧ is-just (P.lookup Γ j) ∧ scTy? 0 (genTy Γ j) ∧ lcTy? 0 (genTy Γ j)

  argsG : GenF → Nat → Ctx → Ctx
  argsG _ _ _ = ε

  resG : GenF → Nat → Ctx → Ty
  resG (gen Γ) j _ = genTy Γ j
  resG _       _ _ = ⋆

genBinders : (K : Set) → Binders K
genBinders K = record
  { B = GenF ; _==B_ = _==Gn_ ; ==B-sound = ==Gn-sound
  ; bside = sideG ; bargs = argsG ; bres = resG }
  where open GenConstruction K GenF (λ b → b)
