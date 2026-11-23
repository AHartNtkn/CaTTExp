------------------------------------------------------------------------
-- Chapter 7's free object ⟦Γ⟧ as a binder head (spec §7.2, rule
-- (FREE); ledger S26k step 1):
--
--   Γ ⊢    (Γ a closed context)
--   ───────────────────────── (FREE)
--   Θ ⊢ ⟦Γ⟧ : ⋆
--
-- ⟦Γ⟧ = bnd free 0 Γ ⟨⟩: the former binds Γ as its telescope (entries
-- refer to earlier entries by bvar 0 j), takes no arguments, and has
-- type ⋆. The side condition asks that Γ be closed (no parameter of
-- Θ); the binder rule's telescope premise, (Θ ⧺ openTel Γ) ⊢ctx, says
-- that Γ is well formed after Θ, checked by the kernel itself with its
-- own coh side condition (CaTT's or L's) and mark judgment. That this
-- is equivalent to Γ ⊢ on its own is not proved here (it needs a
-- strengthening lemma for the kernel).
--
-- Why the telescope and not an index outside the syntax (as S27's
-- chapter 6 heads index lim by a pure context): (FREE)'s premise is
-- Γ ⊢ in the theory being defined, so it should be checked by the
-- kernel's own rules, under whatever side condition it runs with.
-- Since Γ is closed, substitution fixes it (`closed-tel`), so
-- substitution fixes ⟦Γ⟧. Like INIT and lim, ⟦Γ⟧ does not suspend
-- in general (ledger S27 (g); notes/operation-heads.md §4–§5): the
-- suspension of #552 covers empty-telescope heads only, and Σ⟦Γ⟧
-- would be a free object inside a hom, which models need not have.
--
-- The generic diagram η_Γ (GEN) is CaTTExp.Binder.GenHeads (S26k step
-- 2), beside this head and ⊤ = lim_ε; the LIFT fillers (step 3) are not
-- encoded yet.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Binder.Syntax as Syntax
open import CaTTExp.Binder.Embed using (Binders)

module CaTTExp.Binder.FreeObj where

data FreeF : Set where
  free : FreeF

_==Fr_ : FreeF → FreeF → Bool
free ==Fr free = true

==Fr-sound : ∀ a b → T (a ==Fr b) → a ≡ b
==Fr-sound free free _ = refl

module FreeConstruction (K B : Set) (inj : FreeF → B) where

  open Syntax K B

  sideF : FreeF → Nat → Ctx → Bool
  sideF free y Γ = (y ==ℕ 0) ∧ scTel? 0 Γ

  argsF : FreeF → Nat → Ctx → Ctx
  argsF _ _ _ = ε

  resF : FreeF → Nat → Ctx → Ty
  resF _ _ _ = ⋆

  -- ⟦Γ⟧, for a telescope Γ.
  ⟦_⟧ : Ctx → Tm
  ⟦ Γ ⟧ = bnd (inj free) 0 Γ ⟨⟩

freeBinders : (K : Set) → Binders K
freeBinders K = record
  { B = FreeF ; _==B_ = _==Fr_ ; ==B-sound = ==Fr-sound
  ; bside = sideF ; bargs = argsF ; bres = resF }
  where open FreeConstruction K FreeF (λ b → b)
