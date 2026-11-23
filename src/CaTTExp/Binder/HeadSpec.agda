------------------------------------------------------------------------
-- A family of operation heads given as in spec §1.6 (ledger S27 (b)):
-- for each head h and selector y an arity context Γ_{h,y}, a type A_{h,y}
-- over it, and a decidable validity test. `specBinders` turns it into a
-- binder interface (empty telescopes; argument telescope and result type
-- the closures of Γ and A), and `Laws` proves, for every such family:
--
--  * spec-honest: every valid head is honest (CaTTExp.Binder.HonestHeads),
--    so its binder rule is spec §1.1's rule (op);
--  * spec-laws: BinderLaws, so substitution (Binder.Subst), weakening,
--    the certified checker and its completeness hold.
--
-- The side condition adds to the family's own test three syntactic
-- checks that make the data honest: Γ is scoped entry by entry, and A
-- is scoped over Γ and locally closed. They are decided, not assumed.
--
-- The data may mention the family's own heads (λ_{Γ,g}'s type mentions
-- lim_Γ): hctx and hty land in the syntax over H itself. To put several
-- families in one signature, define each over an injection into a
-- common former set (as CaTTExp.Binder.Des does) and take the union.
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Syntax as Syn
import CaTTExp.Binder.Close as Cl
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)

module CaTTExp.Binder.HeadSpec where

record HeadSpec (K : Set) : Set₁ where
  field
    H         : Set
    _==H_     : H → H → Bool
    ==H-sound : ∀ h k → T (h ==H k) → h ≡ k
    hctx      : H → Nat → Syn.Ctx K H
    hty       : H → Nat → Syn.Ty K H
    hok       : H → Nat → Bool

module _ {K : Set} (sp : HeadSpec K) where

  open HeadSpec sp
  open Syn K H
  open Cl K H

  isεC : Ctx → Bool
  isεC ε = true
  isεC _ = false

  specSide : H → Nat → Ctx → Bool
  specSide h y Δ =
    isεC Δ ∧ hok h y ∧ honest? (hctx h y) ∧ scTy? (len (hctx h y)) (hty h y) ∧ lcTy? 0 (hty h y)

  specBinders : Binders K
  specBinders = record
    { B         = H
    ; _==B_     = _==H_
    ; ==B-sound = ==H-sound
    ; bside     = specSide
    ; bargs     = λ h y _ → clTel 0 (hctx h y)
    ; bres      = λ h y _ → clTy 0 (hty h y)
    }

module Laws (𝕊₀ : Old.Signature) (sp : HeadSpec (Old.Signature.K 𝕊₀)) where

  𝕊 : Signature
  𝕊 = extend 𝕊₀ (specBinders sp)

  open Signature 𝕊
  open HeadSpec sp using (hctx; hty; hok)
  open import CaTTExp.Binder.SyntaxLemmas K B using (T∧)
  open import CaTTExp.Binder.HonestHeads 𝕊
  open import CaTTExp.Binder.Heads 𝕊
  import CaTTExp.Binder.Laws as L
  open L 𝕊 using (BinderLaws)

  private
    isε-≡ : ∀ Δ → T (isεC sp Δ) → Δ ≡ ε
    isε-≡ ε _ = refl

    parts : ∀ h y Δ → T (bside h y Δ) →
            (Δ ≡ ε) × Honest (hctx h y) × T (scTy? (len (hctx h y)) (hty h y)) × T (lcTy? 0 (hty h y))
    parts h y Δ p =
      let (a , q₁) = T∧ {isεC sp Δ} p
          (_ , q₂) = T∧ {hok h y} q₁
          (c , q₃) = T∧ {honest? (hctx h y)} q₂
          (d , e)  = T∧ {scTy? (len (hctx h y)) (hty h y)} q₃
      in isε-≡ Δ a , honest?-sound (hctx h y) c , d , e

  spec-honest : ∀ h y → T (bside h y ε) → HonestAt h y (hctx h y) (hty h y)
  spec-honest h y p = record
    { honest  = fst (snd (parts h y ε p))
    ; ty-sc   = fst (snd (snd (parts h y ε p)))
    ; ty-lc   = snd (snd (snd (parts h y ε p)))
    ; side-ε  = λ Δ q → fst (parts h y Δ q)
    ; args-eq = refl
    ; res-eq  = refl
    }

  spec-head : ∀ h → HeadAt h
  spec-head h = honest-head (λ y p → hctx h y , hty h y , spec-honest h y p)
                            (λ y Δ q → fst (parts h y Δ q))

  spec-laws : BinderLaws
  spec-laws = head-laws spec-head
