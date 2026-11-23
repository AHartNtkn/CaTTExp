------------------------------------------------------------------------
-- When a head family given as in spec §1.6 (CaTTExp.Binder.HeadSpec)
-- suspends (ledger S27 (c), (d)).
--
-- Spec §1.5: a head h[σ] suspends to (Σh)[Σσ] when the signature
-- provides a head Σh with arity Σ(Γ_h) and type Σ(A_h). For a family
-- given by arity contexts and types, that is the data of `SpecSusp`:
-- at every head h, selector y where canΣ holds and the family's own
-- test passes,
--
--   * the arity of sH h y (selector sY h y) is Σ of the arity of h,
--   * its type is Σ of the type of h,
--   * the family's own test passes at sH h y, and
--   * the arity and type of h are suspendable syntax.
--
-- `spec-susp` turns it into the hypotheses `HeadSusp` of
-- CaTTExp.Binder.Suspension, so the whole kernel with that family
-- suspends. The honesty side conditions at sH h y are not assumed:
-- suspension preserves scoping and local closure (`honestΣ`, `scΣty`,
-- `lcΣty`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
import CaTTExp.Binder.Mark as BM
open import CaTTExp.Binder.HeadSpec

module CaTTExp.Binder.SpecSusp
  (𝕊₀ : Old.Signature) (sp : HeadSpec (Old.Signature.K 𝕊₀))
  where

open Laws 𝕊₀ sp using (𝕊; spec-honest)
open HeadSpec sp using (H; hctx; hty; hok)
open import CaTTExp.Binder.Signature
open Signature 𝕊
open import CaTTExp.Binder.SyntaxLemmas (Old.Signature.K 𝕊₀) H using (T∧; ∧T)
open import CaTTExp.Binder.HonestHeads 𝕊 using (HonestAt; honest?)

module _
  (mark : Ctx → BM.Mark → Tm → Bool)
  (canΣ : H → Nat → Bool) (sH : H → Nat → H) (sY : H → Nat → Nat)
  where

  open import CaTTExp.Binder.Suspension 𝕊 mark canΣ sH sY

  record SpecSusp : Set where
    field
      ctx-eq  : ∀ h y → T (canΣ h y) → T (hok h y) → hctx (sH h y) (sY h y) ≡ Σctx (hctx h y)
      ty-eq   : ∀ h y → T (canΣ h y) → T (hok h y) → hty (sH h y) (sY h y) ≡ Σty (hty h y)
      hok-Σ   : ∀ h y → T (canΣ h y) → T (hok h y) → T (hok (sH h y) (sY h y))
      sok-ctx : ∀ h y → T (canΣ h y) → T (hok h y) → T (sokCtx (hctx h y))
      sok-ty  : ∀ h y → T (canΣ h y) → T (hok h y) → T (sokTy (hty h y))

  spec-susp : SpecSusp → HeadSusp
  spec-susp ss = record { arity = ar }
    where
    open SpecSusp ss

    ar : ∀ h y → T (canΣ h y) → T (bside h y ε) →
         Σ Ctx λ G → Σ _ λ A →
           HonestAt h y G A × HonestAt (sH h y) (sY h y) (Σctx G) (Σty A)
           × T (bside (sH h y) (sY h y) ε) × T (sokCtx G) × T (sokTy A)
    ar h y c p = hctx h y , hty h y , spec-honest h y p , ha′ , p′
               , sok-ctx h y c ok , sok-ty h y c ok
      where
      G = hctx h y
      A = hty h y
      q₁ = snd (T∧ {true} p)
      ok = fst (T∧ {hok h y} q₁)
      q₂ = snd (T∧ {hok h y} q₁)
      hG = fst (T∧ {honest? G} q₂)
      q₃ = snd (T∧ {honest? G} q₂)
      sA = fst (T∧ {scTy? (len G) A} q₃)
      lA = snd (T∧ {scTy? (len G) A} q₃)

      side′ : T (isεC sp ε ∧ hok (sH h y) (sY h y) ∧ honest? (Σctx G)
                 ∧ scTy? (len (Σctx G)) (Σty A) ∧ lcTy? 0 (Σty A))
      side′ = ∧T {true} tt (∧T (hok-Σ h y c ok) (∧T (honestΣ G hG)
                (∧T (subst (λ n → T (scTy? n (Σty A))) (sym (lenΣ G)) (scΣty (len G) A sA))
                    (lcΣty 0 A lA))))

      p′ : T (bside (sH h y) (sY h y) ε)
      p′ rewrite ctx-eq h y c ok | ty-eq h y c ok = side′

      ha′ : HonestAt (sH h y) (sY h y) (Σctx G) (Σty A)
      ha′ = subst (λ X → HonestAt (sH h y) (sY h y) X (Σty A)) (ctx-eq h y c ok)
              (subst (HonestAt (sH h y) (sY h y) (hctx (sH h y) (sY h y))) (ty-eq h y c ok)
                     (spec-honest (sH h y) (sY h y) p′))
