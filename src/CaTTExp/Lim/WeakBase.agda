------------------------------------------------------------------------
-- Bases read weakly (design decision of notes/design-decisions.md §2).
--
-- A CaTT diagram over a context Γ is a functor out of the free WEAK
-- ω-category on Γ, so a limit rule needs no homotopicality premise on
-- Γ. This module checks how the encoded cone rules behave on a base
-- that is not homotopical, the bubble  x : ⋆, σ : 1_x ⇒ 1_x  (its free
-- strict ω-category is B²ℕ, which groupoidifies to K(ℤ,2)).
--
--   * bubble-cone, bubble-cone-strict: Mikhail's cone recognition rules
--     (printed linearity test and the strict test D3b) accept the lax
--     cone over the bubble whose 2-dimensional projection is
--         p_σ : ρ⁻¹_q ⇛ ρ⁻¹_q ; (q ▷ σ),
--     with ρ⁻¹_q : q ⇒ q · 1_x the cone cell over the coherence 1_x.
--     So the recognition rules already read the base weakly.
--
--   * bubble-unspecified, mu-unspecified: the specified cone
--     construction `coneC` (Repaired.agda) is defined only for
--     generators whose boundaries are variables. It is undefined on
--     the bubble, and also on the homotopical base  x, a : x → x,
--     μ : a · a ⇒ a. The restriction in the encoded repaired rule is
--     therefore "variable boundaries", not homotopicality; extending
--     `coneC` to term boundaries is the cone-over-coherences problem
--     (N^cone, ledger B5/CONE), which the weak-base decision needs.
------------------------------------------------------------------------
module CaTTExp.Lim.WeakBase where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Conditions
open import CaTTExp.Lim.Rules
open import CaTTExp.Lim.Terms
open import CaTTExp.Lim.Repaired using (coneC)

private
  v : Nat → Tm
  v = var

  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

-- x0, σ1 : 1_x ⇒ 1_x
Γbub : NCtx
Γbub = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ arr (0 ⇒⋆ 0) (idc (v 0)) (idc (v 0))

-- Apex 2, leg q3 : c → x, projection p4 over σ.
private
  q1x ρq : Tm
  q1x = comp (v 2) (v 0) (v 3) (v 0) (idc (v 0))     -- q · 1_x
  ρq  = runitInv (v 2) (v 0) (v 3)                   -- ρ⁻¹_q : q ⇒ q · 1_x

Πbub : NCtx
Πbub = ∅ ▹ 3 ∶ (2 ⇒⋆ 0)
         ▹ 4 ∶ arr (arr (2 ⇒⋆ 0) (v 3) q1x) ρq
                   (vcomp (v 2) (v 0) (v 3) q1x ρq q1x
                          (whL (v 2) (v 0) (v 3) (v 0) (idc (v 0)) (idc (v 0)) (v 1)))

bubble-wf : WfCtx (coneCtx Γbub 2 Πbub)
bubble-wf = from-just (wf? _)

bubble-cone : Cone Γbub 2 Πbub
bubble-cone = from-just (cone? Γbub 2 Πbub)

module S = ConeBy strictLin

bubble-cone-strict : S.Cone Γbub 2 Πbub
bubble-cone-strict = from-just (S.cone? Γbub 2 Πbub)

bubble-unspecified : coneC Γbub 2 ≡ nothing
bubble-unspecified = refl

-- x0, a1 : x → x, μ2 : a · a ⇒ a  (homotopical: a positive 2-polygraph).
Γmu : NCtx
Γmu = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)
        ▹ 2 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 0) (v 1) (v 0) (v 1)) (v 1)

mu-unspecified : coneC Γmu 3 ≡ nothing
mu-unspecified = refl
