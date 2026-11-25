------------------------------------------------------------------------
-- Strict-model soundness of two-tier L with the CaTT-shaped coherence
-- case (S30, notes/lax-sc-completeness.md §4; spec/02 §2.2 after PR #591).
--
-- Gray.SupportG takes the coherence-case predicate as a parameter and
-- makes the support function dispatch on it; Strict.G.Soundness proves
-- soundness in the strict model for every predicate that forces equal
-- closed supports (`CohSound`), by (B) (`Strict.Recon.b-supp`). Here:
--
--  * ccV, the Var-shaped clause: endpoints right, equal closed supports,
--    every non-object variable of Θ occurs in both closed supports.
--    `soundV`: every term derivable with this side condition over a
--    pasting context is a cell of ν(K(Γ)), the free strict Gray-enriched
--    category, with coherence-case cohs interpreted as identities and
--    operation-case cohs as the total cell.
--  * ccF, the full-Gray-support clause in closure form, as a control:
--    the same theorem for (closure-form) graySide.
--  * Lemma 4.2 for ccV, both halves (`var-used`, `used-var`): over a
--    pasting context, v is an entry of a tuple of ↓supp(t : A) iff v is
--    a non-object variable of t : A (Strict.G.SuppFV, Gray.G.SuppVars).
--  * evaluation checks on the gap example βα → βα₂ of Gray.CohCaseGap:
--    SV.sideG (SupportG's sideG at ccV) accepts it, the support function now gives it the identity
--    image (empty top chain), the certified checker produces a
--    derivation, and `soundV` turns that derivation into a cell.
--
-- The operation case of SupportG uses closure comparisons
-- (sameDownClosure); graySide uses the generator form (sameDown). They
-- agree on every comparison made in a pasting context (Gray.Graded,
-- Gray.DownAgree), but that agreement is not re-proved for SupportG's
-- support function, so SV.sideG is stated here in closure form.
------------------------------------------------------------------------
module CaTTExp.Gray.CohCaseVarSound where

open import CaTTExp.Prelude
open import CaTTExp.Signature
open import CaTTExp.Pure using (∅; ⟪_⟫)
open Signature ∅
open import CaTTExp.Gray.Support ∅ using (TSet; endsOK; sameDownClosure; ≈T; down; fullT; homs; objs; upto; any)
open import CaTTExp.Strict.Hyp using (≈T-via)
open import CaTTExp.Gray.Examples using (HComp; Txz; fg; f'g'; βα; αβ)
open import CaTTExp.Gray.CohCaseGap using (βα₂)

------------------------------------------------------------------------
-- The two coherence-case predicates.

open import CaTTExp.Gray.VarFull ∅ public using (usesVar; isObj; varFull)

ccV : Ctx → Ty → TSet → TSet → Bool
ccV Θ A St Su = endsOK Θ A ∧ (sameDownClosure Θ St Su ∧ (varFull Θ St ∧ varFull Θ Su))

ccF : Ctx → Ty → TSet → TSet → Bool
ccF Θ A St Su = endsOK Θ A ∧ (sameDownClosure Θ St (fullT (homs Θ))
                            ∧ sameDownClosure Θ Su (fullT (homs Θ)))

------------------------------------------------------------------------
-- Both force equal closed supports.

private
  T-∧r : ∀ a {b} → T (a ∧ b) → T b
  T-∧r true p = p

import CaTTExp.Strict.G.Soundness
import CaTTExp.Strict.G.L
import CaTTExp.Gray.SupportG
import CaTTExp.TypingWith
module V  = CaTTExp.Strict.G.Soundness ccV
module F  = CaTTExp.Strict.G.Soundness ccF
module LV = CaTTExp.Strict.G.L ccV
module LF = CaTTExp.Strict.G.L ccF
module SV = CaTTExp.Gray.SupportG ∅ ccV
module SF = CaTTExp.Gray.SupportG ∅ ccF
module TV = CaTTExp.TypingWith ∅ SV.sideG
module TF = CaTTExp.TypingWith ∅ SF.sideG

hccV : V.CohSound
hccV Θ A St Su p = ∧-fst (T-∧r (endsOK Θ A) p)

hccF : F.CohSound
hccF Θ A St Su p =
  let q = T-∧r (endsOK Θ A) p in
  ≈T-via (down Θ St) (down Θ Su) (down Θ (fullT (homs Θ)))
         (∧-fst q) (∧-snd {sameDownClosure Θ St (fullT (homs Θ))} q)

-- Soundness in the strict model, Var-shaped coherence case.
soundV : ∀ {Γ t A} → LV.PsInv Γ → TV._⊢tm_∶_ Γ t A → LV.IsCellTm Γ t A
soundV = V.Soundness.sound-tm hccV

-- …and for the full-Gray-support clause (closure form).
soundF : ∀ {Γ t A} → LF.PsInv Γ → TF._⊢tm_∶_ Γ t A → LF.IsCellTm Γ t A
soundF = F.Soundness.sound-tm hccF

------------------------------------------------------------------------
-- Lemma 4.2, both halves, for the Var-shaped rule: over a pasting
-- context, v is used by ↓supp(t : A) iff v is a non-object variable of
-- t : A. (⇒: Gray.G.SuppVars; ⇐: Strict.G.SuppFV.)

import CaTTExp.Strict.G.SuppFV
import CaTTExp.Gray.G.SuppVars
import CaTTExp.Strict.G.Hyp
open import CaTTExp.Gray.SetFacts ∅ using (_∈ᴺ_; anyS⇒)
open import CaTTExp.Gray.Cover using (any-witness)
open import CaTTExp.Gray.DownAgree ∅ using (memT-complete)
open import CaTTExp.Strict.CohCase using (down-out)
module FV  = CaTTExp.Strict.G.SuppFV ccV
module SVV = CaTTExp.Gray.G.SuppVars ∅ ccV
module HV  = CaTTExp.Strict.G.Hyp ccV

hvfV : FV.VarFullHyp
hvfV Θ A St Su p = ∧-fst (T-∧r (sameDownClosure Θ St Su) (T-∧r (endsOK Θ A) p))

-- ⇐: every non-object variable of t : A is used by ↓supp(t : A).
var-used : ∀ {Γ t A} → TV._⊢ps Γ → TV._⊢tm_∶_ Γ t A → ∀ {v} → v ∈ᴺ fvTmTy t A →
           (lookup Γ v ≡ just ⋆ → ⊥) → T (usesVar v (down Γ (SV.supp t A)))
var-used P d = FV.supp-fv⇐ hccV hvfV P d

-- ⇒: every variable used by ↓supp(t : A) is a variable of t : A.
used-var : ∀ {Γ t A} → TV._⊢ps Γ → TV._⊢tm_∶_ Γ t A → ∀ {v} →
           T (usesVar v (down Γ (SV.supp t A))) → v ∈ᴺ fvTmTy t A
used-var {Γ} {t} {A} P d {v} u
  with any-witness (anyS⇒ _ (down Γ (SV.supp t A)) u)
... | τ , mτ , uτ with any-witness (anyS⇒ (λ j → v ==ℕ j) τ uτ)
...   | j , mj , e with ==ℕ-sound v j e
...     | refl with down-out P (SV.supp t A) {τ} (memT-complete τ _ mτ)
...       | s , ms , k , r = SVV.supp-vars HV.closed (HV.inv-gr (LV.psInv P)) d ms r mj

------------------------------------------------------------------------
-- Evaluation checks on the gap example.

open import CaTTExp.PastingCheck ∅ using (checkPs)
import CaTTExp.CheckWith
module CV = CaTTExp.CheckWith ∅ SV.sideG
module CF = CaTTExp.CheckWith ∅ SF.sideG

A₁ : Ty
A₁ = arr Txz fg f'g'

gapTy : Ty
gapTy = arr A₁ βα βα₂

gapV : Tm
gapV = coh HComp gapTy (idₛ HComp)

-- accepted by the Var-shaped rule, rejected by the full-support rule
_ : SV.sideG HComp A₁ βα βα₂ ≡ true
_ = refl
_ : SF.sideG HComp A₁ βα βα₂ ≡ false
_ = refl

-- its image is an identity: empty top chain
_ : SV.topS gapV ≡ []
_ = refl

-- the reverse interchanger stays rejected by both
_ : SV.sideG HComp A₁ αβ βα ≡ false
_ = refl
_ : SF.sideG HComp A₁ αβ βα ≡ false
_ = refl

-- a certified derivation of the gap coherence, and its cell
gap-wf : TV._⊢tm_∶_ HComp gapV gapTy
gap-wf = snd (from-just (CV.infer HComp gapV))

_ : fst (from-just (CV.infer HComp gapV)) ≡ gapTy
_ = refl

HComp-ps = from-just (checkPs HComp)

gap-cell : LV.IsCellTm HComp gapV gapTy
gap-cell = soundV (LV.psInv HComp-ps) gap-wf
