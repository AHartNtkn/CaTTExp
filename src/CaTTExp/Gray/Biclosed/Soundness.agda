------------------------------------------------------------------------
-- Theorem S, generic part (notes/free-objects-proofs.md §5.4–5.5):
-- every model of the biclosed kernel (Model.agda) interprets every
-- derivable term of Gray/Biclosed soundly.
--
--   soundness 𝔐 ε Γ hyp t A : if the values ε of the context
--   variables satisfy Γ, and the checker types t at A in Γ, then the
--   interpretation ⟦t⟧ is an element of ⟦A⟧ (Sem.agda's Mem).
--
-- The reading of mode inv is "flat": an inv-cell has equivalent source
-- and target.  This is the reading the strict model 𝔖 satisfies when
-- collars are identities; the strictly-invertible reading is a
-- refinement (open-issues C5b).  No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Soundness where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Gray.Biclosed.Model

module _ (𝔐 : Model) where
  open Model 𝔐
  open import CaTTExp.Gray.Biclosed.Sem 𝔐
  open import CaTTExp.Gray.Biclosed.SemComp 𝔐
  open import CaTTExp.Gray.Biclosed.SemHere 𝔐

  eqMaybe-sound : ∀ m B → T (eqMaybeTy m B) → m ≡ just B
  eqMaybe-sound (just A) B p = cong just (eqTy-sound A B p)

  module Sound (ε : Nat → SC) (Γ : Ctx)
               (hyp : ∀ i {A} → lookup Γ i ≡ just A → Interp.Mem ε A (ε i)) where
    open Interp ε

    nj : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nj ()

    mutual
      sound : ∀ t {A} → infer Γ t ≡ just A → Mem A ⟦ t ⟧
      sound (var i)   p    = hyp i p
      sound (mP U V)  refl = T-cor (cm U V) , refl , refl
      sound (eL A C)  refl = T-evL A C , refl , refl
      sound (eR A C)  refl = T-evR A C , refl , refl
      sound (pP Δ Θ)  refl = T-cor (cp Δ Θ) , refl , refl
      sound pt        refl = T-cor cpt , refl , refl
      sound (idt A)   refl = T-id A , refl , refl
      sound (comp f gs) p with infer Γ f in ef | inferL Γ gs in egs
      ... | just tf | just tgs = compSound ε f gs tf tgs (sound f ef) (soundL gs egs) p
      ... | just _  | nothing  = ⊥-elim (nj p)
      ... | nothing | _        = ⊥-elim (nj p)
      sound (glue am x ap) p with infer Γ am in e₁ | infer Γ ap in e₂ | infer Γ x in e₃
      ... | just ta | just tb | just tx =
        glueSound ε am ap x ta tb tx (sound am e₁) (sound ap e₂) (sound x e₃) p
      ... | just _  | just _  | nothing = ⊥-elim (nj p)
      ... | just _  | nothing | _       = ⊥-elim (nj p)
      ... | nothing | _       | _       = ⊥-elim (nj p)
      sound (here (tmpl ρ g md n) e φs ts) p
        with if-just (okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t)
                       ∧ argsOk Γ (instS φs ts) ts (ctx t)) p
        where t = tmpl ρ g md n
      ... | c , refl = goal-sound e
        where
        t = tmpl ρ g md n
        I : Inst ε t φs ts
        I = record
          { iok   = ∧-fst c
          ; iφ    = ==ℕ-sound _ _ (∧-fst (∧-snd {okT t} c))
          ; its   = ==ℕ-sound _ _ (∧-fst (∧-snd {length φs ==ℕ nObj t} (∧-snd {okT t} c)))
          ; iargs = soundArgs (instS φs ts) ts (ctx t)
                      (∧-snd {length ts ==ℕ nCtx t} (∧-snd {length φs ==ℕ nObj t} (∧-snd {okT t} c)))
          }
        goal-sound : ∀ e → Mem (sY (instS φs ts) (goal t e)) (hereS e t φs ⟦ ts ⟧s)
        goal-sound gc = Here.hereC ε ρ g md φs ts n I
        goal-sound gε = Here.hereE ε ρ g md φs ts n I

      soundL : ∀ ts {As} → inferL Γ ts ≡ just As → All2 Mem As ⟦ ts ⟧s
      soundL []       refl = []
      soundL (t ∷ ts) p with infer Γ t in e | inferL Γ ts in es
      ... | just A  | just As with p
      ...   | refl = sound t e ∷ soundL ts es
      soundL (t ∷ ts) p | just _  | nothing = ⊥-elim (nj p)
      soundL (t ∷ ts) p | nothing | _       = ⊥-elim (nj p)

      soundArgs : ∀ σ ts Δ → T (argsOk Γ σ ts Δ) → All2 (λ x A → Mem (sY σ A) ⟦ x ⟧) ts Δ
      soundArgs σ []       []       _ = []
      soundArgs σ (x ∷ xs) (A ∷ As) p =
        sound x (eqMaybe-sound (infer Γ x) (sY σ A) (∧-fst p)) ∷
        soundArgs σ xs As (∧-snd {eqMaybeTy (infer Γ x) (sY σ A)} p)
      soundArgs σ []       (_ ∷ _)  ()
      soundArgs σ (_ ∷ _)  []       ()

  ----------------------------------------------------------------------
  -- Theorem S (generic): soundness in every model

  soundness : ∀ (ε : Nat → SC) Γ → (∀ i {A} → lookup Γ i ≡ just A → Interp.Mem ε A (ε i)) →
              ∀ t {A} → infer Γ t ≡ just A → Interp.Mem ε A (Interp.⟦_⟧ ε t)
  soundness ε Γ hyp t p = Sound.sound ε Γ hyp t p
