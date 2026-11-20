------------------------------------------------------------------------
-- D7e follow-up: the sort discipline of F.7.4 §2 under substitution.
--
-- The kernel's instances are the AdmI instances (Instances.agda) whose
-- substitution sends the template's output object variables to
-- non-representable formulas.  AdmI itself does not impose this, so it
-- is a superset of the kernel's instances; inst-typed and inst-dir
-- hold on it, hence on the disciplined subset.
--
-- Results (no postulates):
--   * sF-nonRep : substituting into a non-representable formula gives
--                 a non-representable one, provided its head variable
--                 (if it is a variable) goes to a non-representable;
--   * disc-⨾    : a composite σ ⨾ τ is disciplined on S when σ is
--                 disciplined on S and τ is disciplined on the head
--                 variables of σ on S.
-- Which variables of a context Γ are output variables (the context-
-- variable clause of the discipline), and so which τ discharge the
-- second hypothesis, is stated in F.7.4 §2 and not formalized.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.SortDisc where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Templates using (_∈_)
open import CaTTExp.Gray.Biclosed.Subst
open import CaTTExp.Gray.Biclosed.Instances using (_⨾_)

nonRep : Fm → Bool
nonRep (rep _) = false
nonRep _       = true

-- the head variable of a formula, when it is a bare variable
headVar : Fm → Maybe Nat
headVar (obj i) = just i
headVar _       = nothing

sF-nonRep : ∀ φ a → T (nonRep a) →
            (∀ j → headVar a ≡ just j → T (nonRep (φ j))) →
            T (nonRep (sF φ a))
sF-nonRep φ (obj i)  _ h = h i refl
sF-nonRep φ (rep _)  () h
sF-nonRep φ (a ⊗ b)  _ h = tt
sF-nonRep φ (a \\ b) _ h = tt
sF-nonRep φ (a // b) _ h = tt

-- σ is disciplined on the object variables S
DiscOn : List Nat → Sub → Set
DiscOn S σ = ∀ i → i ∈ S → T (nonRep (fo σ i))

disc-⨾ : ∀ S σ τ → DiscOn S σ →
         (∀ i j → i ∈ S → headVar (fo σ i) ≡ just j → T (nonRep (fo τ j))) →
         DiscOn S (σ ⨾ τ)
disc-⨾ S σ τ dσ dτ i i∈S =
  sF-nonRep (fo τ) (fo σ i) (dσ i i∈S) (λ j e → dτ i j i∈S e)

-- the identity substitution is disciplined on any S
disc-id : ∀ S → DiscOn S (sub obj var)
disc-id S i _ = tt
