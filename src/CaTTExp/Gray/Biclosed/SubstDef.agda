------------------------------------------------------------------------
-- Substitution on the biclosed syntax: definitions, identity and
-- composition (moved out of Subst and Instances so that the checker can
-- use it to type coherence terms).
--
-- A substitution σ assigns a formula to every object variable and a
-- term to every context variable.  A coherence term here t e φs ts
-- carries its instance as two lists; substituting into it substitutes
-- into the lists, so the term keeps its instance.  instS φs ts is the
-- substitution the lists stand for (variables beyond the lists are
-- left alone; they do not occur in a well-scoped template, Scope.agda).
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.SubstDef where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax

------------------------------------------------------------------------
-- Substitution

record Sub : Set where
  constructor sub
  field
    fo : Nat → Fm
    tm : Nat → Tm
open Sub public

sF : (Nat → Fm) → Fm → Fm
sF φ (obj i)  = φ i
sF φ (rep s)  = rep s
sF φ (shp s) = shp s
sF φ (a ⊗ b)  = sF φ a ⊗ sF φ b
sF φ (a \\ b) = sF φ a \\ sF φ b
sF φ (a // b) = sF φ a // sF φ b

sFs : (Nat → Fm) → List Fm → List Fm
sFs φ []       = []
sFs φ (a ∷ as) = sF φ a ∷ sFs φ as

sM : (Nat → Fm) → MTy → MTy
sM φ (xs ▸ z) = sFs φ xs ▸ sF φ z

mutual
  sT : Sub → Tm → Tm
  sT σ (var i)      = tm σ i
  sT σ (mP U V)     = mP (sF (fo σ) U) (sF (fo σ) V)
  sT σ (eL A C)     = eL (sF (fo σ) A) (sF (fo σ) C)
  sT σ (eR A C)     = eR (sF (fo σ) A) (sF (fo σ) C)
  sT σ (pP Δ Θ)     = pP Δ Θ
  sT σ pt           = pt
  sT σ (iP Θ)       = iP Θ
  sT σ (idt A)      = idt (sF (fo σ) A)
  sT σ (comp f gs)  = comp (sT σ f) (sTs σ gs)
  sT σ (glue a x b) = glue (sT σ a) (sT σ x) (sT σ b)
  sT σ (here t e φs ts) = here t e (sFs (fo σ) φs) (sTs σ ts)

  sTs : Sub → List Tm → List Tm
  sTs σ []       = []
  sTs σ (t ∷ ts) = sT σ t ∷ sTs σ ts

  sY : Sub → CTy → CTy
  sY σ (op M)          = op (sM (fo σ) M)
  sY σ (hom m g A s t) = hom m g (sY σ A) (sT σ s) (sT σ t)


------------------------------------------------------------------------
-- The substitution a coherence term's lists stand for

nthF : List Fm → Nat → Fm
nthF []       i       = obj i
nthF (a ∷ as) zero    = a
nthF (a ∷ as) (suc i) = nthF as i

nthT : List Tm → Nat → Tm
nthT []       i       = var i
nthT (x ∷ xs) zero    = x
nthT (x ∷ xs) (suc i) = nthT xs i

instS : List Fm → List Tm → Sub
instS φs ts = sub (nthF φs) (nthT ts)

------------------------------------------------------------------------
-- Identity and composition of substitutions

idS : Sub
idS = sub obj var

_⨾_ : Sub → Sub → Sub
σ ⨾ τ = sub (λ i → sF (fo τ) (fo σ i)) (λ i → sT τ (tm σ i))

sF-id : ∀ a → sF obj a ≡ a
sF-id (obj i)  = refl
sF-id (rep s)  = refl
sF-id (shp s) = refl
sF-id (a ⊗ b)  = cong₂ _⊗_ (sF-id a) (sF-id b)
sF-id (a \\ b) = cong₂ _\\_ (sF-id a) (sF-id b)
sF-id (a // b) = cong₂ _//_ (sF-id a) (sF-id b)

sFs-id : ∀ as → sFs obj as ≡ as
sFs-id []       = refl
sFs-id (a ∷ as) = cong₂ _∷_ (sF-id a) (sFs-id as)

sM-id : ∀ M → sM obj M ≡ M
sM-id (xs ▸ z) = cong₂ _▸_ (sFs-id xs) (sF-id z)

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

mutual
  sT-id : ∀ x → sT idS x ≡ x
  sT-id (var i)      = refl
  sT-id (mP U V)     = cong₂ mP (sF-id U) (sF-id V)
  sT-id (eL A C)     = cong₂ eL (sF-id A) (sF-id C)
  sT-id (eR A C)     = cong₂ eR (sF-id A) (sF-id C)
  sT-id (pP Δ Θ)     = refl
  sT-id pt           = refl
  sT-id (iP Θ)       = refl
  sT-id (idt A)      = cong idt (sF-id A)
  sT-id (comp f gs)  = cong₂ comp (sT-id f) (sTs-id gs)
  sT-id (glue a x b) = cong₃ glue (sT-id a) (sT-id x) (sT-id b)
  sT-id (here t e φs ts) = cong₂ (here t e) (sFs-id φs) (sTs-id ts)

  sTs-id : ∀ xs → sTs idS xs ≡ xs
  sTs-id []       = refl
  sTs-id (x ∷ xs) = cong₂ _∷_ (sT-id x) (sTs-id xs)

  sY-id : ∀ A → sY idS A ≡ A
  sY-id (op M)          = cong op (sM-id M)
  sY-id (hom m g A s t) =
    trans (cong (λ A′ → hom m g A′ (sT idS s) (sT idS t)) (sY-id A))
          (cong₂ (hom m g A) (sT-id s) (sT-id t))

module Comp (σ τ : Sub) where
  sF-⨾ : ∀ a → sF (fo τ) (sF (fo σ) a) ≡ sF (fo (σ ⨾ τ)) a
  sF-⨾ (obj i)  = refl
  sF-⨾ (rep s)  = refl
  sF-⨾ (shp s) = refl
  sF-⨾ (a ⊗ b)  = cong₂ _⊗_ (sF-⨾ a) (sF-⨾ b)
  sF-⨾ (a \\ b) = cong₂ _\\_ (sF-⨾ a) (sF-⨾ b)
  sF-⨾ (a // b) = cong₂ _//_ (sF-⨾ a) (sF-⨾ b)

  sFs-⨾ : ∀ as → sFs (fo τ) (sFs (fo σ) as) ≡ sFs (fo (σ ⨾ τ)) as
  sFs-⨾ []       = refl
  sFs-⨾ (a ∷ as) = cong₂ _∷_ (sF-⨾ a) (sFs-⨾ as)

  sM-⨾ : ∀ M → sM (fo τ) (sM (fo σ) M) ≡ sM (fo (σ ⨾ τ)) M
  sM-⨾ (xs ▸ z) = cong₂ _▸_ (sFs-⨾ xs) (sF-⨾ z)

  mutual
    sT-⨾ : ∀ x → sT τ (sT σ x) ≡ sT (σ ⨾ τ) x
    sT-⨾ (var i)      = refl
    sT-⨾ (mP U V)     = cong₂ mP (sF-⨾ U) (sF-⨾ V)
    sT-⨾ (eL A C)     = cong₂ eL (sF-⨾ A) (sF-⨾ C)
    sT-⨾ (eR A C)     = cong₂ eR (sF-⨾ A) (sF-⨾ C)
    sT-⨾ (pP Δ Θ)     = refl
    sT-⨾ pt           = refl
    sT-⨾ (iP Θ)       = refl
    sT-⨾ (idt A)      = cong idt (sF-⨾ A)
    sT-⨾ (comp f gs)  = cong₂ comp (sT-⨾ f) (sTs-⨾ gs)
    sT-⨾ (glue a x b) = cong₃ glue (sT-⨾ a) (sT-⨾ x) (sT-⨾ b)
    sT-⨾ (here t e φs ts) = cong₂ (here t e) (sFs-⨾ φs) (sTs-⨾ ts)

    sTs-⨾ : ∀ xs → sTs τ (sTs σ xs) ≡ sTs (σ ⨾ τ) xs
    sTs-⨾ []       = refl
    sTs-⨾ (x ∷ xs) = cong₂ _∷_ (sT-⨾ x) (sTs-⨾ xs)

    sY-⨾ : ∀ A → sY τ (sY σ A) ≡ sY (σ ⨾ τ) A
    sY-⨾ (op M)          = cong op (sM-⨾ M)
    sY-⨾ (hom m g A s t) =
      trans (cong (λ A′ → hom m g A′ (sT τ (sT σ s)) (sT τ (sT σ t))) (sY-⨾ A))
            (cong₂ (hom m g (sY (σ ⨾ τ) A)) (sT-⨾ s) (sT-⨾ t))

