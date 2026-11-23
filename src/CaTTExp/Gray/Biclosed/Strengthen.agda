------------------------------------------------------------------------
-- The biclosed checker reads a context only at the variables a term
-- uses (ledger S26j, step 2b): if two contexts agree at every variable
-- of t, infer gives the same answer in both.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Strengthen where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing
open import CaTTExp.Binder.MultimapCells using (varsT; varsTs)

------------------------------------------------------------------------
-- Agreement of two contexts on a list of variables.

Agree : Ctx → Ctx → List Nat → Set
Agree Φ Ψ xs = ∀ i → T (elem i xs) → lookup Φ i ≡ lookup Ψ i

∨-l : ∀ a b → T a → T (a ∨ b)
∨-l true  b _ = tt

∨-r : ∀ a b → T b → T (a ∨ b)
∨-r true  b _ = tt
∨-r false b p = p

elem-++l : ∀ i xs ys → T (elem i xs) → T (elem i (xs ++ ys))
elem-++l i (x ∷ xs) ys p with i ==ℕ x
... | true  = tt
... | false = elem-++l i xs ys p

elem-++r : ∀ i xs ys → T (elem i ys) → T (elem i (xs ++ ys))
elem-++r i []       ys p = p
elem-++r i (x ∷ xs) ys p = ∨-r (i ==ℕ x) _ (elem-++r i xs ys p)

agree-l : ∀ Φ Ψ xs ys → Agree Φ Ψ (xs ++ ys) → Agree Φ Ψ xs
agree-l Φ Ψ xs ys a i p = a i (elem-++l i xs ys p)

agree-r : ∀ Φ Ψ xs ys → Agree Φ Ψ (xs ++ ys) → Agree Φ Ψ ys
agree-r Φ Ψ xs ys a i p = a i (elem-++r i xs ys p)

------------------------------------------------------------------------
-- infer on comp, glue and cons, as plain functions of the recursive
-- results.

combC : Tm → List Tm → Maybe CTy → Maybe (List CTy) → Maybe CTy
combC f gs (just tf) (just tgs) = compTy f gs tf tgs
combC f gs _         _          = nothing

combG : Tm → Tm → Maybe CTy → Maybe CTy → Maybe CTy → Maybe CTy
combG am ap (just ta) (just tb) (just tx) = glueTop am ap ta tb tx
combG am ap _         _         _         = nothing

combL : Maybe CTy → Maybe (List CTy) → Maybe (List CTy)
combL (just A) (just As) = just (A ∷ As)
combL _        _         = nothing

comp-eq : ∀ Γ f gs → infer Γ (comp f gs) ≡ combC f gs (infer Γ f) (inferL Γ gs)
comp-eq Γ f gs with infer Γ f | inferL Γ gs
... | just _  | just _  = refl
... | just _  | nothing = refl
... | nothing | _       = refl

glue-eq : ∀ Γ am x ap → infer Γ (glue am x ap) ≡ combG am ap (infer Γ am) (infer Γ ap) (infer Γ x)
glue-eq Γ am x ap with infer Γ am | infer Γ ap | infer Γ x
... | just _  | just _  | just _  = refl
... | just _  | just _  | nothing = refl
... | just _  | nothing | _       = refl
... | nothing | _       | _       = refl

cons-eq : ∀ Γ t ts → inferL Γ (t ∷ ts) ≡ combL (infer Γ t) (inferL Γ ts)
cons-eq Γ t ts with infer Γ t | inferL Γ ts
... | just _  | just _  = refl
... | just _  | nothing = refl
... | nothing | _       = refl

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- The lemma.

mutual
  infer-agree : ∀ Φ Ψ t → Agree Φ Ψ (varsT t) → infer Φ t ≡ infer Ψ t
  infer-agree Φ Ψ (var i) a = a i (∨-l (i ==ℕ i) false (==ℕ-refl i))
  infer-agree Φ Ψ (mP U V) a = refl
  infer-agree Φ Ψ (eL A C) a = refl
  infer-agree Φ Ψ (eR A C) a = refl
  infer-agree Φ Ψ (pP Δ Θ) a = refl
  infer-agree Φ Ψ pt a = refl
  infer-agree Φ Ψ (iP Θ) a = refl
  infer-agree Φ Ψ (idt A) a = refl
  infer-agree Φ Ψ (comp f gs) a =
    trans (comp-eq Φ f gs)
      (trans (cong₂ (combC f gs) (infer-agree Φ Ψ f (agree-l Φ Ψ (varsT f) (varsTs gs) a))
                                 (inferL-agree Φ Ψ gs (agree-r Φ Ψ (varsT f) (varsTs gs) a)))
             (sym (comp-eq Ψ f gs)))
  infer-agree Φ Ψ (glue am x ap) a =
    let a₁  = agree-l Φ Ψ (varsT am) (varsT x ++ varsT ap) a
        a₂₃ = agree-r Φ Ψ (varsT am) (varsT x ++ varsT ap) a
        a₂  = agree-l Φ Ψ (varsT x) (varsT ap) a₂₃
        a₃  = agree-r Φ Ψ (varsT x) (varsT ap) a₂₃
    in trans (glue-eq Φ am x ap)
         (trans (cong₃ (combG am ap) (infer-agree Φ Ψ am a₁) (infer-agree Φ Ψ ap a₃) (infer-agree Φ Ψ x a₂))
                (sym (glue-eq Ψ am x ap)))
  infer-agree Φ Ψ (here t e φs ts) a =
    cong (λ b → if okT t ∧ (length φs ==ℕ nObj t) ∧ (length ts ==ℕ nCtx t) ∧ b
                then just (sY (instS φs ts) (goal t e)) else nothing)
         (argsOk-agree Φ Ψ (instS φs ts) ts (ctx t) a)

  inferL-agree : ∀ Φ Ψ ts → Agree Φ Ψ (varsTs ts) → inferL Φ ts ≡ inferL Ψ ts
  inferL-agree Φ Ψ []       a = refl
  inferL-agree Φ Ψ (t ∷ ts) a =
    trans (cons-eq Φ t ts)
      (trans (cong₂ combL (infer-agree Φ Ψ t (agree-l Φ Ψ (varsT t) (varsTs ts) a))
                          (inferL-agree Φ Ψ ts (agree-r Φ Ψ (varsT t) (varsTs ts) a)))
             (sym (cons-eq Ψ t ts)))

  argsOk-agree : ∀ Φ Ψ σ ts As → Agree Φ Ψ (varsTs ts) → argsOk Φ σ ts As ≡ argsOk Ψ σ ts As
  argsOk-agree Φ Ψ σ []       []       a = refl
  argsOk-agree Φ Ψ σ []       (_ ∷ _)  a = refl
  argsOk-agree Φ Ψ σ (_ ∷ _)  []       a = refl
  argsOk-agree Φ Ψ σ (x ∷ xs) (A ∷ As) a =
    cong₂ (λ m b → eqMaybeTy m (sY σ A) ∧ b)
      (infer-agree Φ Ψ x (agree-l Φ Ψ (varsT x) (varsTs xs) a))
      (argsOk-agree Φ Ψ σ xs As (agree-r Φ Ψ (varsT x) (varsTs xs) a))
