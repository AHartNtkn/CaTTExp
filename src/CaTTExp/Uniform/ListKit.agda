------------------------------------------------------------------------
-- List lemmas used by the uniform-L checker (membership in maps,
-- concatenations and in the list of an element's own memberships).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)

module CaTTExp.Uniform.ListKit where

mapK : ∀ {A B : Set} → (A → B) → List A → List B
mapK f []       = []
mapK f (x ∷ xs) = f x ∷ mapK f xs

concatK : ∀ {A : Set} → List (List A) → List A
concatK []         = []
concatK (xs ∷ xss) = xs ++ concatK xss

∈-++ˡ : ∀ {A : Set} {z : A} {xs} ys → z ∈L xs → z ∈L (xs ++ ys)
∈-++ˡ ys here      = here
∈-++ˡ ys (there m) = there (∈-++ˡ ys m)

∈-++ʳ : ∀ {A : Set} {z : A} xs {ys} → z ∈L ys → z ∈L (xs ++ ys)
∈-++ʳ []       m = m
∈-++ʳ (x ∷ xs) m = there (∈-++ʳ xs m)

∈-++⁻ : ∀ {A : Set} {z : A} xs {ys} → z ∈L (xs ++ ys) → (z ∈L xs) ⊎ (z ∈L ys)
∈-++⁻ []       m         = inj₂ m
∈-++⁻ (x ∷ xs) here      = inj₁ here
∈-++⁻ (x ∷ xs) (there m) with ∈-++⁻ xs m
... | inj₁ m′ = inj₁ (there m′)
... | inj₂ m′ = inj₂ m′

∈-map⁺ : ∀ {A B : Set} (f : A → B) {x xs} → x ∈L xs → f x ∈L mapK f xs
∈-map⁺ f here      = here
∈-map⁺ f (there m) = there (∈-map⁺ f m)

∈-map⁻ : ∀ {A B : Set} (f : A → B) {y} xs → y ∈L mapK f xs →
         Σ A λ x → (x ∈L xs) × (f x ≡ y)
∈-map⁻ f (x ∷ xs) here      = x , here , refl
∈-map⁻ f (x ∷ xs) (there m) with ∈-map⁻ f xs m
... | x′ , m′ , eq = x′ , there m′ , eq

∈-concat⁺ : ∀ {A : Set} {z : A} {xs} xss → z ∈L xs → xs ∈L xss → z ∈L concatK xss
∈-concat⁺ (xs ∷ xss) m here       = ∈-++ˡ (concatK xss) m
∈-concat⁺ (ys ∷ xss) m (there mm) = ∈-++ʳ ys (∈-concat⁺ xss m mm)

∈-concat⁻ : ∀ {A : Set} {z : A} xss → z ∈L concatK xss →
            Σ (List A) λ xs → (z ∈L xs) × (xs ∈L xss)
∈-concat⁻ (xs ∷ xss) m with ∈-++⁻ xs m
... | inj₁ m′ = xs , m′ , here
... | inj₂ m′ with ∈-concat⁻ xss m′
...   | ys , m″ , mm = ys , m″ , there mm

-- Every element of a list, paired with the proof that it is there.
withMem : ∀ {A : Set} (xs : List A) → List (Σ A λ x → x ∈L xs)
withMem []       = []
withMem (x ∷ xs) = (x , here) ∷ mapK (λ p → fst p , there (snd p)) (withMem xs)

withMem-has : ∀ {A : Set} {x : A} xs (m : x ∈L xs) → (x , m) ∈L withMem xs
withMem-has (x ∷ xs) here      = here
withMem-has (y ∷ xs) (there m) =
  there (∈-map⁺ (λ p → fst p , there (snd p)) (withMem-has xs m))

-- Decidable search for a witness in a list.
first? : ∀ {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) →
         Dec (Σ A λ x → (x ∈L xs) × P x)
first? d [] = no λ { (_ , () , _) }
first? d (x ∷ xs) with d x
... | yes p = yes (x , here , p)
... | no ¬p with first? d xs
...   | yes (y , m , q) = yes (y , there m , q)
...   | no ¬q = no λ { (_ , here , p) → ¬p p ; (y , there m , q) → ¬q (y , m , q) }

T? : ∀ b → Dec (T b)
T? true  = yes tt
T? false = no λ ()

isYes : ∀ {P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no _)  = false

isYes-sound : ∀ {P : Set} (d : Dec P) → T (isYes d) → P
isYes-sound (yes p) _ = p

isYes-complete : ∀ {P : Set} (d : Dec P) → P → T (isYes d)
isYes-complete (yes _) _ = tt
isYes-complete (no ¬p) p = ¬p p

