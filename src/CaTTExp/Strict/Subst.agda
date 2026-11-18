------------------------------------------------------------------------
-- The chain maps induced by substitutions on supports.
--
-- CaTTExp.Gray.Support computes the top chain of every term as a bag
-- (topS), and acts by a substitution σ through applyF (topsSub σ): a
-- basis element (v₁ … vₘ) goes to the tensor topS(σv₁) ⊗ … ⊗ topS(σvₘ).
-- This module proves that this action is the chain-level image of
-- substitution:
--
--     topS (t [ σ ]) ≈ applyF (topsSub σ) (topS t)       (t scoped)
--
-- i.e. the interpretation of terms by their top chains commutes with
-- substitution, and the action is functorial (applyF-applyF) and
-- multiplicative (applyF-prod).
------------------------------------------------------------------------
module CaTTExp.Strict.Subst where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Bag
open import CaTTExp.Gray.Pure hiding (Tuple)
import CaTTExp.Subst ∅ graySide as S

------------------------------------------------------------------------
-- Bridges to the list functions of CaTTExp.Gray.Support.

concatMap-cm : ∀ (g : Tuple → Bag) X → concatMap g X ≡ cm g X
concatMap-cm g []      = refl
concatMap-cm g (x ∷ X) = cong (g x ++_) (concatMap-cm g X)

map-cm : ∀ (h : Tuple → Tuple) Y → map h Y ≡ cm (λ y → h y ∷ []) Y
map-cm h []      = refl
map-cm h (y ∷ Y) = cong (h y ∷_) (map-cm h Y)

prodT-prod : ∀ X Y → prodT X Y ≡ prod X Y
prodT-prod []      Y = refl
prodT-prod (x ∷ X) Y = cong₂ _++_ (map-cm (x ++_) Y) (prodT-prod X Y)

applyF-cm : ∀ R C → applyF R C ≡ cm (Ftuple R) C
applyF-cm R C = concatMap-cm (Ftuple R) C

Ftuple-cons : ∀ R v w → Ftuple R (v ∷ w) ≡ prod (nth v R) (Ftuple R w)
Ftuple-cons R v w = prodT-prod (nth v R) (Ftuple R w)

------------------------------------------------------------------------
-- nth.

lengthL : ∀ {A : Set} → List A → Nat
lengthL []       = 0
lengthL (_ ∷ xs) = suc (lengthL xs)

lengthL-snoc : ∀ {A : Set} (R : List A) x → lengthL (R ++ x ∷ []) ≡ suc (lengthL R)
lengthL-snoc []      x = refl
lengthL-snoc (r ∷ R) x = cong suc (lengthL-snoc R x)

nth-snoc : ∀ v R x → nth v (R ++ x ∷ []) ≡ (if v ==ℕ lengthL R then x else nth v R)
nth-snoc zero    []      x = refl
nth-snoc (suc v) []      x = refl
nth-snoc zero    (r ∷ R) x = refl
nth-snoc (suc v) (r ∷ R) x = nth-snoc v R x

nth-map : ∀ (g : Bag → Bag) → g [] ≡ [] → ∀ v R → nth v (map g R) ≡ g (nth v R)
nth-map g g0 v       []      = sym g0
nth-map g g0 zero    (r ∷ R) = refl
nth-map g g0 (suc v) (r ∷ R) = nth-map g g0 v R

map-snoc : ∀ (g : Bag → Bag) R x → map g (R ++ x ∷ []) ≡ map g R ++ g x ∷ []
map-snoc g []      x = refl
map-snoc g (r ∷ R) x = cong (g r ∷_) (map-snoc g R x)

lengthL-map : ∀ (g : Bag → Bag) R → lengthL (map g R) ≡ lengthL R
lengthL-map g []      = refl
lengthL-map g (r ∷ R) = cong suc (lengthL-map g R)

lengthL-topsSub : ∀ σ → lengthL (topsSub σ) ≡ lenₛ σ
lengthL-topsSub ⟨⟩       = refl
lengthL-topsSub (σ ,ₛ t) = trans (lengthL-snoc (topsSub σ) (topS t)) (cong suc (lengthL-topsSub σ))

private
  <suc-≢ : ∀ i n → T (i <ℕ suc n) → (i ==ℕ n) ≡ false → T (i <ℕ n)
  <suc-≢ zero    zero    _ ()
  <suc-≢ zero    (suc n) _ _ = tt
  <suc-≢ (suc i) zero    p _ = ⊥-elim (no-<0 i p)
    where
    no-<0 : ∀ i → T (i <ℕ zero) → ⊥
    no-<0 _ ()
  <suc-≢ (suc i) (suc n) p q = <suc-≢ i n p q

nth-topsSub : ∀ σ i → T (i <ℕ lenₛ σ) → nth i (topsSub σ) ≡ topS (lookupₛ σ i)
nth-topsSub (σ ,ₛ t) i p
  rewrite nth-snoc i (topsSub σ) (topS t) | lengthL-topsSub σ with i ==ℕ lenₛ σ in e
... | true  = refl
... | false = nth-topsSub σ i (<suc-≢ i (lenₛ σ) p e)

------------------------------------------------------------------------
-- Pointwise equality of lists of bags.

PW : List Bag → List Bag → Set
PW R R' = ∀ v → nth v R ≈ nth v R'

Ftuple-cong : ∀ R R' → PW R R' → ∀ w → Ftuple R w ≈ Ftuple R' w
Ftuple-cong R R' p []      = ≈-refl
Ftuple-cong R R' p (v ∷ w) =
  subst₂≈ (sym (Ftuple-cons R v w)) (sym (Ftuple-cons R' v w))
    (≈-trans (prod-congˡ (Ftuple R w) (p v)) (prod-congʳ (nth v R') (Ftuple-cong R R' p w)))
  where
  subst₂≈ : ∀ {X X' Y Y'} → X ≡ X' → Y ≡ Y' → X ≈ Y → X' ≈ Y'
  subst₂≈ refl refl q = q

applyF-congS : ∀ R R' → PW R R' → ∀ C → applyF R C ≈ applyF R' C
applyF-congS R R' p C =
  ≈-trans (≡→≈ (applyF-cm R C))
 (≈-trans (cm-ext' _ _ C (Ftuple-cong R R' p))
          (≡→≈ (sym (applyF-cm R' C))))

applyF-cong : ∀ R {C C'} → C ≈ C' → applyF R C ≈ applyF R C'
applyF-cong R {C} {C'} p =
  ≈-trans (≡→≈ (applyF-cm R C)) (≈-trans (cm-cong _ C C' p) (≡→≈ (sym (applyF-cm R C'))))

applyF-++ : ∀ R X Y → applyF R (X ++ Y) ≡ applyF R X ++ applyF R Y
applyF-++ R X Y =
  trans (applyF-cm R (X ++ Y))
 (trans (cm-++ (Ftuple R) X Y)
        (sym (cong₂ _++_ (applyF-cm R X) (applyF-cm R Y))))

------------------------------------------------------------------------
-- Multiplicativity and functoriality.

Ftuple-++ : ∀ R x y → Ftuple R (x ++ y) ≈ prod (Ftuple R x) (Ftuple R y)
Ftuple-++ R []      y = ≈-sym (prod-unitˡ (Ftuple R y))
Ftuple-++ R (v ∷ x) y =
  begin
    Ftuple R (v ∷ (x ++ y))
  ≈⟨ ≡→≈ (Ftuple-cons R v (x ++ y)) ⟩
    prod (nth v R) (Ftuple R (x ++ y))
  ≈⟨ prod-congʳ (nth v R) (Ftuple-++ R x y) ⟩
    prod (nth v R) (prod (Ftuple R x) (Ftuple R y))
  ≈⟨ ≈-sym (prod-assoc (nth v R) (Ftuple R x) (Ftuple R y)) ⟩
    prod (prod (nth v R) (Ftuple R x)) (Ftuple R y)
  ≈⟨ ≡→≈ (cong (λ Z → prod Z (Ftuple R y)) (sym (Ftuple-cons R v x))) ⟩
    prod (Ftuple R (v ∷ x)) (Ftuple R y)
  ∎

cmF-prod : ∀ R X Y → cm (Ftuple R) (prod X Y) ≈ prod (cm (Ftuple R) X) (cm (Ftuple R) Y)
cmF-prod R X Y =
  begin
    cm F (cm (λ x → cm (λ y → (x ++ y) ∷ []) Y) X)
  ≈⟨ ≡→≈ (cm-fuse F _ X) ⟩
    cm (λ x → cm F (cm (λ y → (x ++ y) ∷ []) Y)) X
  ≈⟨ cm-ext' _ _ X (λ x → ≡→≈ (cm-fuse F _ Y)) ⟩
    cm (λ x → cm (λ y → F (x ++ y) ++ []) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → cm-ext' _ _ Y (λ y →
       ≈-trans (≡→≈ (++-[]L (F (x ++ y)))) (Ftuple-++ R x y))) ⟩
    cm (λ x → cm (λ y → prod (F x) (F y)) Y) X
  ≈⟨ cm-ext' _ _ X (λ x → ≈-sym (prod-cmʳ (F x) F Y)) ⟩
    cm (λ x → prod (F x) (cm F Y)) X
  ≈⟨ ≡→≈ (sym (prod-cmˡ F X (cm F Y))) ⟩
    prod (cm F X) (cm F Y)
  ∎
  where
  F = Ftuple R

applyF-Ftuple : ∀ S R w → applyF S (Ftuple R w) ≈ Ftuple (map (applyF S) R) w
applyF-Ftuple S R []      = ≈-refl
applyF-Ftuple S R (v ∷ w) =
  begin
    applyF S (Ftuple R (v ∷ w))
  ≈⟨ ≡→≈ (trans (applyF-cm S (Ftuple R (v ∷ w))) (cong (cm (Ftuple S)) (Ftuple-cons R v w))) ⟩
    cm (Ftuple S) (prod (nth v R) (Ftuple R w))
  ≈⟨ cmF-prod S (nth v R) (Ftuple R w) ⟩
    prod (cm (Ftuple S) (nth v R)) (cm (Ftuple S) (Ftuple R w))
  ≈⟨ ≡→≈ (cong₂ prod (sym (applyF-cm S (nth v R))) (sym (applyF-cm S (Ftuple R w)))) ⟩
    prod (applyF S (nth v R)) (applyF S (Ftuple R w))
  ≈⟨ ++-congprod ⟩
    prod (nth v (map (applyF S) R)) (Ftuple (map (applyF S) R) w)
  ≈⟨ ≡→≈ (sym (Ftuple-cons (map (applyF S) R) v w)) ⟩
    Ftuple (map (applyF S) R) (v ∷ w)
  ∎
  where
  ++-congprod : prod (applyF S (nth v R)) (applyF S (Ftuple R w))
              ≈ prod (nth v (map (applyF S) R)) (Ftuple (map (applyF S) R) w)
  ++-congprod =
    ≈-trans (prod-congˡ (applyF S (Ftuple R w)) (≡→≈ (sym (nth-map (applyF S) refl v R))))
            (prod-congʳ (nth v (map (applyF S) R)) (applyF-Ftuple S R w))

applyF-applyF : ∀ S R C → applyF S (applyF R C) ≈ applyF (map (applyF S) R) C
applyF-applyF S R C =
  begin
    applyF S (applyF R C)
  ≈⟨ ≡→≈ (trans (applyF-cm S (applyF R C)) (cong (cm (Ftuple S)) (applyF-cm R C))) ⟩
    cm (Ftuple S) (cm (Ftuple R) C)
  ≈⟨ ≡→≈ (cm-fuse (Ftuple S) (Ftuple R) C) ⟩
    cm (λ w → cm (Ftuple S) (Ftuple R w)) C
  ≈⟨ cm-ext' _ _ C (λ w → ≈-trans (≡→≈ (sym (applyF-cm S (Ftuple R w)))) (applyF-Ftuple S R w)) ⟩
    cm (Ftuple (map (applyF S) R)) C
  ≈⟨ ≡→≈ (sym (applyF-cm _ C)) ⟩
    applyF (map (applyF S) R) C
  ∎

------------------------------------------------------------------------
-- Top chains commute with substitution.

mutual
  topS-sub : ∀ t σ → S.ScTm (lenₛ σ) t → topS (t [ σ ]tm) ≈ applyF (topsSub σ) (topS t)
  topS-sub (var i) σ p =
    ≈-sym (≈-trans (≡→≈ (trans (++-[]L _) (Ftuple-cons (topsSub σ) i [])))
          (≈-trans (prod-unitʳ (nth i (topsSub σ))) (≡→≈ (nth-topsSub σ i p))))
  topS-sub (coh Θ ⋆ τ)           σ p = ≈-refl
  topS-sub (coh Θ (arr A t u) τ) σ p =
    ≈-sym (≈-trans (applyF-applyF (topsSub σ) (topsSub τ) C)
                   (applyF-congS _ _ (λ v → ≈-sym (topsSub-∘ τ σ p v)) C))
    where
    C = if cohCase Θ A t u then [] else topT (homs Θ)
  topS-sub (cst ()) σ p

  topsSub-∘ : ∀ τ σ → S.ScSub (lenₛ σ) τ → PW (topsSub (τ ∘ σ)) (map (applyF (topsSub σ)) (topsSub τ))
  topsSub-∘ ⟨⟩       σ p v = ≡→≈ (sym (nth-map (applyF (topsSub σ)) refl v []))
  topsSub-∘ (τ ,ₛ t) σ (p , q) v
    rewrite nth-snoc v (topsSub (τ ∘ σ)) (topS (t [ σ ]tm))
          | map-snoc (applyF (topsSub σ)) (topsSub τ) (topS t)
          | nth-snoc v (map (applyF (topsSub σ)) (topsSub τ)) (applyF (topsSub σ) (topS t))
          | lengthL-topsSub (τ ∘ σ)
          | lengthL-map (applyF (topsSub σ)) (topsSub τ)
          | lengthL-topsSub τ
          | S.lenₛ-∘ τ σ
    with v ==ℕ lenₛ τ
  ... | true  = topS-sub t σ q
  ... | false = topsSub-∘ τ σ p v
