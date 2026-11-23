------------------------------------------------------------------------
-- Sets of words and their interpretations (ledger S3a, the Gray model
-- of P, notes/uniform-checker.md §1.8 Route step 1).
--
-- A support in the Gray model is a set of tuples (Gray/Support.agda):
-- union is the sum of top chains, and the concatenation product is
-- composition across objects. Here a set is a list of words over an
-- alphabet K, compared up to membership (_≈S_). The same algebra
-- serves twice: with K the generator names it holds actual supports,
-- and with K symbols for the faces of schema variables it holds
-- symbolic supports, which `iE ρ` reads back once the variables are
-- given values. `iE ρ` preserves union exactly and the product up to
-- ≈S (`iE-++`, `iE-prod`). Rewriting a symbol by an expression is
-- itself an interpretation, so `iE-comp` makes rewrites sound
-- (`rewrite-sound`). Inclusion of symbolic sets is decided word by
-- word (`incl?`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Join.Quiver using (_⊎_; inj₁; inj₂; Dec; yes; no)
open import CaTTExp.Join.Finite using (_∈L_; here; there)
open import CaTTExp.Uniform.ListKit
open import CaTTExp.Uniform.Grid using (≟List)

module CaTTExp.Uniform.SuppAlg where

SExp : Set → Set
SExp K = List (List K)

------------------------------------------------------------------------
-- Lists.

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

------------------------------------------------------------------------
-- Set equality.

module _ {K : Set} where
  infix 4 _⊆S_ _≈S_
  _⊆S_ _≈S_ : SExp K → SExp K → Set
  A ⊆S B = ∀ {w} → w ∈L A → w ∈L B
  A ≈S B = (A ⊆S B) × (B ⊆S A)

  ≈S-refl : ∀ {A} → A ≈S A
  ≈S-refl = (λ m → m) , (λ m → m)

  ≈S-sym : ∀ {A B} → A ≈S B → B ≈S A
  ≈S-sym (f , g) = g , f

  ≈S-trans : ∀ {A B C} → A ≈S B → B ≈S C → A ≈S C
  ≈S-trans (f , g) (f′ , g′) = (λ m → f′ (f m)) , (λ m → g (g′ m))

  ≡⇒≈S : ∀ {A B} → A ≡ B → A ≈S B
  ≡⇒≈S refl = ≈S-refl

  ∪-cong : ∀ {A A′ B B′} → A ≈S A′ → B ≈S B′ → (A ++ B) ≈S (A′ ++ B′)
  ∪-cong {A} {A′} {B} {B′} (f , g) (f′ , g′) = to , from
    where
    to : (A ++ B) ⊆S (A′ ++ B′)
    to m with ∈-++⁻ A m
    ... | inj₁ m′ = ∈-++ˡ B′ (f m′)
    ... | inj₂ m′ = ∈-++ʳ A′ (f′ m′)
    from : (A′ ++ B′) ⊆S (A ++ B)
    from m with ∈-++⁻ A′ m
    ... | inj₁ m′ = ∈-++ˡ B (g m′)
    ... | inj₂ m′ = ∈-++ʳ A (g′ m′)

------------------------------------------------------------------------
-- The concatenation product.

module _ {K : Set} where
  prodE : SExp K → SExp K → SExp K
  prodE A B = concatK (mapK (λ a → mapK (a ++_) B) A)

  ∈-prod⁺ : ∀ {a b} (A B : SExp K) → a ∈L A → b ∈L B → (a ++ b) ∈L prodE A B
  ∈-prod⁺ {a} A B ma mb =
    ∈-concat⁺ (mapK (λ a′ → mapK (a′ ++_) B) A) (∈-map⁺ (a ++_) mb) (∈-map⁺ (λ a′ → mapK (a′ ++_) B) ma)

  ∈-prod⁻ : ∀ {w} (A B : SExp K) → w ∈L prodE A B →
            Σ (List K) λ a → Σ (List K) λ b → (a ∈L A) × (b ∈L B) × (w ≡ a ++ b)
  ∈-prod⁻ A B m with ∈-concat⁻ (mapK (λ a → mapK (a ++_) B) A) m
  ... | xs , mx , mxs with ∈-map⁻ (λ a → mapK (a ++_) B) A mxs
  ...   | a , ma , refl with ∈-map⁻ (a ++_) B mx
  ...     | b , mb , refl = a , b , ma , mb , refl

  prod-cong : ∀ A A′ B B′ → A ≈S A′ → B ≈S B′ → prodE A B ≈S prodE A′ B′
  prod-cong A A′ B B′ (f , g) (f′ , g′) = to , from
    where
    to : prodE A B ⊆S prodE A′ B′
    to m with ∈-prod⁻ A B m
    ... | a , b , ma , mb , refl = ∈-prod⁺ A′ B′ (f ma) (f′ mb)
    from : prodE A′ B′ ⊆S prodE A B
    from m with ∈-prod⁻ A′ B′ m
    ... | a , b , ma , mb , refl = ∈-prod⁺ A B (g ma) (g′ mb)

  prod-assoc : ∀ A B C → prodE (prodE A B) C ≈S prodE A (prodE B C)
  prod-assoc A B C = to , from
    where
    to : prodE (prodE A B) C ⊆S prodE A (prodE B C)
    to m with ∈-prod⁻ (prodE A B) C m
    ... | ab , c , mab , mc , refl with ∈-prod⁻ A B mab
    ...   | a , b , ma , mb , refl =
      subst (_∈L prodE A (prodE B C)) (sym (++-assoc a b c)) (∈-prod⁺ A (prodE B C) ma (∈-prod⁺ B C mb mc))
    from : prodE A (prodE B C) ⊆S prodE (prodE A B) C
    from m with ∈-prod⁻ A (prodE B C) m
    ... | a , bc , ma , mbc , refl with ∈-prod⁻ B C mbc
    ...   | b , c , mb , mc , refl =
      subst (_∈L prodE (prodE A B) C) (++-assoc a b c) (∈-prod⁺ (prodE A B) C (∈-prod⁺ A B ma mb) mc)

  prod-unitˡ : ∀ A → prodE ([] ∷ []) A ≈S A
  prod-unitˡ A = to , from
    where
    to : prodE ([] ∷ []) A ⊆S A
    to m with ∈-prod⁻ ([] ∷ []) A m
    ... | .[] , b , here , mb , refl = mb
    from : A ⊆S prodE ([] ∷ []) A
    from m = ∈-prod⁺ ([] ∷ []) A here m

  prod-unitʳ : ∀ A → prodE A ([] ∷ []) ≈S A
  prod-unitʳ A = to , from
    where
    to : prodE A ([] ∷ []) ⊆S A
    to m with ∈-prod⁻ A ([] ∷ []) m
    ... | a , .[] , ma , here , refl = subst (_∈L A) (sym (++-[] a)) ma
    from : A ⊆S prodE A ([] ∷ [])
    from {w} m = subst (_∈L prodE A ([] ∷ [])) (++-[] w) (∈-prod⁺ A ([] ∷ []) m here)

  prod-∪ˡ : ∀ A B C → prodE (A ++ B) C ≈S (prodE A C ++ prodE B C)
  prod-∪ˡ A B C = to , from
    where
    to : prodE (A ++ B) C ⊆S (prodE A C ++ prodE B C)
    to m with ∈-prod⁻ (A ++ B) C m
    ... | a , c , mab , mc , refl with ∈-++⁻ A mab
    ...   | inj₁ ma = ∈-++ˡ (prodE B C) (∈-prod⁺ A C ma mc)
    ...   | inj₂ mb = ∈-++ʳ (prodE A C) (∈-prod⁺ B C mb mc)
    from : (prodE A C ++ prodE B C) ⊆S prodE (A ++ B) C
    from m with ∈-++⁻ (prodE A C) m
    ... | inj₁ m′ with ∈-prod⁻ A C m′
    ...   | a , c , ma , mc , refl = ∈-prod⁺ (A ++ B) C (∈-++ˡ B ma) mc
    from m | inj₂ m′ with ∈-prod⁻ B C m′
    ...   | b , c , mb , mc , refl = ∈-prod⁺ (A ++ B) C (∈-++ʳ A mb) mc

------------------------------------------------------------------------
-- Interpretation of words: each letter stands for a set.

module Interp {K L : Set} (ρ : K → SExp L) where
  iW : List K → SExp L
  iW []      = [] ∷ []
  iW (k ∷ w) = prodE (ρ k) (iW w)

  iE : SExp K → SExp L
  iE []      = []
  iE (w ∷ e) = iW w ++ iE e

  iE-++ : ∀ A B → iE (A ++ B) ≡ iE A ++ iE B
  iE-++ []      B = refl
  iE-++ (w ∷ A) B = trans (cong (iW w ++_) (iE-++ A B)) (sym (++-assoc (iW w) (iE A) (iE B)))

  ∈-iE⁺ : ∀ {x w} A → w ∈L A → x ∈L iW w → x ∈L iE A
  ∈-iE⁺ (w ∷ A) here      mx = ∈-++ˡ (iE A) mx
  ∈-iE⁺ (w′ ∷ A) (there m) mx = ∈-++ʳ (iW w′) (∈-iE⁺ A m mx)

  ∈-iE⁻ : ∀ {x} A → x ∈L iE A → Σ (List K) λ w → (w ∈L A) × (x ∈L iW w)
  ∈-iE⁻ (w ∷ A) m with ∈-++⁻ (iW w) m
  ... | inj₁ m′ = w , here , m′
  ... | inj₂ m′ with ∈-iE⁻ A m′
  ...   | w′ , mw , mx = w′ , there mw , mx

  iE-mono : ∀ {A B} → A ⊆S B → iE A ⊆S iE B
  iE-mono {A} {B} f m with ∈-iE⁻ A m
  ... | w , mw , mx = ∈-iE⁺ B (f mw) mx

  iE-cong : ∀ {A B} → A ≈S B → iE A ≈S iE B
  iE-cong (f , g) = iE-mono f , iE-mono g

  iW-++ : ∀ a b → iW (a ++ b) ≈S prodE (iW a) (iW b)
  iW-++ []      b = ≈S-sym (prod-unitˡ (iW b))
  iW-++ (k ∷ a) b =
    ≈S-trans (prod-cong (ρ k) (ρ k) (iW (a ++ b)) (prodE (iW a) (iW b)) ≈S-refl (iW-++ a b))
             (≈S-sym (prod-assoc (ρ k) (iW a) (iW b)))

  iE-prod : ∀ A B → iE (prodE A B) ≈S prodE (iE A) (iE B)
  iE-prod A B = to , from
    where
    to : iE (prodE A B) ⊆S prodE (iE A) (iE B)
    to m with ∈-iE⁻ (prodE A B) m
    ... | w , mw , mx with ∈-prod⁻ A B mw
    ...   | a , b , ma , mb , refl with ∈-prod⁻ (iW a) (iW b) (fst (iW-++ a b) mx)
    ...     | u , v , mu , mv , refl = ∈-prod⁺ (iE A) (iE B) (∈-iE⁺ A ma mu) (∈-iE⁺ B mb mv)
    from : prodE (iE A) (iE B) ⊆S iE (prodE A B)
    from m with ∈-prod⁻ (iE A) (iE B) m
    ... | u , v , mu , mv , refl with ∈-iE⁻ A mu | ∈-iE⁻ B mv
    ...   | a , ma , mua | b , mb , mvb =
      ∈-iE⁺ (prodE A B) (∈-prod⁺ A B ma mb) (snd (iW-++ a b) (∈-prod⁺ (iW a) (iW b) mua mvb))

  iE-unit : iE ([] ∷ []) ≈S ([] ∷ [])
  iE-unit = ≡⇒≈S refl

  iE-letter : ∀ k → iE ((k ∷ []) ∷ []) ≈S ρ k
  iE-letter k = ≈S-trans (≡⇒≈S (++-[] (prodE (ρ k) ([] ∷ [])))) (prod-unitʳ (ρ k))

-- Interpretations respect pointwise equality of the letters' values
-- and compose.
module _ {K L : Set} where
  iW-ρcong : ∀ {ρ ρ′ : K → SExp L} → (∀ k → ρ k ≈S ρ′ k) → ∀ w → Interp.iW ρ w ≈S Interp.iW ρ′ w
  iW-ρcong e []      = ≈S-refl
  iW-ρcong {ρ} {ρ′} e (k ∷ w) = prod-cong (ρ k) (ρ′ k) (Interp.iW ρ w) (Interp.iW ρ′ w) (e k) (iW-ρcong e w)

  iE-ρcong : ∀ {ρ ρ′ : K → SExp L} → (∀ k → ρ k ≈S ρ′ k) → ∀ A → Interp.iE ρ A ≈S Interp.iE ρ′ A
  iE-ρcong e []      = ≈S-refl
  iE-ρcong e (w ∷ A) = ∪-cong (iW-ρcong e w) (iE-ρcong e A)

module _ {J K L : Set} (ρ : K → SExp L) (ρ′ : J → SExp K) where
  private
    module I  = Interp ρ
    module I′ = Interp ρ′
    module IC = Interp (λ j → I.iE (ρ′ j))

  iW-comp : ∀ w → I.iE (I′.iW w) ≈S IC.iW w
  iW-comp []      = ≈S-refl
  iW-comp (j ∷ w) = ≈S-trans (I.iE-prod (ρ′ j) (I′.iW w))
                      (prod-cong (I.iE (ρ′ j)) (I.iE (ρ′ j)) (I.iE (I′.iW w)) (IC.iW w) ≈S-refl (iW-comp w))

  iE-comp : ∀ A → I.iE (I′.iE A) ≈S IC.iE A
  iE-comp []      = ≈S-refl
  iE-comp (w ∷ A) =
    ≈S-trans (≡⇒≈S (I.iE-++ (I′.iW w) (I′.iE A))) (∪-cong (iW-comp w) (iE-comp A))

------------------------------------------------------------------------
-- Rewriting one letter by an expression.

module Rewrite {K : Set} (_≟K_ : (a b : K) → Dec (a ≡ b)) where
  with1 : K → SExp K → K → SExp K
  with1 k e k′ with k′ ≟K k
  ... | yes _ = e
  ... | no _  = (k′ ∷ []) ∷ []

  rw : K → SExp K → SExp K → SExp K
  rw k e = Interp.iE (with1 k e)

  -- If k and e have the same value, rewriting changes no value.
  rewrite-sound : ∀ {L} (ρ : K → SExp L) k e →
                  Interp.iE ρ e ≈S ρ k → ∀ A → Interp.iE ρ (rw k e A) ≈S Interp.iE ρ A
  rewrite-sound ρ k e h A =
    ≈S-trans (iE-comp ρ (with1 k e) A) (iE-ρcong pt A)
    where
    pt : ∀ k′ → Interp.iE ρ (with1 k e k′) ≈S ρ k′
    pt k′ with k′ ≟K k
    ... | yes refl = h
    ... | no _     = Interp.iE-letter ρ k′

  -- Decided inclusion of symbolic sets.
  memW : List K → SExp K → Bool
  memW w []        = false
  memW w (w′ ∷ B)  = isYes (≟List _≟K_ w w′) ∨ memW w B

  incl? : SExp K → SExp K → Bool
  incl? A B = all (λ w → memW w B) A

  memW-sound : ∀ w B → T (memW w B) → w ∈L B
  memW-sound w (w′ ∷ B) t with ≟List _≟K_ w w′
  ... | yes refl = here
  ... | no _     = there (memW-sound w B t)

  incl-sound : ∀ A B → T (incl? A B) → A ⊆S B
  incl-sound (w ∷ A) B t here      = memW-sound w B (∧-fst t)
  incl-sound (w ∷ A) B t (there m) = incl-sound A B (∧-snd {memW w B} t) m

  same? : SExp K → SExp K → Bool
  same? A B = incl? A B ∧ incl? B A

  same-sound : ∀ A B → T (same? A B) → A ≈S B
  same-sound A B t = incl-sound A B (∧-fst t) , incl-sound B A (∧-snd {incl? A B} t)
