------------------------------------------------------------------------
-- A tuple of K(Δ) through any variable, with 1-cells elsewhere.
--
--   through : PsFacts Δ → lookup Δ g ≡ just C → isStar C ≡ false →
--             InK Δ (homs Δ) (pre ++ g ∷ post)
--
-- where every entry of pre and post is a 1-cell variable (dim 1, so
-- a 0-cell of its hom). Each hom of a pasting context contains such a
-- variable (PsFacts.nonE), and g lies in the hom its type ends in
-- (PsFacts.cellP). This is the tuple τ_g of the ⇐ half of
-- notes/conjectures/single-hom-conservativity.md.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.Gray.Through (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Gray.Support 𝕊
open import CaTTExp.Gray.Cover hiding (Tuple)
open import CaTTExp.Gray.SetFacts 𝕊
open import CaTTExp.Gray.Graded 𝕊
open import CaTTExp.Gray.PsFacts 𝕊
open import CaTTExp.Gray.CohDim 𝕊 using (homIdx-bounds; homIdx-in; lookup→entry)
open import CaTTExp.Gray.FullSupp 𝕊 using (InK; knil; kcons)

module _ (Δ : Ctx) (P : PsFacts Δ) where

  private
    os = objs Δ

  -- o is a 1-cell variable of Δ.
  One : Nat → Set
  One o = Σ Ty λ C → (lookup Δ o ≡ just C) × (dim C ≡ 1)

  data AllOne : Tuple → Set where
    []  : AllOne []
    _∷_ : ∀ {o x} → One o → AllOne x → AllOne (o ∷ x)

  -- The cell of a variable, in the hom its type ends in.
  elAt-k : ∀ v C k → lookup Δ v ≡ just C → homOf os C ≡ just k →
           Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (hcs (homAt Δ k))
  elAt-k v C k e h = filter⇐ (λ c → hom c ==ℕ k) (cells Δ) inCells (==ℕ-refl k)
    where
    inMk : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (mkEl os (v , C))
    inMk rewrite mkEl≡ os v C | h = here refl
    inCells : Any (el v k (dim C ∸ 1) (fst (elBdry C)) (snd (elBdry C)) ≡_) (cells Δ)
    inCells = subst (Any _) (sym (cm≡ (mkEl os) (entries Δ)))
                (any-cm⁺ (mkEl os) (any-at (lookup→entry Δ e) inMk))

  private
    star1 : ∀ C → dim C ≡ 1 → isStar C ≡ false
    star1 (arr _ _ _) _ = refl

    -- A 1-cell of hom k.
    one : ∀ k → T (0 <ℕ k) → T (k <ℕ countL os) →
          Σ El λ e → Any (e ≡_) (hcs (homAt Δ k)) × One (lvl e)
    one k p q with nonE P k p q
    ... | v , C , lv , d1 , hk = _ , elAt-k v C k lv hk , C , lv , d1

    Bd : List Nat → Set
    Bd ks = ∀ {k} → k ∈ᴺ ks → T (0 <ℕ k) × T (k <ℕ countL os)

    zeros : ∀ ks → Bd ks → Σ Tuple λ x → InK Δ (map (homAt Δ) ks) x × AllOne x
    zeros []       b = [] , knil , []
    zeros (k ∷ ks) b with b (here refl) | zeros ks (λ m → b (there m))
    ... | p , q | x , kx , ax with one k p q
    ...   | e , me , oe = lvl e ∷ x , kcons me kx , oe ∷ ax

    go : ∀ ks → Bd ks → ∀ {j g C} → j ∈ᴺ ks → lookup Δ g ≡ just C → homOf os C ≡ just j →
         Σ Tuple λ pre → Σ Tuple λ post →
         InK Δ (map (homAt Δ) ks) (pre ++ g ∷ post) × AllOne pre × AllOne post
    go (k ∷ ks) b {g = g} {C} (here refl) lg hj with zeros ks (λ m → b (there m))
    ... | x , kx , ax = [] , x , kcons (elAt-k g C k lg hj) kx , [] , ax
    go (k ∷ ks) b (there m) lg hj with go ks (λ m' → b (there m')) m lg hj | b (here refl)
    ... | pre , post , kx , ap , aq | p , q with one k p q
    ...   | e , me , oe = lvl e ∷ pre , post , kcons me kx , oe ∷ ap , aq

  -- A tuple of K(Δ) through g, with 1-cells in every other hom.
  through : ∀ g C → lookup Δ g ≡ just C → isStar C ≡ false →
            Σ Tuple λ pre → Σ Tuple λ post →
            InK Δ (homs Δ) (pre ++ g ∷ post) × AllOne pre × AllOne post
  through g C lg st with cellP P g C lg st
  ... | j , hj , p , q =
    go (homIdx (countL os)) (homIdx-bounds (countL os)) (homIdx-in j (countL os) p q) lg hj
