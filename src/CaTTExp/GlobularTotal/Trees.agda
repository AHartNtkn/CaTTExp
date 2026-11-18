------------------------------------------------------------------------
-- F2c, lemma 2 (first half): the tree parser inverts the tree builder.
--
--   treeOf (ctxOf τ) ≡ just τ        for every tree τ.
--
-- The proof computes the depth sequence that `pairDepths` reads off a
-- built context (the preorder depths of the tree's nodes, `depthsF`),
-- and shows that `forest` parses any preorder depth sequence back.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature

module CaTTExp.GlobularTotal.Trees (𝕊 : Signature) where

open Signature 𝕊
open import CaTTExp.Pasting 𝕊
open import CaTTExp.PastingTrees 𝕊
open Parse

------------------------------------------------------------------------
-- Preorder depths.

mutual
  depthsF : Nat → List Tree → List Nat
  depthsF lvl []             = []
  depthsF lvl (node cs ∷ ts) = lvl ∷ (depthsF (suc lvl) cs ++ depthsF lvl ts)

------------------------------------------------------------------------
-- List arithmetic.

private
  ++-assoc : ∀ (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  ++-[] : ∀ (xs : List Nat) → xs ++ [] ≡ xs
  ++-[] []       = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  length-++ : ∀ (xs ys : List Nat) → length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  -- ≤ as < suc
  _≤_ : Nat → Nat → Set
  a ≤ b = T (a <ℕ suc b)

  <-suc : ∀ d l → T (d <ℕ l) → T (d <ℕ suc l)
  <-suc zero    (suc l) _ = tt
  <-suc (suc d) (suc l) p = <-suc d l p

  ≤-refl : ∀ a → a ≤ a
  ≤-refl zero    = tt
  ≤-refl (suc a) = ≤-refl a

  ≤-+l : ∀ a b c → (a + b) ≤ c → a ≤ c
  ≤-+l zero    b c       _ = tt
  ≤-+l (suc a) b zero    ()
  ≤-+l (suc a) b (suc c) p = ≤-+l a b c p

  ≤-+r : ∀ a b c → (a + b) ≤ c → b ≤ c
  ≤-+r zero    b c       p = p
  ≤-+r (suc a) b zero    ()
  ≤-+r (suc a) b (suc c) p = <-suc b (suc c) (≤-+r a b c p)

  <→≢ : ∀ d l → T (d <ℕ l) → (d ==ℕ l) ≡ false
  <→≢ zero    (suc l) _ = refl
  <→≢ (suc d) (suc l) p = <→≢ d l p

  ==-refl : ∀ l → (l ==ℕ l) ≡ true
  ==-refl zero    = refl
  ==-refl (suc l) = ==-refl l

  <-self : ∀ l → T (l <ℕ suc l)
  <-self zero    = tt
  <-self (suc l) = <-self l

------------------------------------------------------------------------
-- Claim B: forest parses preorder depth sequences.

-- `rest` may follow a forest at level lvl: it is empty or starts lower.
Stop : Nat → List Nat → Set
Stop lvl []      = ⊤
Stop lvl (d ∷ _) = T (d <ℕ lvl)

stop-suc : ∀ lvl rest → Stop lvl rest → Stop (suc lvl) rest
stop-suc lvl []      _ = tt
stop-suc lvl (d ∷ _) p = <-suc d lvl p

stop-forest : ∀ lvl ts rest → Stop lvl rest → Stop (suc lvl) (depthsF lvl ts ++ rest)
stop-forest lvl []             rest p = stop-suc lvl rest p
stop-forest lvl (node cs ∷ ts) rest p = <-self lvl

private
  if-true : ∀ {a} {A : Set a} b {x y : A} → T b → (if b then x else y) ≡ x
  if-true true _ = refl

forest-ok : ∀ n lvl ts rest → length (depthsF lvl ts) ≤ n → Stop lvl rest →
            forest (suc n) lvl (depthsF lvl ts ++ rest) ≡ just (ts , rest)
forest-ok n lvl [] []       _ _ = refl
forest-ok n lvl [] (d ∷ ds) _ p rewrite <→≢ d lvl p = if-true (d <ℕ lvl) p
forest-ok zero    lvl (node cs ∷ ts) rest () p
forest-ok (suc n) lvl (node cs ∷ ts) rest l p =
  step (subst (_≤ n) (length-++ (depthsF (suc lvl) cs) (depthsF lvl ts)) l)
  where
  step : (length (depthsF (suc lvl) cs) + length (depthsF lvl ts)) ≤ n →
         forest (suc (suc n)) lvl (depthsF lvl (node cs ∷ ts) ++ rest) ≡ just (node cs ∷ ts , rest)
  step lsum
    rewrite ++-assoc (depthsF (suc lvl) cs) (depthsF lvl ts) rest
          | ==-refl lvl
          | forest-ok n (suc lvl) cs (depthsF lvl ts ++ rest) (≤-+l (length (depthsF (suc lvl) cs)) (length (depthsF lvl ts)) n lsum) (stop-forest lvl ts rest p)
          | forest-ok n lvl ts rest (≤-+r (length (depthsF (suc lvl) cs)) (length (depthsF lvl ts)) n lsum) p = refl

------------------------------------------------------------------------
-- Claim A: the depth sequence of a built context.

kids : Tree → List Tree
kids (node ts) = ts

private
  step : ∀ {Γ} A B ds → pairDepths Γ ≡ just ds →
         pairDepths (Γ ▸ A ▸ B) ≡ just (ds ++ (suc (dim A) ∷ []))
  step {ε}      A B ds ()
  step {Γ ▸ X}  A B ds h rewrite h = refl

  shuffle : ∀ ds k (X Y : List Nat) → ((ds ++ (k ∷ [])) ++ X) ++ Y ≡ ds ++ (k ∷ (X ++ Y))
  shuffle ds k X Y =
    trans (++-assoc (ds ++ (k ∷ [])) X Y)
          (++-assoc ds (k ∷ []) (X ++ Y))

mutual
  build-d : ∀ t {Γ x A} (d : Γ ⊢ps x ∶ A) ds → pairDepths Γ ≡ just ds →
            pairDepths (fst (build t d)) ≡ just (ds ++ depthsF (suc (dim A)) (kids t))
  build-d (node ts) d ds h = buildList-d ts d ds h

  buildList-d : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) ds → pairDepths Γ ≡ just ds →
                pairDepths (fst (buildList ts d)) ≡ just (ds ++ depthsF (suc (dim A)) ts)
  buildList-d [] d ds h = trans h (cong just (sym (++-[] ds)))
  buildList-d (node cs ∷ ts) {Γ} {x} {A} d ds h
    with build (node cs) (pse d)
       | build-d (node cs) (pse d) (ds ++ (suc (dim A) ∷ []))
           (step {Γ} A (arr A (var x) (var (len Γ))) ds h)
  ... | Γ₂ , _ , d₂ | h₂ =
    trans (buildList-d ts (psd d₂) _ h₂)
          (cong just (shuffle ds (suc (dim A)) (depthsF (suc (suc (dim A))) cs)
                                               (depthsF (suc (dim A)) ts)))

------------------------------------------------------------------------
-- The round trip.

private
  forest-ok′ : ∀ ts → forest (suc (length (depthsF 1 ts))) 1 (depthsF 1 ts) ≡ just (ts , [])
  forest-ok′ ts =
    subst (λ zs → forest (suc (length (depthsF 1 ts))) 1 zs ≡ just (ts , []))
          (++-[] (depthsF 1 ts))
          (forest-ok (length (depthsF 1 ts)) 1 ts [] (≤-refl (length (depthsF 1 ts))) tt)

treeOf-ctxOf : ∀ τ → treeOf (ctxOf τ) ≡ just τ
treeOf-ctxOf (node ts)
  rewrite build-d (node ts) pss [] refl
        | forest-ok′ ts
  = refl
