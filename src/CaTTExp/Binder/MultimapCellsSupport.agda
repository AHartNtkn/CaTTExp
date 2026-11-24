------------------------------------------------------------------------
-- Supports of biclosed terms (ledger S26j, step 2b): in a well-formed
-- context, the sweep `closeFrom` computes the least set of entries that
-- contains the given variables and is closed under the dependencies of
-- entry types (`cl-closed`, `cl-least`).
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsSupport where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen
  using (T-if; F-if; _⊎′_; inl; inr; dec; closeFrom-mono; nthY-just)

In : List Nat → Nat → Set
In S i = T (elem i S)

_⊆_ : List Nat → List Nat → Set
S ⊆ D = ∀ i → In S i → In D i

-- Dependencies only go down.
Deps↓ : Ctx → Set
Deps↓ Φ = ∀ j {A} → lookup Φ j ≡ just A → Below j (varsY A)

-- D is closed under dependencies, for the entries below n.
Closed : Ctx → List Nat → Set
Closed Φ D = ∀ j {A} → lookup Φ j ≡ just A → In D j → varsY A ⊆ D

elem-split : ∀ i xs ys → In (xs ++ ys) i → In xs i ⊎′ In ys i
elem-split i []       ys p = inr p
elem-split i (x ∷ xs) ys p with dec (i ==ℕ x)
... | inl q = inl (∨-l (i ==ℕ x) _ q)
... | inr q with elem-split i xs ys (or-r (i ==ℕ x) _ q p)
  where
  or-r : ∀ a b → (T a → ⊥) → T (a ∨ b) → T b
  or-r true  b n _ = ⊥-elim (n tt)
  or-r false b n p = p
...   | inl r = inl (∨-r (i ==ℕ x) _ r)
...   | inr r = inr r

lookup-some : ∀ (Φ : Ctx) j → T (j <ℕ length Φ) → Σ CTy (λ A → lookup Φ j ≡ just A)
lookup-some (A ∷ Φ) zero    _ = A , refl
lookup-some (A ∷ Φ) (suc j) p = lookup-some Φ j p

<-trans′ : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans′ zero    (suc b) (suc c) _ _ = tt
<-trans′ (suc a) (suc b) (suc c) p q = <-trans′ a b c p q

<-suc : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
<-suc zero    b       _ = tt
<-suc (suc a) (suc b) p = <-suc a b p

<-irr : ∀ a b → T (a <ℕ b) → T (b <ℕ suc a) → ⊥
<-irr zero    zero    () _
<-irr zero    (suc b) _ q = lt0 b q
  where
  lt0 : ∀ b → T (b <ℕ 0) → ⊥
  lt0 b ()
<-irr (suc a) (suc b) p q = <-irr a b p q

-- j < suc j' and not j < j' means j ≡ j'.
<-split : ∀ l j → T (l <ℕ suc j) → (T (l <ℕ j) → ⊥) → l ≡ j
<-split zero    zero    _ _ = refl
<-split zero    (suc j) _ n = ⊥-elim (n tt)
<-split (suc l) zero    p _ = ⊥-elim (lt0 l p)
  where
  lt0 : ∀ b → T (b <ℕ 0) → ⊥
  lt0 b ()
<-split (suc l) (suc j) p n = cong suc (<-split l j p n)

------------------------------------------------------------------------
-- Least: the sweep stays inside every closed superset.

module _ (Φ : Ctx) where

  step : Nat → List Nat → List Nat
  step j S = if elem j S then S ++ varsY (nthY Φ j) else S

  cl-least : ∀ D → Closed Φ D → ∀ j S → T (j <ℕ suc (length Φ)) →
             (∀ i → In S i → T (i <ℕ length Φ) → In D i) →
             ∀ i → In (closeFrom Φ j S) i → T (i <ℕ length Φ) → In D i
  cl-least D cD zero    S _ h = h
  cl-least D cD (suc j) S jn h = cl-least D cD j (step j S) (<-suc j _ jn) h′
    where
    jlt : T (j <ℕ length Φ)
    jlt = jn
    h′ : ∀ i → In (step j S) i → T (i <ℕ length Φ) → In D i
    h′ i p il with dec (elem j S)
    ... | inr q = h i (subst (λ l → In l i) (F-if (elem j S) q) p) il
    ... | inl q with elem-split i S (varsY (nthY Φ j)) (subst (λ l → In l i) (T-if (elem j S) q) p)
    ...   | inl r = h i r il
    ...   | inr r =
            let (A , eA) = lookup-some Φ j jlt
            in cD j eA (h j q jlt) i (subst (λ B → In (varsY B) i) (nthY-just Φ j eA) r)

------------------------------------------------------------------------
-- Closed: after the sweep, every entry in the set has its dependencies
-- in the set.

  Done : Nat → List Nat → Set
  Done j S = ∀ l {A} → lookup Φ l ≡ just A → (T (l <ℕ j) → ⊥) → In S l → varsY A ⊆ S

  old-mem : Deps↓ Φ → ∀ j S l → T (j <ℕ length Φ) → (T (l <ℕ suc j) → ⊥) →
            In (S ++ varsY (nthY Φ j)) l → In S l
  old-mem dd j S l jl ns p′ with elem-split l S (varsY (nthY Φ j)) p′
  ... | inl r = r
  ... | inr r =
        let (B , eB) = lookup-some Φ j jl
            lb = dd j eB l (subst (λ C → In (varsY C) l) (nthY-just Φ j eB) r)
        in ⊥-elim (ns (<-suc l j lb))

  step-done : Deps↓ Φ → ∀ j S → T (j <ℕ length Φ) → Done (suc j) S → Done j (step j S)
  step-done dd j S jl d l {A} eA nl p with dec (l <ℕ suc j)
  ... | inl ls =
        let lj = <-split l j ls nl in
        go lj
    where
    go : l ≡ j → varsY A ⊆ step j S
    go refl with dec (elem l S)
    ... | inl q = λ i r → subst (λ m → In m i) (sym (T-if (elem l S) q))
                    (elem-++r i S (varsY (nthY Φ l)) (subst (λ B → In (varsY B) i) (sym (nthY-just Φ l eA)) r))
    ... | inr q = ⊥-elim (q (subst (λ m → In m l) (F-if (elem l S) q) p))
  ... | inr ns with dec (elem j S)
  ...   | inr q = λ i r → subst (λ m → In m i) (sym (F-if (elem j S) q))
                    (d l eA ns (subst (λ m → In m l) (F-if (elem j S) q) p) i r)
  ...   | inl q = λ i r → subst (λ m → In m i) (sym (T-if (elem j S) q))
                    (elem-++l i S (varsY (nthY Φ j))
                      (d l eA ns (old-mem dd j S l jl ns (subst (λ m → In m l) (T-if (elem j S) q) p)) i r))

  sweep-done : Deps↓ Φ → ∀ j S → T (j <ℕ suc (length Φ)) → Done j S → Done 0 (closeFrom Φ j S)
  sweep-done dd zero    S _  d = d
  sweep-done dd (suc j) S jn d = sweep-done dd j (step j S) (<-suc j _ jn) (step-done dd j S jn d)

  cl-closed : Deps↓ Φ → ∀ X → Closed Φ (closeFrom Φ (length Φ) X)
  cl-closed dd X j eA p = sweep-done dd (length Φ) X (<-self (length Φ)) d0 j eA (λ ()) p
    where
    <-self : ∀ n → T (n <ℕ suc n)
    <-self zero    = tt
    <-self (suc n) = <-self n
    d0 : Done (length Φ) X
    d0 l eA nl p = ⊥-elim (nl (lookup-below Φ l eA))
