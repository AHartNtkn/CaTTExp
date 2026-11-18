------------------------------------------------------------------------
-- F2c: the labelled tree of a pasting context is a diagram of it.
--
--   lab-ex : ∀ τ → Ex (ctxOf τ) 0 nothing (idTree τ)
--
-- by following PastingTrees.build and GlobularFiller.labT in step:
-- both number a branch's target y and cell f as the next two
-- variables, and the context only grows (`Ext`), so the types read
-- off earlier stay valid.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LabEx where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; labT; labCs; idTree)
open import CaTTExp.GlobularTotal.Uniq
open import CaTTExp.GlobularTotal.PsOrd using (TyIn; inv)

private
  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  <-ne : ∀ a b → T (a <ℕ b) → (a ==ℕ b) ≡ false
  <-ne zero    zero    ()
  <-ne zero    (suc b) p = refl
  <-ne (suc a) zero    ()
  <-ne (suc a) (suc b) p = <-ne a b p

  ==-sound : ∀ a b → (a ==ℕ b) ≡ true → a ≡ b
  ==-sound a b e = ==ℕ-sound a b (≡-T e)

  lookup-lt : ∀ Γ y A → lookup Γ y ≡ just A → T (y <ℕ len Γ)
  lookup-lt ε       y A ()
  lookup-lt (Γ ▸ C) y A e with y ==ℕ len Γ in eq
  ... | true rewrite ==-sound y (len Γ) eq = <-suc (len Γ)
  ... | false = <-weak y (len Γ) (lookup-lt Γ y A e)

  lookup-top : ∀ Γ C → lookup (Γ ▸ C) (len Γ) ≡ just C
  lookup-top Γ C rewrite T-≡ (==ℕ-refl (len Γ)) = refl

------------------------------------------------------------------------
-- Context extension.

Ext : Ctx → Ctx → Set
Ext Γ Γ' = ∀ y A → lookup Γ y ≡ just A → lookup Γ' y ≡ just A

private
  ext-refl : ∀ Γ → Ext Γ Γ
  ext-refl Γ y A e = e

  ext-trans : ∀ Γ₁ Γ₂ Γ₃ → Ext Γ₁ Γ₂ → Ext Γ₂ Γ₃ → Ext Γ₁ Γ₃
  ext-trans _ _ _ f g y A e = g y A (f y A e)

  ext-snoc : ∀ Γ C → Ext Γ (Γ ▸ C)
  ext-snoc Γ C y A e rewrite <-ne y (len Γ) (lookup-lt Γ y A e) = e

  dimOf-just : ∀ Γ y A → lookup Γ y ≡ just A → dimOf Γ y ≡ dim A
  dimOf-just Γ y A e with lookup Γ y
  dimOf-just Γ y A refl | .(just A) = refl

parOf : Ty → Maybe (Nat × Nat)
parOf (arr B (var p) (var q)) = just (p , q)
parOf _                       = nothing

private
  cell-weak : ∀ Γ Γ' e par o → Ext Γ Γ' → Cell Γ e par o → Cell Γ' e par o
  cell-weak Γ Γ' e nothing o x ((A , eA) , d) =
    (A , x o A eA) , trans (dimOf-just Γ' o A (x o A eA)) (trans (sym (dimOf-just Γ o A eA)) d)
  cell-weak Γ Γ' e (just (p , q)) o x ((B , eB) , d) =
    (B , x o _ eB) , trans (dimOf-just Γ' o _ (x o _ eB)) (trans (sym (dimOf-just Γ o _ eB)) d)

  all-weak : ∀ Γ Γ' e par os → Ext Γ Γ' → AllN (Cell Γ e par) os → AllN (Cell Γ' e par) os
  all-weak Γ Γ' e par []       x _        = tt
  all-weak Γ Γ' e par (o ∷ os) x (c , cs) = cell-weak Γ Γ' e par o x c , all-weak Γ Γ' e par os x cs

mutual
  ex-weak : ∀ Γ Γ' e par a → Ext Γ Γ' → Ex Γ e par a → Ex Γ' e par a
  ex-weak Γ Γ' e par (lt os cs) x (oks , xs) = all-weak Γ Γ' e par os x oks , exCs-weak Γ Γ' e os cs x xs

  exCs-weak : ∀ Γ Γ' e os cs → Ext Γ Γ' → ExCs Γ e os cs → ExCs Γ' e os cs
  exCs-weak Γ Γ' e []            cs       x ()
  exCs-weak Γ Γ' e (o ∷ [])      []       x _ = tt
  exCs-weak Γ Γ' e (o ∷ [])      (c ∷ cs) x ()
  exCs-weak Γ Γ' e (o ∷ o' ∷ os) []       x ()
  exCs-weak Γ Γ' e (o ∷ o' ∷ os) (c ∷ cs) x (xc , xs) =
    ex-weak Γ Γ' (suc e) _ c x xc , exCs-weak Γ Γ' e (o' ∷ os) cs x xs

private
  cellOf : ∀ Γ Δ o A → lookup Γ o ≡ just A → TyIn Δ A → Cell Γ (dim A) (parOf A) o
  cellOf Γ Δ o ⋆                       e _ = (⋆ , e) , dimOf-just Γ o ⋆ e
  cellOf Γ Δ o (arr B (var p) (var q)) e _ = (B , e) , dimOf-just Γ o _ e
  cellOf Γ Δ o (arr B (var p) (coh _ _ _)) e ()
  cellOf Γ Δ o (arr B (var p) (cst ()))    e _
  cellOf Γ Δ o (arr B (coh _ _ _) _)       e ()
  cellOf Γ Δ o (arr B (cst ()) _)          e _

------------------------------------------------------------------------
-- build and labT in step.

mutual
  B : ∀ t {Γ x A} (d : Γ ⊢ps x ∶ A) →
      (snd (labT t x (len Γ)) ≡ len (fst (build t d)))
    × Ext Γ (fst (build t d))
    × Ex (fst (build t d)) (dim A) (parOf A) (fst (labT t x (len Γ)))
  B (node ts) {Γ} {x} {A} d with labCs ts (len Γ) | BL ts d
  ... | os , ls , n' | e , ext , cells , exs with inv d
  ...   | _ , ex , tA , _ =
    e , ext , (cell-weak Γ _ (dim A) (parOf A) x ext (cellOf Γ Γ x A ex tA) , cells) , exs

  BL : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) →
       (snd (snd (labCs ts (len Γ))) ≡ len (fst (buildList ts d)))
     × Ext Γ (fst (buildList ts d))
     × AllN (Cell (fst (buildList ts d)) (dim A) (parOf A)) (fst (labCs ts (len Γ)))
     × ExCs (fst (buildList ts d)) (dim A) (x ∷ fst (labCs ts (len Γ))) (fst (snd (labCs ts (len Γ))))
  BL [] {Γ} d = refl , ext-refl Γ , tt , tt
  BL (t ∷ ts) {Γ} {x} {A} d
    with build t (pse d) | labT t (suc (len Γ)) (suc (suc (len Γ))) | B t (pse d)
  ... | Γ₂ , x₂ , d₂ | l , .(len Γ₂) | refl , ext₁ , ex₁
    with labCs ts (len Γ₂) | BL ts (psd d₂)
  ...   | os , ls , n₂ | e₂ , ext₂ , cells₂ , exs₂ with inv d
  ...     | _ , _ , tA , _ =
    e₂ , ext , (cellY , cells₂) , (ex-weak Γ₂ Γ' (suc (dim A)) _ l ext₂ ex₁ , exs₂)
    where
    Γ' : Ctx
    Γ' = fst (buildList ts (psd d₂))

    Γ₁ : Ctx
    Γ₁ = Γ ▸ A ▸ arr A (var x) (var (len Γ))

    ext₀ : Ext Γ Γ₁
    ext₀ = ext-trans Γ (Γ ▸ A) Γ₁ (ext-snoc Γ A) (ext-snoc (Γ ▸ A) _)

    ext : Ext Γ Γ'
    ext = ext-trans Γ Γ₁ Γ' ext₀ (ext-trans Γ₁ Γ₂ Γ' ext₁ ext₂)

    cellY : Cell Γ' (dim A) (parOf A) (len Γ)
    cellY = cellOf Γ' Γ (len Γ) A
              (ext₂ (len Γ) A (ext₁ (len Γ) A (ext-snoc (Γ ▸ A) _ (len Γ) A (lookup-top Γ A))))
              tA

lab-ex : ∀ τ → Ex (ctxOf τ) 0 nothing (idTree τ)
lab-ex τ with build τ pss | B τ pss
... | Γ , _ , d | _ , _ , ex = ex
