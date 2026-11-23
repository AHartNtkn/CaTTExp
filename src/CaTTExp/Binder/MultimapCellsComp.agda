------------------------------------------------------------------------
-- Composing substitutions on the variables and atoms a term uses
-- (ledger S26j, step 2b), and the atoms of a renamed term.
------------------------------------------------------------------------
module CaTTExp.Binder.MultimapCellsComp where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing hiding (canon)
open import CaTTExp.Gray.Biclosed.Strengthen
open import CaTTExp.Binder.MultimapCells
open import CaTTExp.Binder.MultimapCellsStrengthen using (T-if; F-if; dec; inl; inr)
open import CaTTExp.Binder.MultimapCellsSupport using (In; _⊆_)
open import CaTTExp.Binder.MultimapCellsRen using (⊆-l; ⊆-r; map-++)

------------------------------------------------------------------------
-- σ then τ agrees with υ on the atoms and variables of a term.

cong₃′ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
         a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃′ f refl refl refl = refl

module _ (σ τ υ : Sub) where

  OnA : List Nat → Set
  OnA xs = ∀ a → In xs a → sF (fo τ) (fo σ a) ≡ fo υ a

  OnV : List Nat → Set
  OnV xs = ∀ i → In xs i → sT τ (tm σ i) ≡ tm υ i

  onA-l : ∀ xs ys → OnA (xs ++ ys) → OnA xs
  onA-l xs ys h a p = h a (elem-++l a xs ys p)
  onA-r : ∀ xs ys → OnA (xs ++ ys) → OnA ys
  onA-r xs ys h a p = h a (elem-++r a xs ys p)
  onV-l : ∀ xs ys → OnV (xs ++ ys) → OnV xs
  onV-l xs ys h a p = h a (elem-++l a xs ys p)
  onV-r : ∀ xs ys → OnV (xs ++ ys) → OnV ys
  onV-r xs ys h a p = h a (elem-++r a xs ys p)

  compF : ∀ x → OnA (atF x) → sF (fo τ) (sF (fo σ) x) ≡ sF (fo υ) x
  compF (obj i)  h = h i (∨-l (i ==ℕ i) _ (==ℕ-refl i))
  compF (rep _)  h = refl
  compF (shp _)  h = refl
  compF (x ⊗ y)  h = cong₂ _⊗_  (compF x (onA-l (atF x) (atF y) h)) (compF y (onA-r (atF x) (atF y) h))
  compF (x \\ y) h = cong₂ _\\_ (compF x (onA-l (atF x) (atF y) h)) (compF y (onA-r (atF x) (atF y) h))
  compF (x // y) h = cong₂ _//_ (compF x (onA-l (atF x) (atF y) h)) (compF y (onA-r (atF x) (atF y) h))

  compFs : ∀ xs → OnA (atFs xs) → sFs (fo τ) (sFs (fo σ) xs) ≡ sFs (fo υ) xs
  compFs []       h = refl
  compFs (x ∷ xs) h = cong₂ _∷_ (compF x (onA-l (atF x) (atFs xs) h)) (compFs xs (onA-r (atF x) (atFs xs) h))

  mutual
    compT : ∀ t → OnA (atT t) → OnV (varsT t) → sT τ (sT σ t) ≡ sT υ t
    compT (var i)  ha hv = hv i (∨-l (i ==ℕ i) _ (==ℕ-refl i))
    compT (mP U V) ha hv = cong₂ mP (compF U (onA-l (atF U) (atF V) ha)) (compF V (onA-r (atF U) (atF V) ha))
    compT (eL A C) ha hv = cong₂ eL (compF A (onA-l (atF A) (atF C) ha)) (compF C (onA-r (atF A) (atF C) ha))
    compT (eR A C) ha hv = cong₂ eR (compF A (onA-l (atF A) (atF C) ha)) (compF C (onA-r (atF A) (atF C) ha))
    compT (pP Δ Θ) ha hv = refl
    compT pt       ha hv = refl
    compT (iP Θ)   ha hv = refl
    compT (idt A)  ha hv = cong idt (compF A ha)
    compT (comp f gs) ha hv =
      cong₂ comp (compT f (onA-l (atT f) (atTs gs) ha) (onV-l (varsT f) (varsTs gs) hv))
                 (compTs gs (onA-r (atT f) (atTs gs) ha) (onV-r (varsT f) (varsTs gs) hv))
    compT (glue a x b) ha hv =
      let ha₂ = onA-r (atT a) (atT x ++ atT b) ha
          hv₂ = onV-r (varsT a) (varsT x ++ varsT b) hv
      in cong₃′ glue (compT a (onA-l (atT a) (atT x ++ atT b) ha) (onV-l (varsT a) (varsT x ++ varsT b) hv))
                     (compT x (onA-l (atT x) (atT b) ha₂) (onV-l (varsT x) (varsT b) hv₂))
                     (compT b (onA-r (atT x) (atT b) ha₂) (onV-r (varsT x) (varsT b) hv₂))
    compT (here t e φs ts) ha hv =
      cong₂ (here t e) (compFs φs (onA-l (atFs φs) (atTs ts) ha)) (compTs ts (onA-r (atFs φs) (atTs ts) ha) hv)

    compTs : ∀ ts → OnA (atTs ts) → OnV (varsTs ts) → sTs τ (sTs σ ts) ≡ sTs υ ts
    compTs []       ha hv = refl
    compTs (t ∷ ts) ha hv =
      cong₂ _∷_ (compT t (onA-l (atT t) (atTs ts) ha) (onV-l (varsT t) (varsTs ts) hv))
                (compTs ts (onA-r (atT t) (atTs ts) ha) (onV-r (varsT t) (varsTs ts) hv))

  compM : ∀ M → OnA (atY (op M)) → sM (fo τ) (sM (fo σ) M) ≡ sM (fo υ) M
  compM (xs ▸ z) h = cong₂ _▸_ (compFs xs (onA-l (atFs xs) (atF z) h)) (compF z (onA-r (atFs xs) (atF z) h))

  compY : ∀ A → OnA (atY A) → OnV (varsY A) → sY τ (sY σ A) ≡ sY υ A
  compY (op M) ha hv = cong op (compM M ha)
  compY (hom m g A s t) ha hv =
    let ha₂ = onA-r (atY A) (atT s ++ atT t) ha
        hv₂ = onV-r (varsY A) (varsT s ++ varsT t) hv
    in cong₃′ (hom m g) (compY A (onA-l (atY A) (atT s ++ atT t) ha) (onV-l (varsY A) (varsT s ++ varsT t) hv))
                        (compT s (onA-l (atT s) (atT t) ha₂) (onV-l (varsT s) (varsT t) hv₂))
                        (compT t (onA-r (atT s) (atT t) ha₂) (onV-r (varsT s) (varsT t) hv₂))

------------------------------------------------------------------------
-- Atoms of a renamed term.

module AtRen (as vs : List Nat) where
  private ρ = renOf as vs
  ra : Nat → Nat
  ra i = idx i as

  atF-ren : ∀ x → atF (sF (fo ρ) x) ≡ map ra (atF x)
  atF-ren (obj i)  = refl
  atF-ren (rep _)  = refl
  atF-ren (shp _)  = refl
  atF-ren (x ⊗ y)  = trans (cong₂ _++_ (atF-ren x) (atF-ren y)) (sym (map-++ ra (atF x) (atF y)))
  atF-ren (x \\ y) = trans (cong₂ _++_ (atF-ren x) (atF-ren y)) (sym (map-++ ra (atF x) (atF y)))
  atF-ren (x // y) = trans (cong₂ _++_ (atF-ren x) (atF-ren y)) (sym (map-++ ra (atF x) (atF y)))

  atFs-ren : ∀ xs → atFs (sFs (fo ρ) xs) ≡ map ra (atFs xs)
  atFs-ren []       = refl
  atFs-ren (x ∷ xs) = trans (cong₂ _++_ (atF-ren x) (atFs-ren xs)) (sym (map-++ ra (atF x) (atFs xs)))

  mutual
    atT-ren : ∀ t → atT (sT ρ t) ≡ map ra (atT t)
    atT-ren (var i) with elem i vs
    ... | true  = refl
    ... | false = refl
    atT-ren (mP U V) = trans (cong₂ _++_ (atF-ren U) (atF-ren V)) (sym (map-++ ra (atF U) (atF V)))
    atT-ren (eL A C) = trans (cong₂ _++_ (atF-ren A) (atF-ren C)) (sym (map-++ ra (atF A) (atF C)))
    atT-ren (eR A C) = trans (cong₂ _++_ (atF-ren A) (atF-ren C)) (sym (map-++ ra (atF A) (atF C)))
    atT-ren (pP _ _) = refl
    atT-ren pt       = refl
    atT-ren (iP _)   = refl
    atT-ren (idt A)  = atF-ren A
    atT-ren (comp f gs) = trans (cong₂ _++_ (atT-ren f) (atTs-ren gs)) (sym (map-++ ra (atT f) (atTs gs)))
    atT-ren (glue a x b) =
      trans (cong₂ _++_ (atT-ren a) (trans (cong₂ _++_ (atT-ren x) (atT-ren b)) (sym (map-++ ra (atT x) (atT b)))))
            (sym (map-++ ra (atT a) (atT x ++ atT b)))
    atT-ren (here t e φs ts) = trans (cong₂ _++_ (atFs-ren φs) (atTs-ren ts)) (sym (map-++ ra (atFs φs) (atTs ts)))

    atTs-ren : ∀ ts → atTs (sTs ρ ts) ≡ map ra (atTs ts)
    atTs-ren []       = refl
    atTs-ren (t ∷ ts) = trans (cong₂ _++_ (atT-ren t) (atTs-ren ts)) (sym (map-++ ra (atT t) (atTs ts)))

  atY-ren : ∀ A → atY (sY ρ A) ≡ map ra (atY A)
  atY-ren (op (xs ▸ z)) = trans (cong₂ _++_ (atFs-ren xs) (atF-ren z)) (sym (map-++ ra (atFs xs) (atF z)))
  atY-ren (hom m g A s t) =
    trans (cong₂ _++_ (atY-ren A) (trans (cong₂ _++_ (atT-ren s) (atT-ren t)) (sym (map-++ ra (atT s) (atT t)))))
          (sym (map-++ ra (atY A) (atT s ++ atT t)))

  concatAt-ren : ∀ As → concatAt (map (sY ρ) As) ≡ map ra (concatAt As)
  concatAt-ren []       = refl
  concatAt-ren (A ∷ As) = trans (cong₂ _++_ (atY-ren A) (concatAt-ren As)) (sym (map-++ ra (atY A) (concatAt As)))
