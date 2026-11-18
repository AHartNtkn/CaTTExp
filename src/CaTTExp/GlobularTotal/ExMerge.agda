------------------------------------------------------------------------
-- F2c toward (1′): composites of diagrams are diagrams.
--
--   ex-merge : Ex Γ e par a → Ex Γ e par b → Compat k a b → Ex Γ e par (merge k a b)
--   ex-flat  : Good I d P T → (images of I are diagrams) → flatG I d T ≡ just a → Ex Γ 0 nothing a
--
-- so in the coh case of (1′) the normal form, a composite of the
-- arguments' normal forms, is a diagram of Γ.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.ExMerge where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; merge; mergeL; bd; bdL; module Lists)
open Lists using (headN; lastN; drop)
open import CaTTExp.GlobularTotal.TreeAlg using (WF; WFs; Compat)
open import CaTTExp.GlobularTotal.Uniq using (AllN; Cell; Ex; ExCs)

private
  lt-injₒ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → os ≡ os'
  lt-injₒ refl = refl

  lt-injₛ : ∀ {os os' cs cs'} → lt os cs ≡ lt os' cs' → cs ≡ cs'
  lt-injₛ refl = refl

  ∷-injₕ : ∀ {x y : Nat} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-injₕ refl = refl

  ∷-injₜ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-injₜ refl = refl

module _ (Γ : Ctx) where

  private
    all-++ : ∀ P xs ys → AllN P xs → AllN P ys → AllN P (xs ++ ys)
    all-++ P []       ys _        q = q
    all-++ P (x ∷ xs) ys (p , pp) q = p , all-++ P xs ys pp q

    all-drop1 : ∀ P xs → AllN P xs → AllN P (drop 1 xs)
    all-drop1 P []       _       = tt
    all-drop1 P (x ∷ xs) (_ , q) = q

    exCs-++ : ∀ e os cs os' cs' → ExCs Γ e os cs → ExCs Γ e os' cs' → lastN os ≡ headN os' →
              ExCs Γ e (os ++ drop 1 os') (cs ++ cs')
    exCs-++ e []            cs       os'          cs' () _ _
    exCs-++ e (o ∷ [])      []       []           cs' _ () _
    exCs-++ e (o ∷ [])      []       (o'' ∷ rest) cs' _ x refl = x
    exCs-++ e (o ∷ [])      (c ∷ cs) os'          cs' () _ _
    exCs-++ e (o ∷ o' ∷ os) []       os'          cs' () _ _
    exCs-++ e (o ∷ o' ∷ os) (c ∷ cs) os'          cs' (xc , xs) x h =
      xc , exCs-++ e (o' ∷ os) cs os' cs' xs x h

  mutual
    ex-merge : ∀ e par k a b → Ex Γ e par a → Ex Γ e par b → Compat k a b → Ex Γ e par (merge k a b)
    ex-merge e par zero (lt os cs) (lt os' cs') (ao , ac) (bo , bc) cp =
      all-++ _ os (drop 1 os') ao (all-drop1 _ os' bo) ,
      exCs-++ e os cs os' cs' ac bc (∷-injₕ (lt-injₒ cp))
    ex-merge e par (suc k) (lt os cs) (lt os' cs') (ao , ac) (bo , bc) cp
      with lt-injₒ cp
    ... | refl = ao , exCs-merge e k os cs cs' ac bc (lt-injₛ cp)

    exCs-merge : ∀ e k os cs cs' → ExCs Γ e os cs → ExCs Γ e os cs' → bdL true k cs ≡ bdL false k cs' →
                 ExCs Γ e os (mergeL k cs cs')
    exCs-merge e k []            cs       cs'        () _ _
    exCs-merge e k (o ∷ [])      []       []         _ _ _ = tt
    exCs-merge e k (o ∷ [])      []       (c' ∷ cs') _ () _
    exCs-merge e k (o ∷ [])      (c ∷ cs) cs'        () _ _
    exCs-merge e k (o ∷ o' ∷ os) []       cs'        () _ _
    exCs-merge e k (o ∷ o' ∷ os) (c ∷ cs) []         _ () _
    exCs-merge e k (o ∷ o' ∷ os) (c ∷ cs) (c' ∷ cs') (xc , xs) (yc , ys) h =
      ex-merge (suc e) (just (o , o')) k c c' xc yc (∷-injₕ' h) ,
      exCs-merge e k (o' ∷ os) cs cs' xs ys (∷-injₜ h)
      where
      ∷-injₕ' : ∀ {x y : LT} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
      ∷-injₕ' refl = refl

------------------------------------------------------------------------
-- Flattening a compatible diagram whose images are diagrams.

open import CaTTExp.GlobularTotal.FlatBd
  using (flatG; flatGL; Good; GoodCs; Par; flat-bd; flatL-bd; flat-ends)

private
  bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
             (m >>= f) ≡ just b → Σ A λ a → (m ≡ just a) × (f a ≡ just b)
  bind-inv (just a) f e = a , refl , e
  bind-inv nothing  f ()

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

module _ (Γ : Ctx) (I : Nat → Maybe LT) (exI : ∀ y x → I y ≡ just x → Ex Γ 0 nothing x) where

  mutual
    ex-flat : ∀ d P T a → Good I d P T → flatG I d T ≡ just a → Ex Γ 0 nothing a
    ex-flat d P (lt (y ∷ []) [])     a g e = exI y a e
    ex-flat d P (lt [] [])           a (_ , ()) e
    ex-flat d P (lt (y ∷ y' ∷ ys) []) a (_ , ()) e
    ex-flat d P (lt [] (c ∷ cs))     a (_ , ()) e
    ex-flat d P (lt (o ∷ os) (c ∷ cs)) a (_ , g) e = ex-flatL d o os c cs a g e

    ex-flatL : ∀ d o os c cs a → GoodCs I d (o ∷ os) (c ∷ cs) → flatGL I d c cs ≡ just a →
               Ex Γ 0 nothing a
    ex-flatL d o []               c cs        a () e
    ex-flatL d o (o' ∷ [])        c []        a (gc , _) e = ex-flat (suc d) _ c a gc e
    ex-flatL d o (o' ∷ o'' ∷ os)  c []        a (_ , ()) e
    ex-flatL d o (o' ∷ [])        c (c' ∷ cs) a (_ , ()) e
    ex-flatL d o (o' ∷ o'' ∷ os)  c (c' ∷ cs) a (gc , gs) e
      with bind-inv (flatG I (suc d) c) _ e
    ... | a₁ , e₁ , e'
      with bind-inv (flatGL I d c' cs) _ e'
    ... | b , e₂ , refl
      with flat-ends I d o o' c a₁ gc e₁ | flatL-bd I d o' (o'' ∷ os) c' cs b gs e₂
    ... | eo , eo' | _ , _ , ebo , _ =
      ex-merge Γ 0 nothing d a₁ b
        (ex-flat (suc d) _ c a₁ gc e₁) (ex-flatL d o' (o'' ∷ os) c' cs b gs e₂)
        (just-inj (trans (sym eo') ebo))
