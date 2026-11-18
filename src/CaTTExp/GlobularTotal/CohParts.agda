------------------------------------------------------------------------
-- F2c, small lemmas for the coh case of (1′).
--
--   flat-total  : a compatible diagram flattens (some result exists)
--   lab-of-mem  : a predicate true of every label is a Lab
--   anyLab-elim / anyLab-intro : anyLab is "some label satisfies"
--   fvSub-comp / comp-fvSub    : the variables of σ are those of its components
--   look-out    : out of range, lookupₛ returns the variable itself
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.CohParts where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; merge)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.Labels using (anyL; anyLab; anyCs)
open import CaTTExp.GlobularTotal.NfSub using (Lab; LabL; AllN)
open import CaTTExp.GlobularTotal.FlatBd using (flatG; flatGL; Good; GoodCs; Ok)
open import CaTTExp.GlobularTotal.FvSub using (memL-++)

private
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ∨-split : ∀ a b → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split true  b e = inl refl
  ∨-split false b e = inr e

  ∨-inl : ∀ a b → a ≡ true → (a ∨ b) ≡ true
  ∨-inl true b e = refl

  ∨-inr : ∀ a b → b ≡ true → (a ∨ b) ≡ true
  ∨-inr true  b e = refl
  ∨-inr false b e = e

  ≡-T : ∀ {b} → b ≡ true → T b
  ≡-T refl = tt

  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  ==-self : ∀ x xs → memL x (x ∷ xs) ≡ true
  ==-self x xs rewrite T-≡ (==ℕ-refl x) = refl

------------------------------------------------------------------------

module _ (I : Nat → Maybe LT) where
  mutual
    flat-total : ∀ d P T → Good I d P T → Σ LT λ a → flatG I d T ≡ just a
    flat-total d P (lt []            [])       (_ , ())
    flat-total d P (lt (y ∷ [])      [])       ((ok , _) , _) with ok
    ... | x , ex , _ = x , ex
    flat-total d P (lt (y ∷ y' ∷ ys) [])       (_ , ())
    flat-total d P (lt []            (c ∷ cs)) (_ , ())
    flat-total d P (lt (o ∷ os)      (c ∷ cs)) (_ , g) = flatL-total d o os c cs g

    flatL-total : ∀ d o os c cs → GoodCs I d (o ∷ os) (c ∷ cs) → Σ LT λ a → flatGL I d c cs ≡ just a
    flatL-total d o []               c cs        ()
    flatL-total d o (o' ∷ [])        c []        (gc , _) = flat-total (suc d) _ c gc
    flatL-total d o (o' ∷ o'' ∷ os)  c []        (_ , ())
    flatL-total d o (o' ∷ [])        c (c' ∷ cs) (_ , ())
    flatL-total d o (o' ∷ o'' ∷ os)  c (c' ∷ cs) (gc , gs)
      with flat-total (suc d) _ c gc | flatL-total d o' (o'' ∷ os) c' cs gs
    ... | a , ea | b , eb rewrite ea | eb = merge d a b , refl

------------------------------------------------------------------------

mutual
  lab-of-mem : ∀ (P : Nat → Set) a → (∀ y → mem y a ≡ true → P y) → Lab P a
  lab-of-mem P (lt os cs) h =
    all-of-mem os (λ y m → h y (∨-inl (memL y os) (memCs y cs) m)) ,
    labL-of-mem P cs (λ y m → h y (∨-inr (memL y os) (memCs y cs) m))
    where
    all-of-mem : ∀ xs → (∀ y → memL y xs ≡ true → P y) → AllN P xs
    all-of-mem []       h' = tt
    all-of-mem (x ∷ xs) h' = h' x (==-self x xs) , all-of-mem xs (λ y m → h' y (∨-inr (y ==ℕ x) _ m))

  labL-of-mem : ∀ (P : Nat → Set) cs → (∀ y → memCs y cs ≡ true → P y) → LabL P cs
  labL-of-mem P []       h = tt
  labL-of-mem P (c ∷ cs) h =
    lab-of-mem P c (λ y m → h y (∨-inl (mem y c) (memCs y cs) m)) ,
    labL-of-mem P cs (λ y m → h y (∨-inr (mem y c) (memCs y cs) m))

------------------------------------------------------------------------

anyL-elim : ∀ f xs → anyL f xs ≡ true → Σ Nat λ w → (memL w xs ≡ true) × (f w ≡ true)
anyL-elim f []       ()
anyL-elim f (x ∷ xs) e with ∨-split (f x) (anyL f xs) e
... | inl fx = x , ==-self x xs , fx
... | inr r with anyL-elim f xs r
...   | w , m , fw = w , ∨-inr (w ==ℕ x) _ m , fw

anyL-intro : ∀ f xs w → memL w xs ≡ true → f w ≡ true → anyL f xs ≡ true
anyL-intro f []       w () fw
anyL-intro f (x ∷ xs) w m fw with w ==ℕ x in eq
... | true rewrite ==ℕ-sound w x (≡-T eq) = ∨-inl (f x) _ fw
... | false = ∨-inr (f x) _ (anyL-intro f xs w m fw)

mutual
  anyLab-elim : ∀ f a → anyLab f a ≡ true → Σ Nat λ w → (mem w a ≡ true) × (f w ≡ true)
  anyLab-elim f (lt os cs) e with ∨-split (anyL f os) (anyCs f cs) e
  ... | inl l with anyL-elim f os l
  ...   | w , m , fw = w , ∨-inl (memL w os) _ m , fw
  anyLab-elim f (lt os cs) e | inr r with anyCs-elim f cs r
  ...   | w , m , fw = w , ∨-inr (memL w os) _ m , fw

  anyCs-elim : ∀ f cs → anyCs f cs ≡ true → Σ Nat λ w → (memCs w cs ≡ true) × (f w ≡ true)
  anyCs-elim f []       ()
  anyCs-elim f (c ∷ cs) e with ∨-split (anyLab f c) (anyCs f cs) e
  ... | inl l with anyLab-elim f c l
  ...   | w , m , fw = w , ∨-inl (mem w c) _ m , fw
  anyCs-elim f (c ∷ cs) e | inr r with anyCs-elim f cs r
  ...   | w , m , fw = w , ∨-inr (mem w c) _ m , fw

mutual
  anyLab-intro : ∀ f a w → mem w a ≡ true → f w ≡ true → anyLab f a ≡ true
  anyLab-intro f (lt os cs) w m fw with ∨-split (memL w os) (memCs w cs) m
  ... | inl mo = ∨-inl (anyL f os) _ (anyL-intro f os w mo fw)
  ... | inr mc = ∨-inr (anyL f os) _ (anyCs-intro f cs w mc fw)

  anyCs-intro : ∀ f cs w → memCs w cs ≡ true → f w ≡ true → anyCs f cs ≡ true
  anyCs-intro f []       w () fw
  anyCs-intro f (c ∷ cs) w m fw with ∨-split (mem w c) (memCs w cs) m
  ... | inl mc = ∨-inl (anyLab f c) _ (anyLab-intro f c w mc fw)
  ... | inr ms = ∨-inr (anyLab f c) _ (anyCs-intro f cs w ms fw)

------------------------------------------------------------------------

private
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

  lt-ne : ∀ y n → T (y <ℕ suc n) → (y ==ℕ n) ≡ false → T (y <ℕ n)
  lt-ne zero    zero    p ()
  lt-ne zero    (suc n) p e = tt
  lt-ne (suc y) zero    () e
  lt-ne (suc y) (suc n) p e = lt-ne y n p e

fvSub-comp : ∀ σ z → memL z (fvSub σ) ≡ true →
             Σ Nat λ w → T (w <ℕ lenₛ σ) × (memL z (fvTm (lookupₛ σ w)) ≡ true)
fvSub-comp ⟨⟩       z ()
fvSub-comp (σ ,ₛ t) z m with ∨-split (memL z (fvSub σ)) (memL z (fvTm t)) (trans (sym (memL-++ z (fvSub σ) (fvTm t))) m)
... | inr mt = lenₛ σ , <-suc (lenₛ σ) , subst (λ b → memL z (fvTm (if b then t else lookupₛ σ (lenₛ σ))) ≡ true)
                                          (sym (T-≡ (==ℕ-refl (lenₛ σ)))) mt
... | inl ms with fvSub-comp σ z ms
...   | w , p , mw = w , <-weak w (lenₛ σ) p ,
        subst (λ b → memL z (fvTm (if b then t else lookupₛ σ w)) ≡ true) (sym (<-ne w (lenₛ σ) p)) mw

comp-fvSub : ∀ σ z w → T (w <ℕ lenₛ σ) → memL z (fvTm (lookupₛ σ w)) ≡ true → memL z (fvSub σ) ≡ true
comp-fvSub ⟨⟩       z w () m
comp-fvSub (σ ,ₛ t) z w p m with w ==ℕ lenₛ σ in eq
... | true  = trans (memL-++ z (fvSub σ) (fvTm t)) (∨-inr (memL z (fvSub σ)) _ m)
... | false = trans (memL-++ z (fvSub σ) (fvTm t))
                (∨-inl (memL z (fvSub σ)) _ (comp-fvSub σ z w (lt-ne w (lenₛ σ) p eq) m))

look-out : ∀ σ y → (y <ℕ lenₛ σ) ≡ false → lookupₛ σ y ≡ var y
look-out ⟨⟩       y _ = refl
look-out (σ ,ₛ t) y p with y ==ℕ lenₛ σ in eq
... | true rewrite ==ℕ-sound y (lenₛ σ) (≡-T eq) = ⊥-elim (absurd (lenₛ σ) p)
  where
  absurd : ∀ n → (n <ℕ suc n) ≡ false → ⊥
  absurd zero    ()
  absurd (suc n) e = absurd n e
... | false = look-out σ y (weaken y (lenₛ σ) p)
  where
  weaken : ∀ y n → (y <ℕ suc n) ≡ false → (y <ℕ n) ≡ false
  weaken zero    zero    ()
  weaken zero    (suc n) ()
  weaken (suc y) zero    e = refl
  weaken (suc y) (suc n) e = weaken y n e

-- In scope, a variable has a type.
lt-lookup : ∀ Γ y → T (y <ℕ len Γ) → Σ Ty λ A → lookup Γ y ≡ just A
lt-lookup ε       y ()
lt-lookup (Γ ▸ C) y p with y ==ℕ len Γ in eq
... | true  = C , refl
... | false = lt-lookup Γ y (lt-ne y (len Γ) p eq)
