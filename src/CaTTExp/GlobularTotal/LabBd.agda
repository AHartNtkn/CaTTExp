------------------------------------------------------------------------
-- F2c toward (1′), L3: the boundaries of the labelled tree of a
-- pasting context carry exactly the variables of its boundaries.
--
--   lab-src : mem y (bd false k (idTree τ)) ≡ memL y (srcVars k (ctxOf τ))
--
-- so with k = dim Θ − 1 the labels of the source of idTree τ are ∂⁻Θ.
-- The proof follows PastingTrees.build and GlobularFiller.labCs in
-- step, as LabEx does: each child adds the pair (y , f), which
-- srcVars keeps exactly when bd keeps y in the parent and f as the
-- root of the child.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.LabBd where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; labT; labCs; idTree; bd; bdL; module Lists)
open Lists using (lastN)
open import CaTTExp.GlobularTotal.Uniq using (mem; memCs; memL)
open import CaTTExp.GlobularTotal.LabEx using (BL)

private
  T-≡ : ∀ {b} → T b → b ≡ true
  T-≡ {true} _ = refl

  +-suc : ∀ a b → a + suc b ≡ suc (a + b)
  +-suc zero    b = refl
  +-suc (suc a) b = cong suc (+-suc a b)

  +-one : ∀ a → a + 1 ≡ suc a
  +-one a = +-suc a 0 ∙ cong suc (+-zero a)
    where
    _∙_ : ∀ {x y z : Nat} → x ≡ y → y ≡ z → x ≡ z
    _∙_ = trans
    +-zero : ∀ a → a + 0 ≡ a
    +-zero zero    = refl
    +-zero (suc a) = cong suc (+-zero a)

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-weak : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-weak zero    b       p = tt
  <-weak (suc a) zero    ()
  <-weak (suc a) (suc b) p = <-weak a b p

  high : ∀ e k → ((e + suc k) <ℕ suc e) ≡ false
  high zero    k = refl
  high (suc e) k = high e k

  memL-snoc : ∀ y xs a → memL y (snoc xs a) ≡ (memL y xs ∨ ((y ==ℕ a) ∨ false))
  memL-snoc y []       a = refl
  memL-snoc y (x ∷ xs) a with y ==ℕ x
  ... | true  = refl
  ... | false = memL-snoc y xs a

  step-low : ∀ i Γ A B → T (i <ℕ suc (dim A)) → srcVars i (Γ ▸ A ▸ B) ≡ srcVars i Γ
  step-low i Γ A B h rewrite T-≡ h = refl

  step-high : ∀ i Γ A B → (i <ℕ suc (dim A)) ≡ false →
              srcVars i (Γ ▸ A ▸ B) ≡ snoc (snoc (srcVars i Γ) (len Γ)) (suc (len Γ))
  step-high i Γ A B h rewrite h = refl

  ∨-false : ∀ a → a ≡ (a ∨ (false ∨ false))
  ∨-false true  = refl
  ∨-false false = refl

  ∨-false′ : ∀ a → a ≡ (a ∨ false)
  ∨-false′ true  = refl
  ∨-false′ false = refl

  lt-one : ∀ e → T ((e + 1) <ℕ suc (suc e))
  lt-one zero    = tt
  lt-one (suc e) = lt-one e

  shuffle2 : ∀ S a b N o r →
    ((((S ∨ (a ∨ false)) ∨ (b ∨ false)) ∨ N) ∨ (o ∨ r)) ≡ (S ∨ ((a ∨ o) ∨ ((b ∨ N) ∨ r)))
  shuffle2 true  a     b     N     o     r = refl
  shuffle2 false true  b     N     o     r = refl
  shuffle2 false false true  N     o     r with o
  ... | true  = refl
  ... | false = refl
  shuffle2 false false false true  o     r with o
  ... | true  = refl
  ... | false = refl
  shuffle2 false false false false o     r = refl

  -- The boolean bookkeeping of one child.
  shuffle : ∀ S a b c d o r →
    ((((S ∨ a) ∨ b) ∨ (c ∨ d)) ∨ (o ∨ r)) ≡ (S ∨ ((a ∨ o) ∨ ((((b ∨ c) ∨ d)) ∨ r)))
  shuffle S a b c d o r = go S a o b c d r
    where
    go : ∀ S a o b c d r →
      ((((S ∨ a) ∨ b) ∨ (c ∨ d)) ∨ (o ∨ r)) ≡ (S ∨ ((a ∨ o) ∨ ((((b ∨ c) ∨ d)) ∨ r)))
    go true  a     o     b     c     d     r = refl
    go false true  o     b     c     d     r = refl
    go false false true  true  c     d     r = refl
    go false false true  false true  d     r = refl
    go false false true  false false true  r = refl
    go false false true  false false false r = refl
    go false false false true  c     d     r = refl
    go false false false false true  d     r = refl
    go false false false false false true  r = refl
    go false false false false false false r = refl

------------------------------------------------------------------------
-- Below the dimension of the current cell, a subtree adds nothing to
-- the source.

low : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) i → T (i <ℕ suc (dim A)) →
      srcVars i (fst (buildList ts d)) ≡ srcVars i Γ
low []       d i h = refl
low (t ∷ ts) {Γ} {x} {A} d i h with build t (pse d) | low′ t (pse d) i (<-weak i (suc (dim A)) h)
  where
  low′ : ∀ t {Γ x A} (d : Γ ⊢ps x ∶ A) i → T (i <ℕ suc (dim A)) →
         srcVars i (fst (build t d)) ≡ srcVars i Γ
  low′ (node ts) d i h = low ts d i h
... | Γ₂ , _ , d₂ | e₂ =
  trans (low ts (psd d₂) i h) (trans e₂ (step-low i Γ A (arr A (var x) (var (len Γ))) h))

------------------------------------------------------------------------
-- Above it, each child adds y to the parent's objects and f as the
-- root of the child.

-- The labels a subtree adds to the source at bd index k, besides its root.
newc : Nat → List Nat → List LT → Nat → Bool
newc zero    os ls y = false
newc (suc k) os ls y = memL y os ∨ memCs y (bdL false k ls)

private
  bd-root : ∀ k z os ls y → mem y (bd false k (lt (z ∷ os) ls)) ≡ ((y ==ℕ z) ∨ newc k os ls y)
  bd-root zero    z os ls y with y ==ℕ z
  ... | true  = refl
  ... | false = refl
  bd-root (suc k) z os ls y with y ==ℕ z
  ... | true  = refl
  ... | false = refl

  step : ∀ k Γ A x y →
    memL y (srcVars (dim A + suc k) (Γ ▸ A ▸ arr A (var x) (var (len Γ))))
      ≡ ((memL y (srcVars (dim A + suc k) Γ) ∨ ((y ==ℕ len Γ) ∨ false)) ∨ ((y ==ℕ suc (len Γ)) ∨ false))
  step k Γ A x y rewrite step-high (dim A + suc k) Γ A (arr A (var x) (var (len Γ))) (high (dim A) k)
                       | memL-snoc y (snoc (srcVars (dim A + suc k) Γ) (len Γ)) (suc (len Γ))
                       | memL-snoc y (srcVars (dim A + suc k) Γ) (len Γ) = refl

src-step : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) k y →
  memL y (srcVars (dim A + suc k) (fst (buildList ts d)))
    ≡ (memL y (srcVars (dim A + suc k) Γ)
       ∨ (memL y (fst (labCs ts (len Γ))) ∨ memCs y (bdL false k (fst (snd (labCs ts (len Γ)))))))
src-step []       {Γ} {x} {A} d k y = ∨-false (memL y (srcVars (dim A + suc k) Γ))
src-step (node ts' ∷ ts) {Γ} {x} {A} d k y
  with buildList ts' (pse d) | labCs ts' (suc (suc (len Γ))) | BL ts' (pse d) | child k
  where
  Γ₁ = Γ ▸ A ▸ arr A (var x) (var (len Γ))
  child : ∀ k → memL y (srcVars (dim A + suc k) (fst (buildList ts' (pse d))))
              ≡ (memL y (srcVars (dim A + suc k) Γ₁)
                 ∨ newc k (fst (labCs ts' (suc (suc (len Γ)))))
                          (fst (snd (labCs ts' (suc (suc (len Γ)))))) y)
  child zero =
    trans (cong (memL y) (low ts' (pse d) (dim A + 1) (lt-one (dim A))))
          (∨-false′ (memL y (srcVars (dim A + 1) Γ₁)))
  child (suc k) rewrite +-suc (dim A) (suc k) = src-step ts' (pse d) k y
... | Γ₂ , x₂ , d₂ | os₁ , ls₁ , .(len Γ₂) | refl , _ , _ , _ | c =
  trans (src-step ts (psd d₂) k y)
  (trans (cong (λ z → z ∨ R) c)
  (trans (cong (λ z → (z ∨ N) ∨ R) (step k Γ A x y))
  (trans (shuffle2 (memL y (srcVars i Γ)) (y ==ℕ len Γ) (y ==ℕ suc (len Γ)) N O Rs)
         (cong (λ z → memL y (srcVars i Γ) ∨ (((y ==ℕ len Γ) ∨ O) ∨ (z ∨ Rs)))
               (sym (bd-root k (suc (len Γ)) os₁ ls₁ y))))))
  where
  i = dim A + suc k
  N = newc k os₁ ls₁ y
  O = memL y (fst (labCs ts (len Γ₂)))
  Rs = memCs y (bdL false k (fst (snd (labCs ts (len Γ₂)))))
  R = O ∨ Rs

private
  ctxOf-build : ∀ τ → ctxOf τ ≡ fst (build τ pss)
  ctxOf-build τ with build τ pss
  ... | _ = refl

  unpad : ∀ a b → (a ∨ b) ≡ ((a ∨ false) ∨ b)
  unpad true  b = refl
  unpad false b = refl

lab-src : ∀ τ k y → mem y (bd false k (idTree τ)) ≡ memL y (srcVars k (ctxOf τ))
lab-src (node ts) zero y rewrite ctxOf-build (node ts) | low ts pss 0 tt with labCs ts 1
... | os , ls , _ = sym (∨-false′ _)
lab-src (node ts) (suc k) y rewrite ctxOf-build (node ts) | src-step ts pss k y with labCs ts 1
... | os , ls , _ = trans (bd-root (suc k) 0 os ls y) (unpad (y ==ℕ 0) _)

-- L3, source half: the labels of the source of idTree τ are ∂⁻Θ.
lab-∂⁻ : ∀ τ y → mem y (bd false (dimCtx (ctxOf τ) ∸ 1) (idTree τ)) ≡ memL y (∂⁻ (ctxOf τ))
lab-∂⁻ τ y = lab-src τ (dimCtx (ctxOf τ) ∸ 1) y

------------------------------------------------------------------------
-- Target half. At the dimension of the current cell each child's y
-- replaces the last target variable (dropLastᴸ in tgtVars), which is
-- why bd true 0 keeps only the last object.

private
  dropLast-snoc : ∀ L z → dropLastᴸ (snoc L z) ≡ L
  dropLast-snoc []            z = refl
  dropLast-snoc (a ∷ [])      z = refl
  dropLast-snoc (a ∷ b ∷ L)   z = cong (a ∷_) (dropLast-snoc (b ∷ L) z)

  <-irr : ∀ a → (a <ℕ a) ≡ false
  <-irr zero    = refl
  <-irr (suc a) = <-irr a

  <-+ : ∀ e k → ((e + suc k) <ℕ e) ≡ false
  <-+ zero    k = refl
  <-+ (suc e) k = <-+ e k

  ==-+ : ∀ e k → (e ==ℕ (e + suc k)) ≡ false
  ==-+ zero    k = refl
  ==-+ (suc e) k = ==-+ e k

  tstep-low : ∀ i Γ A B → T (i <ℕ dim A) → tgtVars i (Γ ▸ A ▸ B) ≡ tgtVars i Γ
  tstep-low i Γ A B h rewrite T-≡ h = refl

  tstep-eq : ∀ Γ A B → tgtVars (dim A) (Γ ▸ A ▸ B) ≡ snoc (dropLastᴸ (tgtVars (dim A) Γ)) (len Γ)
  tstep-eq Γ A B rewrite <-irr (dim A) | T-≡ (==ℕ-refl (dim A)) = refl

  tstep-high : ∀ k Γ A B → tgtVars (dim A + suc k) (Γ ▸ A ▸ B)
                          ≡ snoc (snoc (tgtVars (dim A + suc k) Γ) (len Γ)) (suc (len Γ))
  tstep-high k Γ A B rewrite <-+ (dim A) k | ==-+ (dim A) k = refl

-- Replace the last variable by the last of the new objects, if any.
repl : List Nat → List Nat → List Nat
repl T []       = T
repl T (o ∷ os) = snoc (dropLastᴸ T) (lastN (o ∷ os))

private
  repl-cons : ∀ T n os → repl (snoc (dropLastᴸ T) n) os ≡ repl T (n ∷ os)
  repl-cons T n []       = refl
  repl-cons T n (o ∷ os) rewrite dropLast-snoc (dropLastᴸ T) n = refl

tlow : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) i → T (i <ℕ dim A) →
       tgtVars i (fst (buildList ts d)) ≡ tgtVars i Γ
tlow []       d i h = refl
tlow (t ∷ ts) {Γ} {x} {A} d i h with build t (pse d) | tlow′ t (pse d) i (<-weak i (dim A) h)
  where
  tlow′ : ∀ t {Γ x A} (d : Γ ⊢ps x ∶ A) i → T (i <ℕ dim A) →
          tgtVars i (fst (build t d)) ≡ tgtVars i Γ
  tlow′ (node ts) d i h = tlow ts d i h
... | Γ₂ , _ , d₂ | e₂ =
  trans (tlow ts (psd d₂) i h) (trans e₂ (tstep-low i Γ A (arr A (var x) (var (len Γ))) h))

teq : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) →
      tgtVars (dim A) (fst (buildList ts d)) ≡ repl (tgtVars (dim A) Γ) (fst (labCs ts (len Γ)))
teq []       d = refl
teq (node ts' ∷ ts) {Γ} {x} {A} d
  with buildList ts' (pse d) | labCs ts' (suc (suc (len Γ))) | BL ts' (pse d)
     | tlow ts' (pse d) (dim A) (<-suc (dim A))
... | Γ₂ , x₂ , d₂ | os₁ , ls₁ , .(len Γ₂) | refl , _ , _ , _ | c =
  trans (teq ts (psd d₂))
  (trans (cong (λ z → repl z (fst (labCs ts (len Γ₂))))
               (trans c (tstep-eq Γ A (arr A (var x) (var (len Γ))))))
         (repl-cons (tgtVars (dim A) Γ) (len Γ) (fst (labCs ts (len Γ₂)))))

private
  shuffle3 : ∀ S a M o r → (((S ∨ (a ∨ false)) ∨ M) ∨ (o ∨ r)) ≡ (S ∨ ((a ∨ o) ∨ (M ∨ r)))
  shuffle3 true  a     M     o     r = refl
  shuffle3 false true  M     o     r = refl
  shuffle3 false false true  o     r with o
  ... | true  = refl
  ... | false = refl
  shuffle3 false false false o     r = refl

  assoc3 : ∀ X b c d → ((X ∨ (b ∨ false)) ∨ (c ∨ d)) ≡ (X ∨ ((b ∨ c) ∨ d))
  assoc3 true  b     c d = refl
  assoc3 false true  c d = refl
  assoc3 false false c d = refl

  pad : ∀ X b → (X ∨ (b ∨ false)) ≡ (X ∨ ((b ∨ false) ∨ false))
  pad X true  = refl
  pad X false = refl

  memL-snoc² : ∀ y T a b → memL y (snoc (snoc T a) b)
                         ≡ ((memL y T ∨ ((y ==ℕ a) ∨ false)) ∨ ((y ==ℕ b) ∨ false))
  memL-snoc² y T a b rewrite memL-snoc y (snoc T a) b | memL-snoc y T a = refl

  -- The child at bd index 0: its last object, or its root if it has none.
  last-child : ∀ y T n os₁ →
    memL y (repl (snoc (snoc T n) (suc n)) os₁)
      ≡ ((memL y T ∨ ((y ==ℕ n) ∨ false)) ∨ (((y ==ℕ lastN (suc n ∷ os₁)) ∨ false) ∨ false))
  last-child y T n [] = trans (memL-snoc² y T n (suc n)) (pad (memL y T ∨ ((y ==ℕ n) ∨ false)) (y ==ℕ suc n))
  last-child y T n (o ∷ os) rewrite dropLast-snoc (snoc T n) (suc n) =
    trans (memL-snoc y (snoc T n) (lastN (o ∷ os)))
    (trans (cong (λ z → z ∨ ((y ==ℕ lastN (o ∷ os)) ∨ false)) (memL-snoc y T n))
           (pad (memL y T ∨ ((y ==ℕ n) ∨ false)) (y ==ℕ lastN (o ∷ os))))

tgt-step : ∀ ts {Γ x A} (d : Γ ⊢ps x ∶ A) k y →
  memL y (tgtVars (dim A + suc k) (fst (buildList ts d)))
    ≡ (memL y (tgtVars (dim A + suc k) Γ)
       ∨ (memL y (fst (labCs ts (len Γ))) ∨ memCs y (bdL true k (fst (snd (labCs ts (len Γ)))))))
tgt-step []       {Γ} {x} {A} d k y = ∨-false (memL y (tgtVars (dim A + suc k) Γ))
tgt-step (node ts' ∷ ts) {Γ} {x} {A} d k y
  with buildList ts' (pse d) | labCs ts' (suc (suc (len Γ))) | BL ts' (pse d) | child k
  where
  Γ₁ = Γ ▸ A ▸ arr A (var x) (var (len Γ))
  child : ∀ k → memL y (tgtVars (dim A + suc k) (fst (buildList ts' (pse d))))
              ≡ ((memL y (tgtVars (dim A + suc k) Γ) ∨ ((y ==ℕ len Γ) ∨ false))
                 ∨ mem y (bd true k (fst (labT (node ts') (suc (len Γ)) (suc (suc (len Γ)))))))
  child zero rewrite +-one (dim A)
                   | teq ts' (pse d)
                   | sym (+-one (dim A))
                   | tstep-high 0 Γ A (arr A (var x) (var (len Γ)))
                   with labCs ts' (suc (suc (len Γ)))
  ... | os₁ , ls₁ , _ = last-child y (tgtVars (dim A + 1) Γ) (len Γ) os₁
  child (suc k) rewrite +-suc (dim A) (suc k)
                      | tgt-step ts' (pse d) k y
                      | sym (+-suc (dim A) (suc k))
                      | tstep-high (suc k) Γ A (arr A (var x) (var (len Γ)))
                      | memL-snoc² y (tgtVars (dim A + suc (suc k)) Γ) (len Γ) (suc (len Γ))
                      with labCs ts' (suc (suc (len Γ)))
  ... | os₁ , ls₁ , _ =
    assoc3 (memL y (tgtVars (dim A + suc (suc k)) Γ) ∨ ((y ==ℕ len Γ) ∨ false))
           (y ==ℕ suc (len Γ)) (memL y os₁) (memCs y (bdL true k ls₁))
... | Γ₂ , x₂ , d₂ | os₁ , ls₁ , .(len Γ₂) | refl , _ , _ , _ | c =
  trans (tgt-step ts (psd d₂) k y)
  (trans (cong (λ z → z ∨ (O ∨ Rs)) c)
         (shuffle3 (memL y (tgtVars i Γ)) (y ==ℕ len Γ) M O Rs))
  where
  i = dim A + suc k
  M = mem y (bd true k (lt (suc (len Γ) ∷ os₁) ls₁))
  O = memL y (fst (labCs ts (len Γ₂)))
  Rs = memCs y (bdL true k (fst (snd (labCs ts (len Γ₂)))))

private
  bd-root-true : ∀ k z os ls y → mem y (bd true (suc k) (lt (z ∷ os) ls))
                                ≡ (((y ==ℕ z) ∨ false) ∨ (memL y os ∨ memCs y (bdL true k ls)))
  bd-root-true k z os ls y with y ==ℕ z
  ... | true  = refl
  ... | false = refl

  last-root : ∀ y os → (((y ==ℕ lastN (0 ∷ os)) ∨ false) ∨ false) ≡ memL y (repl (0 ∷ []) os)
  last-root y []       = sym (∨-false′ _)
  last-root y (o ∷ os) = sym (∨-false′ _)

lab-tgt : ∀ τ k y → mem y (bd true k (idTree τ)) ≡ memL y (tgtVars k (ctxOf τ))
lab-tgt (node ts) zero y rewrite ctxOf-build (node ts) | teq ts pss with labCs ts 1
... | os , ls , _ = last-root y os
lab-tgt (node ts) (suc k) y rewrite ctxOf-build (node ts) | tgt-step ts pss k y with labCs ts 1
... | os , ls , _ = bd-root-true k 0 os ls y

-- L3, target half: the labels of the target of idTree τ are ∂⁺Θ.
lab-∂⁺ : ∀ τ y → mem y (bd true (dimCtx (ctxOf τ) ∸ 1) (idTree τ)) ≡ memL y (∂⁺ (ctxOf τ))
lab-∂⁺ τ y = lab-tgt τ (dimCtx (ctxOf τ) ∸ 1) y
