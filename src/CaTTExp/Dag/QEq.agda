------------------------------------------------------------------------
-- Sharing-aware comparison of two tables (CaTTExp.Dag.Table).
--
-- A query (a context and a type) is given as its own table Q; the
-- certificate's root lives in the table R. Comparing their unfoldings
-- with ==Ctx / ==Ty would walk both as trees, which for large queries is
-- as infeasible as tree-walking the answer. Here the comparison is by
-- ids, with a memo of id pairs already shown equal (one for terms, one
-- for contexts), so each pair is compared once.
--
-- Soundness (module Sound): when both tables are decreasing, an
-- accepting run shows that the unfoldings are equal.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Dag.Table
open import CaTTExp.Dag.Trie
open import CaTTExp.Dag.Lemmas
import CaTTExp.Dag.Unfold

module CaTTExp.Dag.QEq (Q R : Nat → Maybe Item) where

-- Memo: query term id ↦ certificate term id, query context id ↦
-- certificate context id.
Memo : Set
Memo = Trie Nat × Trie Nat

addT addC : Nat → Nat → Memo → Memo
addT q c (mt , mc) = insert q c mt , mc
addC q c (mt , mc) = mt , insert q c mc

mutual
  eqT : Nat → Nat → Nat → Memo → Maybe Memo
  eqT zero    q c M = nothing
  eqT (suc f) q c M = eqTHit f q c M (lookupT q (fst M))

  eqTHit : Nat → Nat → Nat → Memo → Maybe Nat → Maybe Memo
  eqTHit f q c M (just c') = if c' ==ℕ c then just M else nothing
  eqTHit f q c M nothing   = eqTI f q c (Q q) (R c) M

  eqTI : Nat → Nat → Nat → Maybe Item → Maybe Item → Memo → Maybe Memo
  eqTI f q c (just (V i)) (just (V j)) M =
    if i ==ℕ j then just (addT q c M) else nothing
  eqTI f q c (just (C h as)) (just (C h' bs)) M =
    (eqH f (Q h) (R h') M >>= eqL f as bs) >>= λ M' → just (addT q c M')
  eqTI f q c _ _ M = nothing

  eqH : Nat → Maybe Item → Maybe Item → Memo → Maybe Memo
  eqH f (just (H c A)) (just (H c' B)) M = eqC f c c' M >>= eqRT f A B
  eqH f _ _ M = nothing

  eqC : Nat → Nat → Nat → Memo → Maybe Memo
  eqC zero    q c M = nothing
  eqC (suc f) q c M = eqCHit f q c M (lookupT q (snd M))

  eqCHit : Nat → Nat → Nat → Memo → Maybe Nat → Maybe Memo
  eqCHit f q c M (just c') = if c' ==ℕ c then just M else nothing
  eqCHit f q c M nothing   = eqCI f q c (Q q) (R c) M

  eqCI : Nat → Nat → Nat → Maybe Item → Maybe Item → Memo → Maybe Memo
  eqCI f q c (just E) (just E) M = just (addC q c M)
  eqCI f q c (just (S q' A)) (just (S c' B)) M =
    (eqC f q' c' M >>= eqRT f A B) >>= λ M' → just (addC q c M')
  eqCI f q c _ _ M = nothing

  eqRT : Nat → RTy → RTy → Memo → Maybe Memo
  eqRT f ⋆ᵣ ⋆ᵣ M = just M
  eqRT f (arrᵣ A s t) (arrᵣ B u v) M = (eqRT f A B M >>= eqT f s u) >>= eqT f t v
  eqRT f _ _ M = nothing

  eqL : Nat → List Nat → List Nat → Memo → Maybe Memo
  eqL f []       []       M = just M
  eqL f (a ∷ as) (b ∷ bs) M = eqT f a b M >>= eqL f as bs
  eqL f _        _        M = nothing

-- The whole query: a context and a type.
qeqOK : Nat → Nat → Nat → RTy → RTy → Bool
qeqOK fuel qg g qA A = is-just (eqC fuel qg g (tleaf , tleaf) >>= eqRT fuel qA A)

-- A query that is a context alone.
qeqCOK : Nat → Nat → Nat → Bool
qeqCOK fuel qg g = is-just (eqC fuel qg g (tleaf , tleaf))

------------------------------------------------------------------------
-- Soundness

bind-just : ∀ {A B : Set} (m : Maybe A) {k : A → Maybe B} {y} → (m >>= k) ≡ just y →
            Σ A λ x → (m ≡ just x) × (k x ≡ just y)
bind-just (just x) e = x , refl , e

cong₃′ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
         a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃′ f refl refl refl = refl

module UQ = CaTTExp.Dag.Unfold Q
module UR = CaTTExp.Dag.Unfold R

module Sound (decQ : UQ.Decreasing) (decR : UR.Decreasing) where
  module IQ = UQ.Irr decQ
  module IR = UR.Irr decR

  Inv : Memo → Set
  Inv (mt , mc) = All (λ q c → UQ.⟦ q ⟧ ≡ UR.⟦ c ⟧) mt × All (λ q c → UQ.⟦ q ⟧c ≡ UR.⟦ c ⟧c) mc

  inv₀ : Inv (tleaf , tleaf)
  inv₀ = tt , tt

  addT-inv : ∀ {q c} M → Inv M → UQ.⟦ q ⟧ ≡ UR.⟦ c ⟧ → Inv (addT q c M)
  addT-inv (mt , mc) (it , ic) e = insert-All it e , ic

  addC-inv : ∀ {q c} M → Inv M → UQ.⟦ q ⟧c ≡ UR.⟦ c ⟧c → Inv (addC q c M)
  addC-inv (mt , mc) (it , ic) e = it , insert-All ic e

  HeadEq : Maybe Item → Maybe Item → Set
  HeadEq mi mj = Σ Nat λ c → Σ RTy λ A → Σ Nat λ c' → Σ RTy λ B →
    (mi ≡ just (H c A)) × (mj ≡ just (H c' B)) ×
    (UQ.⟦ c ⟧c ≡ UR.⟦ c' ⟧c) × (UQ.⟦ A ⟧ty ≡ UR.⟦ B ⟧ty)

  mutual
    eqT-sound : ∀ f q c M {M'} → Inv M → eqT f q c M ≡ just M' →
                Inv M' × (UQ.⟦ q ⟧ ≡ UR.⟦ c ⟧)
    eqT-sound (suc f) q c M inv e = eqTHit-sound f q c M _ refl inv e

    eqTHit-sound : ∀ f q c M m {M'} → lookupT q (fst M) ≡ m → Inv M →
                   eqTHit f q c M m ≡ just M' → Inv M' × (UQ.⟦ q ⟧ ≡ UR.⟦ c ⟧)
    eqTHit-sound f q c M (just c') eh inv e with if-just (c' ==ℕ c) e
    ... | b , refl =
      inv , subst (λ x → UQ.⟦ q ⟧ ≡ UR.⟦ x ⟧) (==ℕ-sound c' c b)
              (lookup-All {k = q} {t = fst M} (fst inv) eh)
    eqTHit-sound f q c M nothing eh inv e = eqTI-sound f q c (Q q) (R c) refl refl M inv e

    eqTI-sound : ∀ f q c mi mj → Q q ≡ mi → R c ≡ mj → ∀ M {M'} → Inv M →
                 eqTI f q c mi mj M ≡ just M' → Inv M' × (UQ.⟦ q ⟧ ≡ UR.⟦ c ⟧)
    eqTI-sound f q c (just (V i)) (just (V j)) eq ec M inv e with if-just (i ==ℕ j) e
    ... | b , refl =
      let eqv = trans (IQ.⟦⟧-V eq)
                  (trans (cong var (==ℕ-sound i j b)) (sym (IR.⟦⟧-V ec))) in
      addT-inv M inv eqv , eqv
    eqTI-sound f q c (just (C h as)) (just (C h' bs)) eq ec M inv e
      with bind-just (eqH f (Q h) (R h') M >>= eqL f as bs) e
    ... | M₂ , e₂ , refl with bind-just (eqH f (Q h) (R h') M) e₂
    ... | M₁ , e₁ , e₃ with eqH-sound f (Q h) (R h') M inv e₁
    ... | inv₁ , (cq , A , cr , B , eh , eh' , ectx , ety) with eqL-sound f as bs M₁ inv₁ e₃
    ... | inv₂ , esub =
      let eqv = trans (IQ.⟦⟧-C eq eh)
                  (trans (cong₃′ coh ectx ety esub) (sym (IR.⟦⟧-C ec eh'))) in
      addT-inv M₂ inv₂ eqv , eqv
    eqTI-sound f q c (just (V _))    (just (C _ _)) eq ec M inv ()
    eqTI-sound f q c (just (V _))    (just E)       eq ec M inv ()
    eqTI-sound f q c (just (V _))    (just (S _ _)) eq ec M inv ()
    eqTI-sound f q c (just (V _))    (just (H _ _)) eq ec M inv ()
    eqTI-sound f q c (just (V _))    nothing        eq ec M inv ()
    eqTI-sound f q c (just (C _ _))  (just (V _))   eq ec M inv ()
    eqTI-sound f q c (just (C _ _))  (just E)       eq ec M inv ()
    eqTI-sound f q c (just (C _ _))  (just (S _ _)) eq ec M inv ()
    eqTI-sound f q c (just (C _ _))  (just (H _ _)) eq ec M inv ()
    eqTI-sound f q c (just (C _ _))  nothing        eq ec M inv ()
    eqTI-sound f q c (just E)        _              eq ec M inv ()
    eqTI-sound f q c (just (S _ _))  _              eq ec M inv ()
    eqTI-sound f q c (just (H _ _))  _              eq ec M inv ()
    eqTI-sound f q c nothing         _              eq ec M inv ()

    eqH-sound : ∀ f mi mj M {M'} → Inv M → eqH f mi mj M ≡ just M' → Inv M' × HeadEq mi mj
    eqH-sound f (just (H c A)) (just (H c' B)) M inv e with bind-just (eqC f c c' M) e
    ... | M₁ , e₁ , e₂ with eqC-sound f c c' M inv e₁
    ... | inv₁ , ectx with eqRT-sound f A B M₁ inv₁ e₂
    ... | inv₂ , ety = inv₂ , (c , A , c' , B , refl , refl , ectx , ety)
    eqH-sound f (just (V _))   _              M inv ()
    eqH-sound f (just (C _ _)) _              M inv ()
    eqH-sound f (just E)       _              M inv ()
    eqH-sound f (just (S _ _)) _              M inv ()
    eqH-sound f nothing        _              M inv ()
    eqH-sound f (just (H _ _)) (just (V _))   M inv ()
    eqH-sound f (just (H _ _)) (just (C _ _)) M inv ()
    eqH-sound f (just (H _ _)) (just E)       M inv ()
    eqH-sound f (just (H _ _)) (just (S _ _)) M inv ()
    eqH-sound f (just (H _ _)) nothing        M inv ()

    eqC-sound : ∀ f q c M {M'} → Inv M → eqC f q c M ≡ just M' →
                Inv M' × (UQ.⟦ q ⟧c ≡ UR.⟦ c ⟧c)
    eqC-sound (suc f) q c M inv e = eqCHit-sound f q c M _ refl inv e

    eqCHit-sound : ∀ f q c M m {M'} → lookupT q (snd M) ≡ m → Inv M →
                   eqCHit f q c M m ≡ just M' → Inv M' × (UQ.⟦ q ⟧c ≡ UR.⟦ c ⟧c)
    eqCHit-sound f q c M (just c') eh inv e with if-just (c' ==ℕ c) e
    ... | b , refl =
      inv , subst (λ x → UQ.⟦ q ⟧c ≡ UR.⟦ x ⟧c) (==ℕ-sound c' c b)
              (lookup-All {k = q} {t = snd M} (snd inv) eh)
    eqCHit-sound f q c M nothing eh inv e = eqCI-sound f q c (Q q) (R c) refl refl M inv e

    eqCI-sound : ∀ f q c mi mj → Q q ≡ mi → R c ≡ mj → ∀ M {M'} → Inv M →
                 eqCI f q c mi mj M ≡ just M' → Inv M' × (UQ.⟦ q ⟧c ≡ UR.⟦ c ⟧c)
    eqCI-sound f q c (just E) (just E) eq ec M inv refl =
      let eqv = trans (IQ.⟦⟧c-E eq) (sym (IR.⟦⟧c-E ec)) in
      addC-inv M inv eqv , eqv
    eqCI-sound f q c (just (S q' A)) (just (S c' B)) eq ec M inv e
      with bind-just (eqC f q' c' M >>= eqRT f A B) e
    ... | M₂ , e₂ , refl with bind-just (eqC f q' c' M) e₂
    ... | M₁ , e₁ , e₃ with eqC-sound f q' c' M inv e₁
    ... | inv₁ , ectx with eqRT-sound f A B M₁ inv₁ e₃
    ... | inv₂ , ety =
      let eqv = trans (IQ.⟦⟧c-S eq) (trans (cong₂ _▸_ ectx ety) (sym (IR.⟦⟧c-S ec))) in
      addC-inv M₂ inv₂ eqv , eqv
    eqCI-sound f q c (just E)       (just (V _))   eq ec M inv ()
    eqCI-sound f q c (just E)       (just (C _ _)) eq ec M inv ()
    eqCI-sound f q c (just E)       (just (S _ _)) eq ec M inv ()
    eqCI-sound f q c (just E)       (just (H _ _)) eq ec M inv ()
    eqCI-sound f q c (just E)       nothing        eq ec M inv ()
    eqCI-sound f q c (just (S _ _)) (just (V _))   eq ec M inv ()
    eqCI-sound f q c (just (S _ _)) (just (C _ _)) eq ec M inv ()
    eqCI-sound f q c (just (S _ _)) (just E)       eq ec M inv ()
    eqCI-sound f q c (just (S _ _)) (just (H _ _)) eq ec M inv ()
    eqCI-sound f q c (just (S _ _)) nothing        eq ec M inv ()
    eqCI-sound f q c (just (V _))   _              eq ec M inv ()
    eqCI-sound f q c (just (C _ _)) _              eq ec M inv ()
    eqCI-sound f q c (just (H _ _)) _              eq ec M inv ()
    eqCI-sound f q c nothing        _              eq ec M inv ()

    eqRT-sound : ∀ f A B M {M'} → Inv M → eqRT f A B M ≡ just M' →
                 Inv M' × (UQ.⟦ A ⟧ty ≡ UR.⟦ B ⟧ty)
    eqRT-sound f ⋆ᵣ ⋆ᵣ M inv refl = inv , refl
    eqRT-sound f (arrᵣ A s t) (arrᵣ B u v) M inv e
      with bind-just (eqRT f A B M >>= eqT f s u) e
    ... | M₂ , e₂ , e₃ with bind-just (eqRT f A B M) e₂
    ... | M₁ , e₁ , e₄ with eqRT-sound f A B M inv e₁
    ... | inv₁ , eA with eqT-sound f s u M₁ inv₁ e₄
    ... | inv₂ , es with eqT-sound f t v M₂ inv₂ e₃
    ... | inv₃ , et = inv₃ , cong₃′ arr eA es et
    eqRT-sound f ⋆ᵣ (arrᵣ _ _ _) M inv ()
    eqRT-sound f (arrᵣ _ _ _) ⋆ᵣ M inv ()

    eqL-sound : ∀ f as bs M {M'} → Inv M → eqL f as bs M ≡ just M' →
                Inv M' × (UQ.⟦ as ⟧s ≡ UR.⟦ bs ⟧s)
    eqL-sound f []       []       M inv refl = inv , refl
    eqL-sound f (a ∷ as) (b ∷ bs) M inv e with bind-just (eqT f a b M) e
    ... | M₁ , e₁ , e₂ with eqT-sound f a b M inv e₁
    ... | inv₁ , ea with eqL-sound f as bs M₁ inv₁ e₂
    ... | inv₂ , eas = inv₂ , cong₂ _,ₛ_ eas ea
    eqL-sound f []       (_ ∷ _)  M inv ()
    eqL-sound f (_ ∷ _)  []       M inv ()

  qeqOK-sound : ∀ fuel qg g qA A → T (qeqOK fuel qg g qA A) →
                (UQ.⟦ qg ⟧c ≡ UR.⟦ g ⟧c) × (UQ.⟦ qA ⟧ty ≡ UR.⟦ A ⟧ty)
  qeqOK-sound fuel qg g qA A p with is-just-sound _ p
  ... | M₂ , e with bind-just (eqC fuel qg g (tleaf , tleaf)) e
  ... | M₁ , e₁ , e₂ with eqC-sound fuel qg g _ inv₀ e₁
  ... | inv₁ , ectx = ectx , snd (eqRT-sound fuel qA A M₁ inv₁ e₂)

  qeqCOK-sound : ∀ fuel qg g → T (qeqCOK fuel qg g) → UQ.⟦ qg ⟧c ≡ UR.⟦ g ⟧c
  qeqCOK-sound fuel qg g p with is-just-sound _ p
  ... | M , e = snd (eqC-sound fuel qg g _ inv₀ e)
