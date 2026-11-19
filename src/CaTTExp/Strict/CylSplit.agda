------------------------------------------------------------------------
-- Rows of the cylinder atoms ⟨k ⊗ i⟩ against those of ⟨s k ⊗ i⟩ and
-- ⟨t k ⊗ i⟩ (ledger A5, (N3), collapse step 5).
--
-- For an ordered globular presentation D and k of degree m ≥ 1, below
-- its top row ⟨k ⊗ i⟩ agrees with ⟨s k ⊗ i⟩ on the negative side and
-- with ⟨t k ⊗ i⟩ on the positive side (one degree lower, from the
-- globular identities), so
--     src_{m−1} ⟨k ⊗ i⟩ = src_{m−1} ⟨s k ⊗ i⟩,
--     tgt_{m−1} ⟨k ⊗ i⟩ = tgt_{m−1} ⟨t k ⊗ i⟩,
-- and its row m is (k⊗e₀ + sk⊗i, tk⊗i + k⊗e₁) with the two end copies
-- at positions k·3 and k·3 + 2 of the layout.
------------------------------------------------------------------------
module CaTTExp.Strict.CylSplit where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-suc; ≤-trans; ≤-<-⊥; tri; tri<; tri≡; tri>)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.BasisCheck
open import CaTTExp.Strict.Cylinder
open import CaTTExp.Strict.GlobBasis

-- The parity flag of the middle atom, with the top row included.
P̂ : Nat → Nat → Bool
P̂ g e = if e <ℕ suc g then not (even (g ∸ e)) else true

P̂-shift : ∀ g d → P̂ (suc g) (suc d) ≡ P̂ g d
P̂-shift g d = refl

module CylSplit (D : GData) where
  open GData D
  private
    module K  = GB D
    module FO = FreeOn D 0
    module CD = CylDD K.basis K.hyp K.DegP-ok K.DegM-ok
    module A  = Atom K.basis
    module A′ = Atom (Cyl.B′ K.basis)

  pmx ppx : Nat → Nat → Vec Nat N
  pmx x zero    = 0c
  pmx x (suc j) = fst (A.entK x j)
  ppx x zero    = 0c
  ppx x (suc j) = snd (A.entK x j)

  private
    <ℕ-true : ∀ e g → e ≤ g → (e <ℕ suc g) ≡ true
    <ℕ-true zero    g       _       = refl
    <ℕ-true (suc e) (suc g) (s≤s l) = <ℕ-true e g l

    <ℕ-self : ∀ g → (suc g <ℕ suc g) ≡ false
    <ℕ-self zero    = refl
    <ℕ-self (suc g) = <ℕ-self g

    pm≡ : ∀ x (xN : x < N) e → CD.Mid.pm x xN e ≡ pmx x e
    pm≡ x xN zero    = refl
    pm≡ x xN (suc e) = refl
    pp≡ : ∀ x (xN : x < N) e → CD.Mid.pp x xN e ≡ ppx x e
    pp≡ x xN zero    = refl
    pp≡ x xN (suc e) = refl

  -- ⟨x ⊗ i⟩ at depth e ≤ deg x + 1, uniformly.
  form : ∀ x (xN : x < N) e → e ≤ suc (A.deg x) →
         A′.entK (x * 3 + 1) e ≡ (CD.F (P̂ (A.deg x) e) (pmx x e) (fst (A.entK x e)) , CD.G (P̂ (A.deg x) e) (ppx x e) (snd (A.entK x e)))
  form x xN e l with tri e (suc (A.deg x))
  ... | tri> l′ = ⊥-elim (≤-<-⊥ l l′)
  ... | tri< (s≤s l′) rewrite <ℕ-true e (A.deg x) l′ =
    trans (CD.Mid.claim x xN e l′) (cong₂ (λ a b → (CD.F _ a (fst (A.entK x e)) , CD.G _ b (snd (A.entK x e)))) (pm≡ x xN e) (pp≡ x xN e))
  ... | tri≡ refl rewrite <ℕ-self (A.deg x) = CD.Mid.top x xN

  private
    up : ∀ x → x < N → 1 ≤ gd x → 1 ≤ A.deg x
    up x xN p = subst (1 ≤_) (sym (K.gdeg-at x xN)) p

    pos : ∀ {g} → 1 ≤ g → suc (g ∸ 1) ≡ g
    pos {suc g} _ = refl

    two-one : ∀ {g} → 2 ≤ g → 1 ≤ g ∸ 1
    two-one {suc (suc g)} _ = s≤s z≤n
    two-one {suc zero} (s≤s ())

  deg-s : ∀ k → k < N → 1 ≤ gd k → A.deg k ≡ suc (A.deg (s k))
  deg-s k kN p = trans (K.gdeg-at k kN) (sym (trans (cong suc (trans (K.gdeg-at (s k) (sN k kN p)) (ds k kN p))) (pos p)))
  deg-t : ∀ k → k < N → 1 ≤ gd k → A.deg k ≡ suc (A.deg (t k))
  deg-t k kN p = trans (K.gdeg-at k kN) (sym (trans (cong suc (trans (K.gdeg-at (t k) (tN k kN p)) (dt k kN p))) (pos p)))

  Am-s : ∀ k → k < N → 1 ≤ gd k → ∀ e → fst (A.entK k (suc e)) ≡ fst (A.entK (s k) e)
  Am-s k kN p e = cong fst (FO.claim k kN (up k kN p) e)
  Ap-t : ∀ k → k < N → 1 ≤ gd k → ∀ e → snd (A.entK k (suc e)) ≡ snd (A.entK (t k) e)
  Ap-t k kN p e = cong snd (FO.claim k kN (up k kN p) e)

  Ap-s : ∀ k → k < N → 2 ≤ gd k → ∀ e → snd (A.entK k (suc (suc e))) ≡ snd (A.entK (s k) (suc e))
  Ap-s k kN p e =
    trans (Ap-t k kN p1 (suc e))
      (trans (Ap-t (t k) tkN (subst (1 ≤_) (sym (dt k kN p1)) (two-one p)) e)
        (sym (trans (Ap-t (s k) skN (subst (1 ≤_) (sym (ds k kN p1)) (two-one p)) e) (cong (λ y → snd (A.entK y e)) (gtt k kN p)))))
    where
    p1 = ≤-trans (s≤s z≤n) p
    tkN = tN k kN p1
    skN = sN k kN p1
  Am-t : ∀ k → k < N → 2 ≤ gd k → ∀ e → fst (A.entK k (suc (suc e))) ≡ fst (A.entK (t k) (suc e))
  Am-t k kN p e =
    trans (Am-s k kN p1 (suc e))
      (trans (Am-s (s k) skN (subst (1 ≤_) (sym (ds k kN p1)) (two-one p)) e)
        (sym (trans (Am-s (t k) tkN (subst (1 ≤_) (sym (dt k kN p1)) (two-one p)) e) (cong (λ y → fst (A.entK y e)) (sym (gss k kN p))))))
    where
    p1 = ≤-trans (s≤s z≤n) p
    tkN = tN k kN p1
    skN = sN k kN p1

  -- Negative rows of ⟨k⊗i⟩ below the top are those of ⟨sk⊗i⟩.
  fst-s : ∀ k (kN : k < N) (p : 1 ≤ gd k) d → 1 ≤ d → d ≤ suc (A.deg (s k)) →
          fst (A′.entK (k * 3 + 1) (suc d)) ≡ fst (A′.entK (s k * 3 + 1) d)
  fst-s k kN p (suc d) _ l =
    trans (cong fst (form k kN (suc (suc d)) (subst (λ g → suc (suc d) ≤ suc g) (sym (deg-s k kN p)) (s≤s l))))
      (trans (cong₃ (λ e a b → CD.F e a b) (cong (λ g → P̂ g (suc (suc d))) (deg-s k kN p)) (Am-s k kN p d) (Am-s k kN p (suc d)))
             (sym (cong fst (form (s k) (sN k kN p) (suc d) l))))
    where
    cong₃ : ∀ {A B C R : Set} (f : A → B → C → R) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
    cong₃ f refl refl refl = refl

  -- Positive rows of ⟨k⊗i⟩ below the top are those of ⟨tk⊗i⟩.
  snd-t : ∀ k (kN : k < N) (p : 1 ≤ gd k) d → 1 ≤ d → d ≤ suc (A.deg (t k)) →
          snd (A′.entK (k * 3 + 1) (suc d)) ≡ snd (A′.entK (t k * 3 + 1) d)
  snd-t k kN p (suc d) _ l =
    trans (cong snd (form k kN (suc (suc d)) (subst (λ g → suc (suc d) ≤ suc g) (sym (deg-t k kN p)) (s≤s l))))
      (trans (cong₃ (λ e a b → CD.G e a b) (cong (λ g → P̂ g (suc (suc d))) (deg-t k kN p)) (Ap-t k kN p d) (Ap-t k kN p (suc d)))
             (sym (cong snd (form (t k) (tN k kN p) (suc d) l))))
    where
    cong₃ : ∀ {A B C R : Set} (f : A → B → C → R) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
    cong₃ f refl refl refl = refl

  -- One more row down, the other side agrees too (globular identities).
  snd-s : ∀ k (kN : k < N) (p : 2 ≤ gd k) d → 2 ≤ d → d ≤ suc (A.deg (s k)) →
          snd (A′.entK (k * 3 + 1) (suc d)) ≡ snd (A′.entK (s k * 3 + 1) d)
  snd-s k kN p (suc zero) (s≤s ()) l
  snd-s k kN p (suc (suc d)) _ l =
    trans (cong snd (form k kN (suc (suc (suc d))) (subst (λ g → suc (suc (suc d)) ≤ suc g) (sym (deg-s k kN p1)) (s≤s l))))
      (trans (cong₃ (λ e a b → CD.G e a b) (cong (λ g → P̂ g (suc (suc (suc d)))) (deg-s k kN p1)) (Ap-s k kN p d) (Ap-s k kN p (suc d)))
             (sym (cong snd (form (s k) (sN k kN p1) (suc (suc d)) l))))
    where
    p1 = ≤-trans (s≤s z≤n) p
    cong₃ : ∀ {A B C R : Set} (f : A → B → C → R) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
    cong₃ f refl refl refl = refl
  fst-t : ∀ k (kN : k < N) (p : 2 ≤ gd k) d → 2 ≤ d → d ≤ suc (A.deg (t k)) →
          fst (A′.entK (k * 3 + 1) (suc d)) ≡ fst (A′.entK (t k * 3 + 1) d)
  fst-t k kN p (suc zero) (s≤s ()) l
  fst-t k kN p (suc (suc d)) _ l =
    trans (cong fst (form k kN (suc (suc (suc d))) (subst (λ g → suc (suc (suc d)) ≤ suc g) (sym (deg-t k kN p1)) (s≤s l))))
      (trans (cong₃ (λ e a b → CD.F e a b) (cong (λ g → P̂ g (suc (suc (suc d)))) (deg-t k kN p1)) (Am-t k kN p d) (Am-t k kN p (suc d)))
             (sym (cong fst (form (t k) (tN k kN p1) (suc (suc d)) l))))
    where
    p1 = ≤-trans (s≤s z≤n) p
    cong₃ : ∀ {A B C R : Set} (f : A → B → C → R) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
    cong₃ f refl refl refl = refl

  private
    even-pred : ∀ g → 1 ≤ g → not (even (g ∸ 1)) ≡ even g
    even-pred (suc g) _ = sym (even-suc g)

    cyl-split : ∀ (a b c : Vec Nat N) → cyl (Basis.gdeg K.basis) a b c ≡ cyl (Basis.gdeg K.basis) 0c b 0c +c cyl (Basis.gdeg K.basis) a 0c c
    cyl-split a b c =
      trans (cong₃ (cyl (Basis.gdeg K.basis)) (sym (+c-id a)) (sym (r0 b)) (sym (+c-id c)))
            (cyl-+ (Basis.gdeg K.basis) 0c b 0c a 0c c)
      where
      cong₃ : ∀ {A B C R : Set} (f : A → B → C → R) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
      cong₃ f refl refl refl = refl
      r0 : ∀ (u : Vec Nat N) → u +c 0c ≡ u
      r0 u = trans (+c-comm u 0c) (+c-id u)

    if-flip : ∀ b (u : Vec Nat N) → (if b then 0c else u) ≡ (if not b then u else 0c)
    if-flip true  u = refl
    if-flip false u = refl

  -- Row m of ⟨k ⊗ i⟩: (sk⊗i + k⊗e₀, k⊗e₁ + tk⊗i), the end copies at k·3, k·3 + 2.
  row-top : ∀ k (kN : k < N) → 1 ≤ gd k →
            A′.entK (k * 3 + 1) 1 ≡ (unit (s k * 3 + 1) +c unit (k * 3) , unit (k * 3 + 2) +c unit (t k * 3 + 1))
  row-top k kN p =
    trans (form k kN 1 (s≤s z≤n))
      (cong₂ _,_
        (trans (cong (λ e → CD.F e (unit k) (fst (A.entK k 1))) Pe)
          (trans (cyl-split _ _ _)
            (cong₂ _+c_ (trans (cong (λ v → cyl gs 0c v 0c) (cong fst s1)) (cyl-unit-mid gs (s k) (sN k kN p)))
                        (trans (cong (λ v → cyl gs (if even (g k) then unit k else 0c) 0c v) (if-flip (even (g k)) (unit k)))
                               (cyl-unit-lo gs k kN)))))
        (trans (cong (λ e → CD.G e (unit k) (snd (A.entK k 1))) Pe)
          (trans (cyl-split _ _ _)
            (trans (+c-comm _ _)
              (cong₂ _+c_ (trans (cong (λ v → cyl gs v 0c (if even (g k) then unit k else 0c)) (if-flip (even (g k)) (unit k)))
                                 (cyl-unit-hi gs k kN))
                          (trans (cong (λ v → cyl gs 0c v 0c) (cong snd s1)) (cyl-unit-mid gs (t k) (tN k kN p))))))))
    where
    gs = Basis.gdeg K.basis
    g = λ k → at 0 gs k
    Pe : P̂ (A.deg k) 1 ≡ even (g k)
    Pe = go (A.deg k) (up k kN p)
      where
      go : ∀ h → 1 ≤ h → P̂ h 1 ≡ even h
      go (suc h) _ = sym (even-suc h)
    s1 : A.entK k 1 ≡ (unit (s k) , unit (t k))
    s1 = FO.claim k kN (up k kN p) 0
