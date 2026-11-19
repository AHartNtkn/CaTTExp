------------------------------------------------------------------------
-- Unitality of K ⊗ L, and with it `Hyp (K ⊗ L)` (ledger A5, N3).
--
-- Steiner's formula for the atoms of a tensor (Steiner 2004, §5):
-- for generators x of K and y of L, at depth d below the top,
--
--   ⟨x ⊗ y⟩^α_d  =  Σ_{a ≤ d} ⟨x⟩^α_a ⊗ ⟨y⟩^{σ_a α}_{d − a},
--
-- with depths counted down from the top of each atom, and σ_a flipping
-- the sign when deg x − a is odd. `Pair.entF` proves it by induction
-- on d. The right side F_d satisfies
--
--   ∂⁺F^α_d + F⁻_{d+1} = ∂⁻F^α_d + F⁺_{d+1}            (`EqC`)
--
-- by telescoping, and F⁻_{d+1}, F⁺_{d+1} are disjoint (`DjF`): terms
-- with different a differ in K-degree, and at equal a either
-- ⟨x⟩⁻_a, ⟨x⟩⁺_a or ⟨y⟩⁻_b, ⟨y⟩⁺_b are disjoint. Those two facts pin
-- down the truncated differences of `Atom.step` (`uniq`). At the
-- bottom only a = deg x survives, so ε⟨x ⊗ y⟩^α_0 = ε⟨x⟩_0 · ε⟨y⟩_0 = 1.
--
-- `TensorUnit.Hyp⊗`: if B and C satisfy `Hyp` and the degree
-- conditions, so does the basis B⊗ of K ⊗ L. No unitality is assumed
-- beyond that of B and C.
------------------------------------------------------------------------
module CaTTExp.Strict.TensorUnit where

open import CaTTExp.Prelude
open import Agda.Builtin.Nat using (_*_)
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-suc)
open import CaTTExp.Strict.Tables using (Vec; []; _∷_)
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms using (at; unit; _∸c_; module Atom)
open import CaTTExp.Strict.Generation using (Hyp; at-0c; ≤-dec)
open import CaTTExp.Strict.BasisCheck using (DegP; DegM; degFix; zipV; ⊙-0c)
open import CaTTExp.Strict.Cylinder using (even; even-suc)
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Strict.Bag using (+-zero; +-suc; +-comm; +-cancelˡ)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)
open import CaTTExp.Strict.TensorBasis

------------------------------------------------------------------------
-- Arithmetic.

private
  sucz : ∀ {g} → suc g ≡ 0 → ⊥
  sucz ()

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  not-not : ∀ b → not (not b) ≡ b
  not-not true  = refl
  not-not false = refl

  0∸ : ∀ v → 0 ∸ v ≡ 0
  0∸ zero    = refl
  0∸ (suc v) = refl

  n∸n : ∀ n → n ∸ n ≡ 0
  n∸n zero    = refl
  n∸n (suc n) = n∸n n

  ∸+0 : ∀ q v → q ∸ (q + v) ≡ 0
  ∸+0 zero    v = 0∸ v
  ∸+0 (suc q) v = ∸+0 q v

  +∸l : ∀ q v → (q + v) ∸ q ≡ v
  +∸l zero    v = refl
  +∸l (suc q) v = +∸l q v

  suc∸ : ∀ d a → a ≤ d → suc d ∸ a ≡ suc (d ∸ a)
  suc∸ d       zero    _       = refl
  suc∸ (suc d) (suc a) (s≤s p) = suc∸ d a p

  ∸suc : ∀ x a → suc a ≤ x → x ∸ a ≡ suc (x ∸ suc a)
  ∸suc (suc x) a (s≤s p) = suc∸ x a p

  m+∸ : ∀ a x → a ≤ x → x ≡ a + (x ∸ a)
  m+∸ zero    x       _       = refl
  m+∸ (suc a) (suc x) (s≤s p) = cong suc (m+∸ a x p)

  ∸-inj : ∀ x a b → a ≤ x → b ≤ x → x ∸ a ≡ x ∸ b → a ≡ b
  ∸-inj x a b pa pb e =
    +-cancelˡ (x ∸ a) a b
      (trans (+-comm (x ∸ a) a)
      (trans (sym (m+∸ a x pa))
      (trans (m+∸ b x pb)
      (trans (cong (b +_) (sym e)) (+-comm b (x ∸ a))))))

  lt→Σ : ∀ x a → x < a → Σ Nat (λ j → a ≡ suc (x + j))
  lt→Σ zero    (suc a) (s≤s _) = a , refl
  lt→Σ (suc x) (suc a) (s≤s p) = let (j , e) = lt→Σ x a p in j , cong suc e

  ≤-+l : ∀ x y → y ≤ x + y
  ≤-+l zero    y = ≤-refl y
  ≤-+l (suc x) y = ≤-suc (≤-+l x y)

  ≤-+ : ∀ x y → x ≤ x + y
  ≤-+ zero    y = z≤n
  ≤-+ (suc x) y = s≤s (≤-+ x y)

  ltY : ∀ x y a → a < x → y < (x + y) ∸ a
  ltY (suc x) y zero    _       = s≤s (≤-+l x y)
  ltY (suc x) y (suc a) (s≤s p) = ltY x y a p

  eqDec : ∀ (a b : Nat) → (a ≡ b) ⊎ (a ≡ b → ⊥)
  eqDec zero    zero    = inj₁ refl
  eqDec zero    (suc b) = inj₂ (λ ())
  eqDec (suc a) zero    = inj₂ (λ ())
  eqDec (suc a) (suc b) with eqDec a b
  ... | inj₁ e  = inj₁ (cong suc e)
  ... | inj₂ ne = inj₂ (λ e → ne (suc-inj e))

  trich : ∀ (a b : Nat) → (a ≡ b → ⊥) → (a < b) ⊎ (b < a)
  trich zero    zero    ne = ⊥-elim (ne refl)
  trich zero    (suc b) _  = inj₁ (s≤s z≤n)
  trich (suc a) zero    _  = inj₂ (s≤s z≤n)
  trich (suc a) (suc b) ne with trich a b (λ e → ne (cong suc e))
  ... | inj₁ p = inj₁ (s≤s p)
  ... | inj₂ p = inj₂ (s≤s p)

  lt-ne : ∀ j n → j < suc n → (j ≡ n → ⊥) → j < n
  lt-ne zero    zero    _        ne = ⊥-elim (ne refl)
  lt-ne zero    (suc n) _        _  = s≤s z≤n
  lt-ne (suc j) zero    (s≤s ()) _
  lt-ne (suc j) (suc n) (s≤s p)  ne = s≤s (lt-ne j n p (λ e → ne (cong suc e)))

  lt-irr : ∀ j → j < j → ⊥
  lt-irr zero    ()
  lt-irr (suc j) (s≤s p) = lt-irr j p

  *0r : ∀ n → n * 0 ≡ 0
  *0r zero    = refl
  *0r (suc n) = *0r n

------------------------------------------------------------------------
-- Disjoint supports.

Dj : ∀ {m} → Vec Nat m → Vec Nat m → Set
Dj []      []      = ⊤
Dj (a ∷ u) (b ∷ v) = (a ≡ 0 ⊎ b ≡ 0) × Dj u v

DjM : ∀ {N M} → Mat N M → Mat N M → Set
DjM []      []      = ⊤
DjM (x ∷ X) (y ∷ Y) = Dj x y × DjM X Y

private
  hdV : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → a ≡ b
  hdV refl = refl

  tlV : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → u ≡ v
  tlV refl = refl

  sw⊎ : ∀ {a b : Nat} → (a ≡ 0 ⊎ b ≡ 0) → (b ≡ 0 ⊎ a ≡ 0)
  sw⊎ (inj₁ e) = inj₂ e
  sw⊎ (inj₂ e) = inj₁ e

  dj+ : ∀ {a b c : Nat} → (a ≡ 0 ⊎ c ≡ 0) → (b ≡ 0 ⊎ c ≡ 0) → (a + b ≡ 0 ⊎ c ≡ 0)
  dj+ (inj₂ e)    _           = inj₂ e
  dj+ (inj₁ refl) (inj₂ e)    = inj₂ e
  dj+ (inj₁ refl) (inj₁ refl) = inj₁ refl

Dj-sym : ∀ {m} (u v : Vec Nat m) → Dj u v → Dj v u
Dj-sym []      []      _       = tt
Dj-sym (a ∷ u) (b ∷ v) (h , s) = sw⊎ h , Dj-sym u v s

Dj-0l : ∀ {m} (v : Vec Nat m) → Dj 0c v
Dj-0l []      = tt
Dj-0l (b ∷ v) = inj₁ refl , Dj-0l v

Dj-0r : ∀ {m} (v : Vec Nat m) → Dj v 0c
Dj-0r v = Dj-sym 0c v (Dj-0l v)

Dj-+l : ∀ {m} (u u′ v : Vec Nat m) → Dj u v → Dj u′ v → Dj (u +c u′) v
Dj-+l []      []       []      _       _         = tt
Dj-+l (a ∷ u) (a′ ∷ u′) (b ∷ v) (h , s) (h′ , s′) = dj+ h h′ , Dj-+l u u′ v s s′

Dj-+r : ∀ {m} (v u u′ : Vec Nat m) → Dj v u → Dj v u′ → Dj v (u +c u′)
Dj-+r v u u′ d d′ = Dj-sym (u +c u′) v (Dj-+l u u′ v (Dj-sym v u d) (Dj-sym v u′ d′))

Dj-⊙l : ∀ {m} a (u v : Vec Nat m) → Dj u v → Dj (a ⊙ u) v
Dj-⊙l zero    u v d = Dj-0l v
Dj-⊙l (suc a) u v d = Dj-+l u (a ⊙ u) v d (Dj-⊙l a u v d)

Dj-⊙ : ∀ {m} a b (u v : Vec Nat m) → Dj u v → Dj (a ⊙ u) (b ⊙ v)
Dj-⊙ a b u v d = Dj-⊙l a u (b ⊙ v) (Dj-sym (b ⊙ v) u (Dj-⊙l b v u (Dj-sym u v d)))

Dj-⊙0 : ∀ {m} a b (u v : Vec Nat m) → (a ≡ 0 ⊎ b ≡ 0) → Dj (a ⊙ u) (b ⊙ v)
Dj-⊙0 a b u v (inj₁ refl) = Dj-0l (b ⊙ v)
Dj-⊙0 a b u v (inj₂ refl) = Dj-0r (a ⊙ u)

-- Supports in two different degrees are disjoint.
Dj-deg : ∀ {m} j j′ (gs u v : Vec Nat m) → SupS (λ h → h ≡ j) gs u → SupS (λ h → h ≡ j′) gs v → (j ≡ j′ → ⊥) → Dj u v
Dj-deg j j′ []       []      []      _         _         ne = tt
Dj-deg j j′ (g ∷ gs) (a ∷ u) (b ∷ v) (h₁ , s₁) (h₂ , s₂) ne = hd h₁ h₂ , Dj-deg j j′ gs u v s₁ s₂ ne
  where
  hd : a ≡ 0 ⊎ g ≡ j → b ≡ 0 ⊎ g ≡ j′ → a ≡ 0 ⊎ b ≡ 0
  hd (inj₁ e)  _         = inj₁ e
  hd (inj₂ _)  (inj₁ e)  = inj₂ e
  hd (inj₂ e₁) (inj₂ e₂) = ⊥-elim (ne (trans (sym e₁) e₂))

DjM-0l : ∀ {N M} (Y : Mat N M) → DjM 0m Y
DjM-0l []      = tt
DjM-0l (y ∷ Y) = Dj-0l y , DjM-0l Y

DjM-0r : ∀ {N M} (Y : Mat N M) → DjM Y 0m
DjM-0r []      = tt
DjM-0r (y ∷ Y) = Dj-0r y , DjM-0r Y

DjM-+l : ∀ {N M} (X Y Z : Mat N M) → DjM X Z → DjM Y Z → DjM (X +m Y) Z
DjM-+l []      []      []      _       _         = tt
DjM-+l (x ∷ X) (y ∷ Y) (z ∷ Z) (h , s) (h′ , s′) = Dj-+l x y z h h′ , DjM-+l X Y Z s s′

DjM-+r : ∀ {N M} (Z X Y : Mat N M) → DjM Z X → DjM Z Y → DjM Z (X +m Y)
DjM-+r []      []      []      _       _         = tt
DjM-+r (z ∷ Z) (x ∷ X) (y ∷ Y) (h , s) (h′ , s′) = Dj-+r z x y h h′ , DjM-+r Z X Y s s′

DjM-outer : ∀ {N M} (f g : Vec Nat N) (x y : Vec Nat M) → (Dj f g ⊎ Dj x y) → DjM (outer f x) (outer g y)
DjM-outer []      []      x y _                = tt
DjM-outer (a ∷ f) (b ∷ g) x y (inj₁ (h , s)) = Dj-⊙0 a b x y h , DjM-outer f g x y (inj₁ s)
DjM-outer (a ∷ f) (b ∷ g) x y (inj₂ d)       = Dj-⊙ a b x y d , DjM-outer f g x y (inj₂ d)

-- The layout keeps disjointness.
private
  Dj-snoc : ∀ {m} (u v : Vec Nat m) a b → Dj u v → (a ≡ 0 ⊎ b ≡ 0) → Dj (snocV u a) (snocV v b)
  Dj-snoc []      []      a b _        h = h , tt
  Dj-snoc (c ∷ u) (e ∷ v) a b (h′ , s) h = h′ , Dj-snoc u v a b s h

  Dj-rev : ∀ {m} (u v : Vec Nat m) → Dj u v → Dj (revV u) (revV v)
  Dj-rev []      []      _       = tt
  Dj-rev (a ∷ u) (b ∷ v) (h , s) = Dj-snoc (revV u) (revV v) a b (Dj-rev u v s) h

  Dj-rv : ∀ {m} c (u v : Vec Nat m) → Dj u v → Dj (rv c u) (rv c v)
  Dj-rv true  u v s = Dj-rev u v s
  Dj-rv false u v s = s

  Dj-++ : ∀ {m n} (u v : Vec Nat m) (u′ v′ : Vec Nat n) → Dj u v → Dj u′ v′ → Dj (u ++V u′) (v ++V v′)
  Dj-++ []      []      u′ v′ _       s′ = s′
  Dj-++ (a ∷ u) (b ∷ v) u′ v′ (h , s) s′ = h , Dj-++ u v u′ v′ s s′

Dj-flat : ∀ {N M} (gs : Vec Nat N) (X Y : Mat N M) → DjM X Y → Dj (flatA gs X) (flatA gs Y)
Dj-flat []       []      []      _       = tt
Dj-flat (g ∷ gs) (x ∷ X) (y ∷ Y) (h , s) =
  Dj-++ (rv (odd g) x) (rv (odd g) y) (flatA gs X) (flatA gs Y) (Dj-rv (odd g) x y h) (Dj-flat gs X Y s)

------------------------------------------------------------------------
-- Truncated differences are pinned down by a disjoint decomposition.

private
  uniq1 : ∀ p q u v → p + u ≡ q + v → (u ≡ 0 ⊎ v ≡ 0) → (q ∸ p ≡ u) × (p ∸ q ≡ v)
  uniq1 p q u v e (inj₁ refl) =
    let pq = trans (sym (+-zero p)) e in
    trans (cong (q ∸_) pq) (∸+0 q v) , trans (cong (_∸ q) pq) (+∸l q v)
  uniq1 p q u v e (inj₂ refl) =
    let qp = trans (sym (+-zero q)) (sym e) in
    trans (cong (_∸ p) qp) (+∸l p u) , trans (cong (p ∸_) qp) (∸+0 p u)

  dj1 : ∀ p m p′ m′ → p + m′ ≡ p′ + m → (m ∸ p ≡ 0) ⊎ (p′ ∸ m′ ≡ 0)
  dj1 zero    zero    p′ m′ e = inj₁ refl
  dj1 (suc p) zero    p′ m′ e = inj₁ refl
  dj1 zero    (suc m) p′ m′ e = inj₂ (trans (cong (p′ ∸_) e) (∸+0 p′ (suc m)))
  dj1 (suc p) (suc m) p′ m′ e = dj1 p m p′ m′ (suc-inj (trans e (+-suc p′ m)))

uniq : ∀ {m} (p q u v : Vec Nat m) → p +c u ≡ q +c v → Dj u v → (q ∸c p ≡ u) × (p ∸c q ≡ v)
uniq []      []      []      []      e _       = refl , refl
uniq (a ∷ p) (b ∷ q) (c ∷ u) (d ∷ v) e (h , s) =
  let (r₁ , r₂) = uniq1 a b c d (hdV e) h
      (t₁ , t₂) = uniq p q u v (tlV e) s
  in cong₂ _∷_ r₁ t₁ , cong₂ _∷_ r₂ t₂

-- (∂c)₋ and (∂c)₊ are disjoint.
Dj-∸ : ∀ {m} (p mm p′ m′ : Vec Nat m) → p +c m′ ≡ p′ +c mm → Dj (mm ∸c p) (p′ ∸c m′)
Dj-∸ []      []       []        []       e = tt
Dj-∸ (a ∷ p) (c ∷ mm) (a′ ∷ p′) (d ∷ m′) e = dj1 a c a′ d (hdV e) , Dj-∸ p mm p′ m′ (tlV e)

------------------------------------------------------------------------
-- Finite sums of matrices.

S : ∀ {N M} → (Nat → Mat N M) → Nat → Mat N M
S f zero    = 0m
S f (suc n) = S f n +m f n

shift : ∀ {N M} → (Nat → Mat N M) → Nat → Mat N M
shift f zero    = 0m
shift f (suc a) = f a

SN : (Nat → Nat) → Nat → Nat
SN f zero    = 0
SN f (suc n) = SN f n + f n

module MatL {N M : Nat} where
  open Solver (matMon N M)

  sw : (A B C : Mat N M) → (A +m B) +m C ≡ (A +m C) +m B
  sw A B C = solve ((` 0 ⊞ ` 1) ⊞ ` 2) ((` 0 ⊞ ` 2) ⊞ ` 1) (lk (A ∷ B ∷ C ∷ [])) tt

  sw2 : (A B C : Mat N M) → (A +m B) +m C ≡ A +m (C +m B)
  sw2 A B C = solve ((` 0 ⊞ ` 1) ⊞ ` 2) (` 0 ⊞ (` 2 ⊞ ` 1)) (lk (A ∷ B ∷ C ∷ [])) tt

  as′ : (A B C : Mat N M) → A +m (B +m C) ≡ (A +m C) +m B
  as′ A B C = solve (` 0 ⊞ (` 1 ⊞ ` 2)) ((` 0 ⊞ ` 2) ⊞ ` 1) (lk (A ∷ B ∷ C ∷ [])) tt

  re4 : (A B C E : Mat N M) → (A +m B) +m (C +m E) ≡ (A +m C) +m (B +m E)
  re4 A B C E = solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) (lk (A ∷ B ∷ C ∷ E ∷ [])) tt

  re5 : (A B C E F : Mat N M) → ((A +m B) +m C) +m (E +m F) ≡ ((A +m C) +m E) +m (B +m F)
  re5 A B C E F = solve (((` 0 ⊞ ` 1) ⊞ ` 2) ⊞ (` 3 ⊞ ` 4)) (((` 0 ⊞ ` 2) ⊞ ` 3) ⊞ (` 1 ⊞ ` 4)) (lk (A ∷ B ∷ C ∷ E ∷ F ∷ [])) tt

  re6 : (A B C E F G : Mat N M) → ((A +m B) +m (C +m E)) +m (F +m G) ≡ ((A +m C) +m F) +m ((B +m E) +m G)
  re6 A B C E F G =
    solve (((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ⊞ (` 4 ⊞ ` 5)) (((` 0 ⊞ ` 2) ⊞ ` 4) ⊞ ((` 1 ⊞ ` 3) ⊞ ` 5)) (lk (A ∷ B ∷ C ∷ E ∷ F ∷ G ∷ [])) tt

  S-ext : ∀ (f g : Nat → Mat N M) n → (∀ a → a < n → f a ≡ g a) → S f n ≡ S g n
  S-ext f g zero    h = refl
  S-ext f g (suc n) h = cong₂ _+m_ (S-ext f g n (λ a p → h a (≤-suc p))) (h n (≤-refl (suc n)))

  S-+ : ∀ (f g : Nat → Mat N M) n → S (λ a → f a +m g a) n ≡ S f n +m S g n
  S-+ f g zero    = sym (+m-id 0m)
  S-+ f g (suc n) = trans (cong (_+m (f n +m g n)) (S-+ f g n)) (re4 (S f n) (S g n) (f n) (g n))

  S-shift : ∀ (f : Nat → Mat N M) n → S (shift f) (suc n) ≡ S f n
  S-shift f zero    = +m-id 0m
  S-shift f (suc n) = cong (_+m f n) (S-shift f n)

  -- Summing termwise equations.
  sumEq : ∀ (P₁ P₂ Q R₁ R₂ T′ : Nat → Mat N M) n →
          (∀ a → a < n → (P₁ a +m P₂ a) +m Q a ≡ (R₁ a +m R₂ a) +m T′ a) →
          (S P₁ n +m S P₂ n) +m S Q n ≡ (S R₁ n +m S R₂ n) +m S T′ n
  sumEq P₁ P₂ Q R₁ R₂ T′ zero    h = refl
  sumEq P₁ P₂ Q R₁ R₂ T′ (suc n) h =
    trans (re6 (S P₁ n) (P₁ n) (S P₂ n) (P₂ n) (S Q n) (Q n))
      (trans (cong₂ _+m_ (sumEq P₁ P₂ Q R₁ R₂ T′ n (λ a p → h a (≤-suc p))) (h n (≤-refl (suc n))))
             (sym (re6 (S R₁ n) (R₁ n) (S R₂ n) (R₂ n) (S T′ n) (T′ n))))

  comb : ∀ (A B C E F A′ B′ C′ E′ F′ : Mat N M) →
         (A +m C) +m E ≡ (A′ +m C′) +m E′ → B +m F ≡ B′ +m F′ →
         ((A +m B) +m C) +m (E +m F) ≡ ((A′ +m B′) +m C′) +m (E′ +m F′)
  comb A B C E F A′ B′ C′ E′ F′ h₁ h₂ =
    trans (re5 A B C E F) (trans (cong₂ _+m_ h₁ h₂) (sym (re5 A′ B′ C′ E′ F′)))

  DjM-S : ∀ (f g : Nat → Mat N M) n n′ → (∀ a b → a < n → b < n′ → DjM (f a) (g b)) → DjM (S f n) (S g n′)
  DjM-S f g zero    n′ h = DjM-0l (S g n′)
  DjM-S f g (suc n) n′ h =
    DjM-+l (S f n) (f n) (S g n′) (DjM-S f g n n′ (λ a b p q → h a b (≤-suc p) q)) (inner n′ (λ b q → h n b (≤-refl (suc n)) q))
    where
    inner : ∀ m → (∀ b → b < m → DjM (f n) (g b)) → DjM (f n) (S g m)
    inner zero    h′ = DjM-0r (f n)
    inner (suc m) h′ = DjM-+r (f n) (S g m) (g m) (inner m (λ b q → h′ b (≤-suc q))) (h′ m (≤-refl (suc m)))

  ----------------------------------------------------------------------
  -- The termwise equations, with the chains left abstract.

  E1 : ∀ (a b c d : Vec Nat N) (y : Vec Nat M) → a +c b ≡ c +c d → outer a y +m outer b y ≡ outer c y +m outer d y
  E1 a b c d y h = trans (sym (outer-+l a b y)) (trans (cong (λ z → outer z y) h) (outer-+l c d y))

  E2 : ∀ (u : Vec Nat N) (a b c d : Vec Nat M) → a +c b ≡ c +c d → outer u a +m outer u b ≡ outer u c +m outer u d
  E2 u a b c d h = trans (sym (outer-+r u a b)) (trans (cong (outer u) h) (outer-+r u c d))

  -- a = 0: only the L-boundary of ⟨x⟩_0 ⊗ ⟨y⟩_d contributes.
  edge0L : ∀ p α (Xf : Bool → Vec Nat N) (dv Yv : Bool → Vec Nat M) → Xf true ≡ Xf false →
           dv true +c Yv false ≡ dv false +c Yv true →
           (0m +m outer (Xf α) (dv (sg p true))) +m outer (Xf false) (Yv (sg p false)) ≡
           (0m +m outer (Xf α) (dv (sg p false))) +m outer (Xf true) (Yv (sg p true))
  edge0L p α Xf dv Yv e h₂ =
    trans (cong (_+m outer (Xf false) (Yv (sg p false))) (trans (+m-id _) (cong (λ f → outer f (dv (sg p true))) (Xα α))))
      (trans (core p (Xf false))
        (sym (cong₂ _+m_ (trans (+m-id _) (cong (λ f → outer f (dv (sg p false))) (Xα α))) (cong (λ f → outer f (Yv (sg p true))) e))))
    where
    Xα : ∀ γ → Xf γ ≡ Xf false
    Xα true  = e
    Xα false = refl
    core : ∀ p u → outer u (dv (sg p true)) +m outer u (Yv (sg p false)) ≡ outer u (dv (sg p false)) +m outer u (Yv (sg p true))
    core true  u = E2 u (dv true) (Yv false) (dv false) (Yv true) h₂
    core false u = sym (E2 u (dv true) (Yv false) (dv false) (Yv true) h₂)

  -- 0 < a ≤ deg x: the parity flips between a − 1 and a.
  flipL : ∀ p p₀ α → p₀ ≡ not p → (a⁺ a⁻ : Vec Nat N) (Xf : Bool → Vec Nat N) (dv Yv : Bool → Vec Nat M) →
          a⁺ +c Xf false ≡ a⁻ +c Xf true → dv true +c Yv false ≡ dv false +c Yv true →
          (outer a⁺ (Yv (sg p₀ α)) +m outer (Xf α) (dv (sg p true))) +m outer (Xf false) (Yv (sg p false)) ≡
          (outer a⁻ (Yv (sg p₀ α)) +m outer (Xf α) (dv (sg p false))) +m outer (Xf true) (Yv (sg p true))
  flipL true .false true refl a⁺ a⁻ Xf dv Yv h₁ h₂ =
    trans (sw (outer a⁺ (Yv false)) (outer (Xf true) (dv true)) (outer (Xf false) (Yv false)))
    (trans (cong (_+m outer (Xf true) (dv true)) (E1 a⁺ (Xf false) a⁻ (Xf true) (Yv false) h₁))
    (trans (sw2 (outer a⁻ (Yv false)) (outer (Xf true) (Yv false)) (outer (Xf true) (dv true)))
    (trans (cong (outer a⁻ (Yv false) +m_) (E2 (Xf true) (dv true) (Yv false) (dv false) (Yv true) h₂))
           (sym (+m-assoc (outer a⁻ (Yv false)) (outer (Xf true) (dv false)) (outer (Xf true) (Yv true)))))))
  flipL true .false false refl a⁺ a⁻ Xf dv Yv h₁ h₂ =
    trans (+m-assoc (outer a⁺ (Yv true)) (outer (Xf false) (dv true)) (outer (Xf false) (Yv false)))
    (trans (cong (outer a⁺ (Yv true) +m_) (E2 (Xf false) (dv true) (Yv false) (dv false) (Yv true) h₂))
    (trans (as′ (outer a⁺ (Yv true)) (outer (Xf false) (dv false)) (outer (Xf false) (Yv true)))
    (trans (cong (_+m outer (Xf false) (dv false)) (E1 a⁺ (Xf false) a⁻ (Xf true) (Yv true) h₁))
           (sw (outer a⁻ (Yv true)) (outer (Xf true) (Yv true)) (outer (Xf false) (dv false))))))
  flipL false .true true refl a⁺ a⁻ Xf dv Yv h₁ h₂ =
    trans (sw (outer a⁺ (Yv true)) (outer (Xf true) (dv false)) (outer (Xf false) (Yv true)))
    (trans (cong (_+m outer (Xf true) (dv false)) (E1 a⁺ (Xf false) a⁻ (Xf true) (Yv true) h₁))
    (trans (sw2 (outer a⁻ (Yv true)) (outer (Xf true) (Yv true)) (outer (Xf true) (dv false)))
    (trans (cong (outer a⁻ (Yv true) +m_) (sym (E2 (Xf true) (dv true) (Yv false) (dv false) (Yv true) h₂)))
           (sym (+m-assoc (outer a⁻ (Yv true)) (outer (Xf true) (dv true)) (outer (Xf true) (Yv false)))))))
  flipL false .true false refl a⁺ a⁻ Xf dv Yv h₁ h₂ =
    trans (+m-assoc (outer a⁺ (Yv false)) (outer (Xf false) (dv false)) (outer (Xf false) (Yv true)))
    (trans (cong (outer a⁺ (Yv false) +m_) (sym (E2 (Xf false) (dv true) (Yv false) (dv false) (Yv true) h₂)))
    (trans (as′ (outer a⁺ (Yv false)) (outer (Xf false) (dv true)) (outer (Xf false) (Yv false)))
    (trans (cong (_+m outer (Xf false) (dv true)) (E1 a⁺ (Xf false) a⁻ (Xf true) (Yv false) h₁))
           (sw (outer a⁻ (Yv false)) (outer (Xf true) (Yv false)) (outer (Xf false) (dv true))))))

  -- a > deg x: ⟨x⟩_a = 0, and ∂⁺⟨x⟩_{a−1} = ∂⁻⟨x⟩_{a−1}.
  zeroL : ∀ (a⁺ a⁻ : Vec Nat N) (Xf : Bool → Vec Nat N) α (W z₁ z₂ z₃ z₄ : Vec Nat M) → (∀ γ → Xf γ ≡ 0c) →
          a⁺ +c Xf false ≡ a⁻ +c Xf true →
          (outer a⁺ W +m outer (Xf α) z₁) +m outer (Xf false) z₂ ≡ (outer a⁻ W +m outer (Xf α) z₃) +m outer (Xf true) z₄
  zeroL a⁺ a⁻ Xf α W z₁ z₂ z₃ z₄ z h₁ =
    trans (cong₂ _+m_ (cong₂ _+m_ (cong (λ f → outer f W) ea) (o0 α z₁)) (o0 false z₂))
          (sym (cong₂ _+m_ (cong₂ _+m_ refl (o0 α z₃)) (o0 true z₄)))
    where
    o0 : ∀ γ y → outer (Xf γ) y ≡ 0m
    o0 γ y = trans (cong (λ f → outer f y) (z γ)) (outer-0l y)
    ea : a⁺ ≡ a⁻
    ea = +c-cancel a⁺ a⁻ 0c (trans (cong (a⁺ +c_) (sym (z false))) (trans h₁ (cong (a⁻ +c_) (z true))))

  -- a = d + 1: only the K-boundary of ⟨x⟩_d ⊗ ⟨y⟩_0 contributes.
  lastL : ∀ (a⁺ a⁻ P Q : Vec Nat N) (Yv : Bool → Vec Nat M) (u : Vec Nat M) → (∀ γ → Yv γ ≡ u) →
          a⁺ +c Q ≡ a⁻ +c P → ∀ s₁ s₂ s₃ →
          outer a⁺ (Yv s₁) +m outer Q (Yv s₂) ≡ outer a⁻ (Yv s₁) +m outer P (Yv s₃)
  lastL a⁺ a⁻ P Q Yv u hY h₁ s₁ s₂ s₃ =
    trans (cong₂ (λ y y′ → outer a⁺ y +m outer Q y′) (hY s₁) (hY s₂))
      (trans (E1 a⁺ Q a⁻ P u h₁) (sym (cong₂ (λ y y′ → outer a⁻ y +m outer P y′) (hY s₁) (hY s₃))))

open MatL public

augM-S : ∀ {N M} (gK : Vec Nat N) (gL : Vec Nat M) (f : Nat → Mat N M) n → augM gK gL (S f n) ≡ SN (λ a → augM gK gL (f a)) n
augM-S gK gL f zero    = augM-0 gK gL
augM-S gK gL f (suc n) = trans (augM-+ gK gL (S f n) (f n)) (cong (_+ augM gK gL (f n)) (augM-S gK gL f n))

private
  SN-zero : ∀ (f : Nat → Nat) n → (∀ a → a < n → f a ≡ 0) → SN f n ≡ 0
  SN-zero f zero    h = refl
  SN-zero f (suc n) h = cong₂ _+_ (SN-zero f n (λ a p → h a (≤-suc p))) (h n (≤-refl (suc n)))

  SN-one : ∀ (f : Nat → Nat) n j → j < n → (∀ a → a < n → (a ≡ j → ⊥) → f a ≡ 0) → SN f n ≡ f j
  SN-one f (suc n) j jn z with eqDec j n
  ... | inj₁ refl = cong (_+ f j) (SN-zero f j (λ a p → z a (≤-suc p) (λ e → lt-irr j (subst (_< j) e p))))
  ... | inj₂ ne   =
    trans (cong₂ _+_ (SN-one f n j (lt-ne j n jn ne) (λ a p ne′ → z a (≤-suc p) ne′)) (z n (≤-refl (suc n)) (λ e → ne (sym e))))
          (+-zero (f j))

------------------------------------------------------------------------
-- The atoms of one basis.

module AtomF {N : Nat} (B : Basis N) (H : Hyp B) (dgp : DegP B) (dgm : DegM B) (k : Nat) (kN : k < N) where
  private
    module B = Basis B
  open Atom B using (entK; step; Bd⁻; Bd⁺)
  open Atom.Cells B (Hyp.dd H) using (Inv-entK)
  open Atom.Cells.Deg B (Hyp.dd H) (Hyp.deg-dp H) (Hyp.deg-dm H) using (deg-entK)

  bB : Bool → Vec (Vec Nat N) N
  bB true  = B.bplus
  bB false = B.bminus

  dx : Nat
  dx = at 0 B.gdeg k

  pick : Bool → Vec Nat N × Vec Nat N → Vec Nat N
  pick α c = if α then snd c else fst c

  -- ⟨k⟩^α at depth a.
  E : Bool → Nat → Vec Nat N
  E α a = pick α (entK k a)

  E0 : ∀ α → E α 0 ≡ unit k
  E0 true  = refl
  E0 false = refl

  Bd : ∀ α a → lin (E α a) B.bplus +c E false (suc a) ≡ lin (E α a) B.bminus +c E true (suc a)
  Bd false a = Bd⁻ (entK k a) (Inv-entK k a)
  Bd true  a = Bd⁺ (entK k a) (Inv-entK k a)

  Djs : ∀ a → Dj (E false (suc a)) (E true (suc a))
  Djs a = Dj-∸ (lin (fst (entK k a)) B.bplus) (lin (fst (entK k a)) B.bminus)
               (lin (snd (entK k a)) B.bplus) (lin (snd (entK k a)) B.bminus) (Inv-entK k a)

  supp : ∀ α a → a ≤ dx → SupS (λ h → h ≡ dx ∸ a) B.gdeg (E α a)
  supp false a l = prj→SupS (dx ∸ a) B.gdeg (E false a) (fst (deg-entK k a (dx ∸ a) (m+∸ a dx l)))
  supp true  a l = prj→SupS (dx ∸ a) B.gdeg (E true a) (snd (deg-entK k a (dx ∸ a) (m+∸ a dx l)))

  augE : ∀ α → augm B.gdeg (E α dx) ≡ 1
  augE false = fst (Hyp.unital H k kN)
  augE true  = snd (Hyp.unital H k kN)

  private
    SupS-none : ∀ {m} P (gs w : Vec Nat m) → SupS P gs w → (∀ g → P g → ⊥) → w ≡ 0c
    SupS-none P []       []      s       n = refl
    SupS-none P (g ∷ gs) (a ∷ w) (h , s) n = cong₂ _∷_ (hd h) (SupS-none P gs w s n)
      where
      hd : a ≡ 0 ⊎ P g → a ≡ 0
      hd (inj₁ e) = e
      hd (inj₂ p) = ⊥-elim (n g p)

    dg : ∀ β → zipV (degFix B) B.gdeg (bB β) ≡ bB β
    dg true  = dgp
    dg false = dgm

    row0 : ∀ β k′ → at 0 B.gdeg k′ ≡ 0 → at 0c (bB β) k′ ≡ 0c
    row0 β k′ e =
      SupS-none (λ g → suc g ≡ at 0 B.gdeg k′) B.gdeg (at 0c (bB β) k′)
        (Sup→SupS (λ g → suc g ≡ at 0 B.gdeg k′) B.gdeg (at 0c (bB β) k′) (supFix B (bB β) (dg β) k′))
        (λ g p → sucz (trans p e))

    lin-vanish : ∀ {m n} P (gs : Vec Nat m) (v : Vec Nat m) (vs : Vec (Vec Nat n) m) → SupS P gs v →
                 (∀ i → P (at 0 gs i) → at 0c vs i ≡ 0c) → lin v vs ≡ 0c
    lin-vanish P []       []      []       s       z = refl
    lin-vanish P (g ∷ gs) (a ∷ v) (w ∷ ws) (h , s) z =
      trans (cong₂ _+c_ (hd h) (lin-vanish P gs v ws s (λ i → z (suc i)))) (+c-id 0c)
      where
      hd : a ≡ 0 ⊎ P g → a ⊙ w ≡ 0c
      hd (inj₁ refl) = refl
      hd (inj₂ p)    = trans (cong (a ⊙_) (z 0 p)) (⊙-0c a)

    d0 : ∀ β v → SupS (λ h → h ≡ 0) B.gdeg v → lin v (bB β) ≡ 0c
    d0 β v s = lin-vanish (λ h → h ≡ 0) B.gdeg v (bB β) s (λ i e → row0 β i e)

    ∸c00 : ∀ {m} → (0c {m}) ∸c 0c ≡ 0c
    ∸c00 {zero}  = refl
    ∸c00 {suc m} = cong (0 ∷_) (∸c00 {m})

    st0 : step (0c , 0c) ≡ (0c , 0c)
    st0 = cong₂ _,_ (trans (cong₂ _∸c_ (lin-0 B.bminus) (lin-0 B.bplus)) ∸c00)
                    (trans (cong₂ _∸c_ (lin-0 B.bplus) (lin-0 B.bminus)) ∸c00)

    s0 : ∀ α → SupS (λ h → h ≡ 0) B.gdeg (E α dx)
    s0 α = subst (λ j → SupS (λ h → h ≡ j) B.gdeg (E α dx)) (n∸n dx) (supp α dx (≤-refl dx))

    z1 : entK k (suc dx) ≡ (0c , 0c)
    z1 = cong₂ _,_ (trans (cong₂ _∸c_ (d0 false (E false dx) (s0 false)) (d0 true (E false dx) (s0 false))) ∸c00)
                   (trans (cong₂ _∸c_ (d0 true (E true dx) (s0 true)) (d0 false (E true dx) (s0 true))) ∸c00)

  -- Below the bottom of the atom, everything vanishes.
  zX : ∀ j → entK k (suc (dx + j)) ≡ (0c , 0c)
  zX zero    = trans (cong (λ n → entK k (suc n)) (+-zero dx)) z1
  zX (suc j) = trans (cong (λ n → entK k (suc n)) (+-suc dx j)) (trans (cong step (zX j)) st0)

  zE : ∀ α a → dx < a → E α a ≡ 0c
  zE α a p with lt→Σ dx a p
  ... | (j , refl) = trans (cong (pick α) (zX j)) (pk α)
    where
    pk : ∀ α → pick α (0c , 0c) ≡ 0c
    pk true  = refl
    pk false = refl

  -- ⟨k⟩_a sits in degree deg k − a.
  suppAll : ∀ α a k′ → at 0 (E α a) k′ ≡ 0 ⊎ even (at 0 B.gdeg k′) ≡ even (dx ∸ a)
  suppAll α a k′ with ≤-dec a dx
  ... | inj₁ l = cs (SupS→Sup (λ h → h ≡ dx ∸ a) B.gdeg (E α a) (supp α a l) k′)
    where
    cs : at 0 (E α a) k′ ≡ 0 ⊎ at 0 B.gdeg k′ ≡ dx ∸ a → at 0 (E α a) k′ ≡ 0 ⊎ even (at 0 B.gdeg k′) ≡ even (dx ∸ a)
    cs (inj₁ z) = inj₁ z
    cs (inj₂ e) = inj₂ (cong even e)
  ... | inj₂ p = inj₁ (trans (cong (λ w → at 0 w k′) (zE α a p)) (at-0c {N} k′))

------------------------------------------------------------------------
-- The atoms of K ⊗ L.

module TensorUnit {N M : Nat} (B : Basis N) (C : Basis M) (HB : Hyp B) (HC : Hyp C)
                  (dgpB : DegP B) (dgmB : DegM B) (dgpC : DegP C) (dgmC : DegM C) where
  open Tensor B C
  open TensorAll B C HB HC dgpB dgmB dgpC dgmC
  open TensorOrd B C HB HC using (gen⊗)
  private
    module B = Basis B
    module C = Basis C
    gK = B.gdeg
    gL = C.gdeg

  dK : Bool → Vec Nat N → Vec Nat N
  dK β f = lin f (bK β)

  dL : Bool → Vec Nat M → Vec Nat M
  dL γ v = lin v (bL γ)

  private
    S-D : ∀ β (f : Nat → Mat N M) n → D β (S f n) ≡ S (λ a → D β (f a)) n
    S-D β f zero    = D-0 β
    S-D β f (suc n) = trans (D-+ β (S f n) (f n)) (cong (_+m D β (f n)) (S-D β f n))

    σ : ∀ p β → sg (not p) (not β) ≡ sg p β
    σ true  β = not-not β
    σ false β = refl

  module Pair (k l : Nat) (kN : k < N) (lM : l < M) where
    module Kx = AtomF B HB dgpB dgmB k kN
    module Ly = AtomF C HC dgpC dgmC l lM
    module A⊗ = Atom B⊗

    dx dy : Nat
    dx = Kx.dx
    dy = Ly.dx

    par : Nat → Bool
    par a = even (dx ∸ a)

    -- The terms of Steiner's formula at depth d.
    Tm : Bool → Nat → Nat → Mat N M
    Tm α d a = outer (Kx.E α a) (Ly.E (sg (par a) α) (d ∸ a))

    F : Bool → Nat → Mat N M
    F α d = S (Tm α d) (suc d)

    G1 G2 : Bool → Bool → Nat → Nat → Mat N M
    G1 β α d a = outer (dK β (Kx.E α a)) (Ly.E (sg (par a) α) (d ∸ a))
    G2 β α d a = outer (Kx.E α a) (dL (sg (par a) β) (Ly.E (sg (par a) α) (d ∸ a)))

    -- D on one term: the Koszul sign is the parity of deg x − a.
    Dhom : ∀ β α a (v : Vec Nat M) →
           D β (outer (Kx.E α a) v) ≡ outer (dK β (Kx.E α a)) v +m outer (Kx.E α a) (dL (sg (par a) β) v)
    Dhom β α a v =
      cong₂ _+m_ (osum-outer (bK β) (Kx.E α a) v)
        (trans (outer-row gK bL β (Kx.E α a) v (not (par a)) sp)
               (cong (λ s → outer (Kx.E α a) (lin v (bL s))) (σ (par a) β)))
      where
      sp : ∀ k′ → at 0 (Kx.E α a) k′ ≡ 0 ⊎ even (at 0 gK k′) ≡ not (not (par a))
      sp k′ with Kx.suppAll α a k′
      ... | inj₁ z = inj₁ z
      ... | inj₂ e = inj₂ (trans e (sym (not-not (par a))))

    DF : ∀ β α d → D β (F α d) ≡ S (shift (G1 β α d)) (suc (suc d)) +m S (G2 β α d) (suc d)
    DF β α d =
      trans (S-D β (Tm α d) (suc d))
        (trans (S-ext (λ a → D β (Tm α d a)) (λ a → G1 β α d a +m G2 β α d a) (suc d) (λ a _ → Dhom β α a _))
          (trans (S-+ (G1 β α d) (G2 β α d) (suc d))
                 (cong (_+m S (G2 β α d) (suc d)) (sym (S-shift (G1 β α d) (suc d))))))

    parflip : ∀ a → suc a ≤ dx → par a ≡ not (par (suc a))
    parflip a p = trans (cong even (∸suc dx a p)) (even-suc (dx ∸ suc a))

    Pt : ∀ α d a → a < suc d →
         (shift (G1 true α d) a +m G2 true α d a) +m Tm false (suc d) a ≡
         (shift (G1 false α d) a +m G2 false α d a) +m Tm true (suc d) a
    Pt α d zero _ =
      edge0L (par 0) α (λ γ → Kx.E γ 0) (λ γ → dL γ (Ly.E (sg (par 0) α) d)) (λ γ → Ly.E γ (suc d)) refl
             (Ly.Bd (sg (par 0) α) d)
    Pt α d (suc a) (s≤s ad) with ≤-dec (suc a) dx
    ... | inj₁ ax =
      flipL (par (suc a)) (par a) α (parflip a ax) (dK true (Kx.E α a)) (dK false (Kx.E α a))
            (λ γ → Kx.E γ (suc a)) (λ γ → dL γ V) (λ γ → Ly.E γ (d ∸ a))
            (Kx.Bd α a)
            (subst (λ n → dL true V +c Ly.E false n ≡ dL false V +c Ly.E true n) (sym (∸suc d a ad))
                   (Ly.Bd (sg (par (suc a)) α) (d ∸ suc a)))
      where
      V = Ly.E (sg (par (suc a)) α) (d ∸ suc a)
    ... | inj₂ xa =
      zeroL (dK true (Kx.E α a)) (dK false (Kx.E α a)) (λ γ → Kx.E γ (suc a)) α _ _ _ _ _
            (λ γ → Kx.zE γ (suc a) xa) (Kx.Bd α a)

    Lt : ∀ α d → shift (G1 true α d) (suc d) +m Tm false (suc d) (suc d) ≡
                 shift (G1 false α d) (suc d) +m Tm true (suc d) (suc d)
    Lt α d =
      lastL (dK true (Kx.E α d)) (dK false (Kx.E α d)) (Kx.E true (suc d)) (Kx.E false (suc d))
            (λ γ → Ly.E γ (d ∸ d)) (unit l) (λ γ → trans (cong (Ly.E γ) (n∸n d)) (Ly.E0 γ)) (Kx.Bd α d) _ _ _

    -- ∂⁺F_d + F⁻_{d+1} = ∂⁻F_d + F⁺_{d+1}.
    EqC : ∀ α d → D true (F α d) +m F false (suc d) ≡ D false (F α d) +m F true (suc d)
    EqC α d =
      trans (cong (_+m F false (suc d)) (DF true α d))
        (trans (comb (S (shift (G1 true α d)) (suc d)) (shift (G1 true α d) (suc d)) (S (G2 true α d) (suc d))
                     (S (Tm false (suc d)) (suc d)) (Tm false (suc d) (suc d))
                     (S (shift (G1 false α d)) (suc d)) (shift (G1 false α d) (suc d)) (S (G2 false α d) (suc d))
                     (S (Tm true (suc d)) (suc d)) (Tm true (suc d) (suc d))
                     (sumEq (shift (G1 true α d)) (G2 true α d) (Tm false (suc d))
                            (shift (G1 false α d)) (G2 false α d) (Tm true (suc d)) (suc d) (Pt α d))
                     (Lt α d))
          (sym (cong (_+m F true (suc d)) (DF false α d))))

    -- F⁻_{d+1} and F⁺_{d+1} are disjoint.
    djX : ∀ a b → (a ≡ b → ⊥) → Dj (Kx.E false a) (Kx.E true b)
    djX a b ne with ≤-dec a dx | ≤-dec b dx
    ... | inj₁ la | inj₁ lb =
      Dj-deg (dx ∸ a) (dx ∸ b) gK (Kx.E false a) (Kx.E true b) (Kx.supp false a la) (Kx.supp true b lb)
             (λ e → ne (∸-inj dx a b la lb e))
    ... | inj₂ xa | _       = subst (λ w → Dj w (Kx.E true b)) (sym (Kx.zE false a xa)) (Dj-0l (Kx.E true b))
    ... | inj₁ _  | inj₂ xb = subst (λ w → Dj (Kx.E false a) w) (sym (Kx.zE true b xb)) (Dj-0r (Kx.E false a))

    djY : ∀ p n → Dj (Ly.E (sg p false) (suc n)) (Ly.E (sg p true) (suc n))
    djY true  n = Ly.Djs n
    djY false n = Dj-sym (Ly.E false (suc n)) (Ly.E true (suc n)) (Ly.Djs n)

    djEq : ∀ n a → DjM (Tm false (suc n) a) (Tm true (suc n) a)
    djEq n zero    = DjM-outer _ _ _ _ (inj₂ (djY (par 0) n))
    djEq n (suc a) = DjM-outer _ _ _ _ (inj₁ (Kx.Djs a))

    djT : ∀ n a b → DjM (Tm false (suc n) a) (Tm true (suc n) b)
    djT n a b with eqDec a b
    ... | inj₁ refl = djEq n a
    ... | inj₂ ne   = DjM-outer _ _ _ _ (inj₁ (djX a b ne))

    DjF : ∀ n → DjM (F false (suc n)) (F true (suc n))
    DjF n = DjM-S (Tm false (suc n)) (Tm true (suc n)) (suc (suc n)) (suc (suc n)) (λ a b _ _ → djT n a b)

    -- Steiner's formula.
    dflat : ∀ α (Y : Mat N M) → lin (flatA gK Y) (flatA gK (fam α)) ≡ flatA gK (D α Y)
    dflat α Y = trans (d⊗ α (flatA gK Y)) (cong (λ Z → flatA gK (D α Z)) (unflat-flat gK Y))

    eqn : ∀ α d → lin (flatA gK (F α d)) (flatA gK (fam true)) +c flatA gK (F false (suc d)) ≡
                  lin (flatA gK (F α d)) (flatA gK (fam false)) +c flatA gK (F true (suc d))
    eqn α d =
      trans (cong (_+c flatA gK (F false (suc d))) (dflat true (F α d)))
      (trans (sym (flat-+ gK (D true (F α d)) (F false (suc d))))
      (trans (cong (flatA gK) (EqC α d))
      (trans (flat-+ gK (D false (F α d)) (F true (suc d)))
             (cong (_+c flatA gK (F true (suc d))) (sym (dflat false (F α d)))))))

    entF : ∀ i → flatA gK (outer (unit {N} k) (unit {M} l)) ≡ unit {N * M} i →
           ∀ d → A⊗.entK i d ≡ (flatA gK (F false d) , flatA gK (F true d))
    entF i ef zero = cong₂ _,_ (sym (base false)) (sym (base true))
      where
      base : ∀ α → flatA gK (F α 0) ≡ unit i
      base α = trans (cong (flatA gK) (trans (+m-id _) (cong₂ outer (Kx.E0 α) (Ly.E0 (sg (par 0) α))))) ef
    entF i ef (suc d) =
      trans (cong A⊗.step (entF i ef d))
        (cong₂ _,_
          (fst (uniq (lin (flatA gK (F false d)) (flatA gK (fam true))) (lin (flatA gK (F false d)) (flatA gK (fam false)))
                     (flatA gK (F false (suc d))) (flatA gK (F true (suc d))) (eqn false d) dj))
          (snd (uniq (lin (flatA gK (F true d)) (flatA gK (fam true))) (lin (flatA gK (F true d)) (flatA gK (fam false)))
                     (flatA gK (F false (suc d))) (flatA gK (F true (suc d))) (eqn true d) dj)))
      where
      dj = Dj-flat gK (F false (suc d)) (F true (suc d)) (DjF d)

    -- At the bottom only a = deg x survives.
    augF : ∀ α → augm gdeg⊗ (flatA gK (F α (dx + dy))) ≡ 1
    augF α =
      trans (augm-flat (F α (dx + dy)))
      (trans (augM-S gK gL (Tm α (dx + dy)) (suc (dx + dy)))
      (trans (SN-one (λ a → augM gK gL (Tm α (dx + dy) a)) (suc (dx + dy)) dx (s≤s (≤-+ dx dy)) others)
      (trans (augM-outer gK gL (Kx.E α dx) (Ly.E (sg (par dx) α) ((dx + dy) ∸ dx)))
             (cong₂ _*_ (Kx.augE α)
                        (trans (cong (λ n → augm gL (Ly.E (sg (par dx) α) n)) (+∸l dx dy)) (Ly.augE (sg (par dx) α)))))))
      where
      others : ∀ a → a < suc (dx + dy) → (a ≡ dx → ⊥) → augM gK gL (Tm α (dx + dy) a) ≡ 0
      others a _ ne with trich a dx ne
      ... | inj₁ ax =
        trans (augM-outer gK gL (Kx.E α a) (Ly.E (sg (par a) α) ((dx + dy) ∸ a)))
          (trans (cong (λ w → augm gK (Kx.E α a) * augm gL w) (Ly.zE (sg (par a) α) ((dx + dy) ∸ a) (ltY dx dy a ax)))
          (trans (cong (augm gK (Kx.E α a) *_) (augm-0 gL)) (*0r (augm gK (Kx.E α a)))))
      ... | inj₂ xa =
        trans (augM-outer gK gL (Kx.E α a) (Ly.E (sg (par a) α) ((dx + dy) ∸ a)))
          (trans (cong (λ w → augm gK w * augm gL (Ly.E (sg (par a) α) ((dx + dy) ∸ a))) (Kx.zE α a xa))
                 (cong (_* augm gL (Ly.E (sg (par a) α) ((dx + dy) ∸ a))) (augm-0 gK)))

    unitalPair : ∀ i → flatA gK (outer (unit {N} k) (unit {M} l)) ≡ unit {N * M} i → at 0 gdeg⊗ i ≡ dx + dy →
                 Atom.Cells.Deg.Unital B⊗ dd′ deg-dp′ deg-dm′ i
    unitalPair i ef eg =
      trans (cong (λ n → augm gdeg⊗ (fst (A⊗.entK i n))) eg)
            (trans (cong (λ c → augm gdeg⊗ (fst c)) (entF i ef (dx + dy))) (augF false)) ,
      trans (cong (λ n → augm gdeg⊗ (snd (A⊗.entK i n))) eg)
            (trans (cong (λ c → augm gdeg⊗ (snd c)) (entF i ef (dx + dy))) (augF true))

  -- Every atom of K ⊗ L is unital.
  unital⊗ : ∀ i → i < N * M → Atom.Cells.Deg.Unital B⊗ dd′ deg-dp′ deg-dm′ i
  unital⊗ i iNM with gen⊗ i iNM
  ... | (k , l , kN , lM , ef , eg) = Pair.unitalPair k l kN lM i ef eg

  -- K ⊗ L satisfies the hypotheses of `Generation`.
  Hyp⊗ : Hyp B⊗
  Hyp⊗ = hyp⊗ unital⊗

------------------------------------------------------------------------
-- Instances: the general theorem, applied (DegP, DegM by computation).

module _ where
  open import CaTTExp.Strict.BasisCheck using (BD¹; BD²; hyp-D¹; hyp-D²)

  D¹⊗D²-hyp : Hyp (TensorLay.B⊗ BD¹ BD²)
  D¹⊗D²-hyp = TensorUnit.Hyp⊗ BD¹ BD² hyp-D¹ hyp-D² refl refl refl refl

  D²⊗D²-hyp : Hyp (TensorLay.B⊗ BD² BD²)
  D²⊗D²-hyp = TensorUnit.Hyp⊗ BD² BD² hyp-D² hyp-D² refl refl refl refl
