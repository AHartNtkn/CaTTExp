------------------------------------------------------------------------
-- Functors that kill a set of generators (ledger A5, (N3), collapse
-- step 3).
--
-- Let E be a set of basis elements closed under ∂ (the boundaries of an
-- element of E are supported on E), and F : ν(K) → 𝒟 a strict functor
-- sending each atom ⟨e⟩, e ∈ E, to a 0-cell. Then F sends every cell
-- whose rows above r are supported on E to a cell of dimension ≤ r:
--
--   kill : AboveE r x → F x ≡ src r (F x).
--
-- (Induction on a generation of x by atoms: an atom with a row above r
-- has its top generator in E; for a composite x #ₙ y the rows of x and
-- y above r are again supported on E, using the boundary condition at
-- the composition level when n > r; and in 𝒟 a composite of cells of
-- dimension ≤ r has dimension ≤ r by the axioms.) For the Gray
-- cylinder, E is the set of end elements k ⊗ 0, k ⊗ 1.
------------------------------------------------------------------------
module CaTTExp.Strict.Kill where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.Generation
open import CaTTExp.Strict.NuRows using (module TabAt; module Rows)
open import CaTTExp.Strict.Bag using (+-zero)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

private
  +-0 : ∀ a b → a + b ≡ 0 → (a ≡ 0) × (b ≡ 0)
  +-0 zero    b e = refl , e
  +-0 (suc a) b ()

-- A chain supported on E.
SE : ∀ {m} → (Nat → Bool) → Vec Nat m → Set
SE E u = ∀ d → E d ≡ false → at0 u d ≡ 0

SE-+ : ∀ {m} E (u v : Vec Nat m) → SE E (u +c v) → SE E u × SE E v
SE-+ E u v h = (λ d e → fst (+-0 _ _ (trans (sym (at-+c u v d)) (h d e)))) ,
               (λ d e → snd (+-0 _ _ (trans (sym (at-+c u v d)) (h d e))))

SE-+′ : ∀ {m} E (u v : Vec Nat m) → SE E u → SE E v → SE E (u +c v)
SE-+′ E u v hu hv d e = trans (at-+c u v d) (cong₂ _+_ (hu d e) (hv d e))

SE-0 : ∀ {m} E → SE E (0c {m})
SE-0 {m} E d _ = at-0c {m} d

private
  at0-⊙ : ∀ {m} k (v : Vec Nat m) d → at0 v d ≡ 0 → at0 (k ⊙ v) d ≡ 0
  at0-⊙ {m} zero    v d e = at-0c {m} d
  at0-⊙ (suc k) v d e = trans (at-+c v (k ⊙ v) d) (cong₂ _+_ e (at0-⊙ k v d e))

-- lin u vs is supported on E when every column used by u is.
SE-lin : ∀ {M m} E (P : Nat → Bool) (u : Vec Nat m) (vs : Vec (Vec Nat M) m) →
         (∀ i → P i ≡ true → SE E (at 0c vs i)) → (∀ i → P i ≡ false → at0 u i ≡ 0) → SE E (lin u vs)
SE-lin {M} E P []      []       hv hu = SE-0 {M} E
SE-lin {M} E P (k ∷ u) (v ∷ vs) hv hu =
  SE-+′ E (k ⊙ v) (lin u vs) hd (SE-lin E (λ i → P (suc i)) u vs (λ i → hv (suc i)) (λ i → hu (suc i)))
  where
  hd : SE E (k ⊙ v)
  hd d e with P 0 in p
  ... | true  = at0-⊙ k v d (hv 0 p d e)
  ... | false rewrite hu 0 p = at-0c {M} d

module Kill {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) (E : Nat → Bool)
            (E-dp : ∀ i → E i ≡ true → SE E (at 0c (Basis.bplus B) i))
            (E-dm : ∀ i → E i ≡ true → SE E (at 0c (Basis.bminus B) i)) where
  open Basis B
  open Atom B
  open Gen B H L
  open Rows B H L using (rows; dim-atom; rows-atom)
  open TabAt (ADC.𝕄 K)

  private
    module ν = ωCat (nu K L)
    𝕄 = ADC.𝕄 K
    zr : Row
    zr = 0c , 0c

  SER : Row → Set
  SER r = SE E (fst r) × SE E (snd r)

  -- Rows above r supported on E.
  AboveE : Nat → Tb → Set
  AboveE r x = ∀ j → r < j → SER (at zr x j)

  SE-∂⁺ : ∀ u → SE E u → SE E (dP B u)
  SE-∂⁺ u h = SE-lin E E u bplus (E-dp) (λ i e → h i e)
  SE-∂⁻ : ∀ u → SE E u → SE E (dM B u)
  SE-∂⁻ u h = SE-lin E E u bminus (E-dm) (λ i e → h i e)

  ----------------------------------------------------------------------
  -- Rows of boundaries and composites at and below the level.

  private
    at-comp-lt : ∀ {m} n (x y : Tab 𝕄 m) j → j < n → at zr (compT 𝕄 n x y) j ≡ at zr x j
    at-comp-lt (suc n) []      []       j       _       = refl
    at-comp-lt (suc n) (e ∷ r) (e′ ∷ s) zero    _       = refl
    at-comp-lt (suc n) (e ∷ r) (e′ ∷ s) (suc j) (s≤s l) = at-comp-lt n r s j l

    at-comp-eq : ∀ {m} n (x y : Tab 𝕄 m) → at zr (compT 𝕄 n x y) n ≡ (fst (at zr x n) , snd (at zr y n))
    at-comp-eq n       []            []            = refl
    at-comp-eq zero    ((a , b) ∷ r) ((c , d) ∷ s) = refl
    at-comp-eq (suc n) (e ∷ r)       (e′ ∷ s)      = at-comp-eq n r s

    at-tgt-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at zr (tgtT 𝕄 n x) j ≡ at zr x j
    at-tgt-lt (suc n) []      j       _       = refl
    at-tgt-lt (suc n) (e ∷ r) zero    _       = refl
    at-tgt-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-tgt-lt n r j l
    at-src-lt : ∀ {m} n (x : Tab 𝕄 m) j → j < n → at zr (srcT 𝕄 n x) j ≡ at zr x j
    at-src-lt (suc n) []      j       _       = refl
    at-src-lt (suc n) (e ∷ r) zero    _       = refl
    at-src-lt (suc n) (e ∷ r) (suc j) (s≤s l) = at-src-lt n r j l

    at-tgt-eq : ∀ {m} n (x : Tab 𝕄 m) → fst (at zr (tgtT 𝕄 n x) n) ≡ snd (at zr x n)
    at-tgt-eq n       []            = refl
    at-tgt-eq zero    ((a , b) ∷ r) = refl
    at-tgt-eq (suc n) (e ∷ r)       = at-tgt-eq n r
    at-src-eq : ∀ {m} n (x : Tab 𝕄 m) → fst (at zr (srcT 𝕄 n x) n) ≡ fst (at zr x n)
    at-src-eq n       []            = refl
    at-src-eq zero    ((a , b) ∷ r) = refl
    at-src-eq (suc n) (e ∷ r)       = at-src-eq n r

    SER-+ : ∀ (r r′ : Row) → SER (_+P_ 𝕄 r r′) → SER r × SER r′
    SER-+ (a , b) (c , d) (h1 , h2) = (fst (SE-+ E a c h1) , fst (SE-+ E b d h2)) , (snd (SE-+ E a c h1) , snd (SE-+ E b d h2))

    at-out : ∀ {A : Set} {m} (d : A) (vs : Vec A m) i → m ≤ i → at d vs i ≡ d
    at-out d []       i       _       = refl
    at-out d (v ∷ vs) (suc i) (s≤s q) = at-out d vs i q

    ≤-suc′ : ∀ {a b} → a < b → a < suc b
    ≤-suc′ (s≤s z≤n)     = s≤s z≤n
    ≤-suc′ (s≤s (s≤s p)) = s≤s (≤-suc′ (s≤s p))

    SE-zr : SER zr
    SE-zr = SE-0 {N} E , SE-0 {N} E

  -- The positive row at the composition level is supported on E when
  -- the negative one and the next row are.
  plus-row : ∀ (x : Tb) → IsCell K L x → ∀ n → SE E (fst (at zr x n)) → SE E (fst (at zr x (suc n))) →
             SE E (snd (at zr x n))
  plus-row x cx n hm hn with IsCell→CellF x cx | tri n L
  ... | (_ , ent , _) | tri< nL = λ d e →
      snd (+-0 (at0 (dM B u) d) (at0 b d)
        (trans (sym (at-+c (dM B u) b d))
          (trans (cong (λ v → at0 v d) (sym (bd n nL ent)))
            (trans (at-+c (dP B u) a d) (cong₂ _+_ (SE-∂⁺ u hn d e) (hm d e))))))
    where
    u = fst (at zr x (suc n))
    a = fst (at zr x n)
    b = snd (at zr x n)
    bd : ∀ n → n < L → (∀ j → j < L → Ent K L (suc j) (at zr x j) (at zr x (suc j))) →
         dP B (fst (at zr x (suc n))) +c fst (at zr x n) ≡ dM B (fst (at zr x (suc n))) +c snd (at zr x n)
    bd n nL ent = fst (snd (snd (ent n nL)))
  ... | (_ , _ , last) | tri≡ refl = subst (SE E) last hm
  ... | _ | tri> Ln = subst (λ q → SE E (snd q)) (sym (at-out zr x n Ln)) (SE-0 {N} E)

  -- The factors of a composite with rows above r on E have rows above r on E.
  above-comp : ∀ r n (x y : Tb) → IsCell K L x → tgtT 𝕄 n x ≡ srcT 𝕄 n y →
               AboveE r (compT 𝕄 n x y) → AboveE r x × AboveE r y
  above-comp r n x y cx m h = hx , hy
    where
    row-lt : ∀ j → j < n → at zr x j ≡ at zr y j
    row-lt j l = trans (sym (at-tgt-lt n x j l)) (trans (cong (λ t → at zr t j) m) (at-src-lt n y j l))
    mid : snd (at zr x n) ≡ fst (at zr y n)
    mid = trans (sym (at-tgt-eq n x)) (trans (cong (λ t → fst (at zr t n)) m) (at-src-eq n y))
    above : ∀ j → n < j → r < j → SER (at zr x j) × SER (at zr y j)
    above j l rj = SER-+ (at zr x j) (at zr y j) (subst SER (at-comp n x y j l) (h j rj))
    hx : AboveE r x
    hx j rj with tri j n
    ... | tri< l = subst SER (at-comp-lt n x y j l) (h j rj)
    ... | tri> l = fst (above j l rj)
    ... | tri≡ refl = hm , plus-row x cx j hm (fst (fst (above (suc j) (≤-refl _) (≤-suc′ rj))))
      where
      hm : SE E (fst (at zr x j))
      hm = fst (subst SER (at-comp-eq j x y) (h j rj))
    hy : AboveE r y
    hy j rj with tri j n
    ... | tri< l = subst SER (row-lt j l) (hx j rj)
    ... | tri> l = snd (above j l rj)
    ... | tri≡ refl = subst (SE E) mid (snd (hx j rj)) , snd (subst SER (at-comp-eq j x y) (h j rj))

  ----------------------------------------------------------------------
  -- The atom of an element of degree > r outside E has a row above r
  -- not supported on E.

  private
    <ℕ-suc : ∀ n → (n <ℕ suc n) ≡ true
    <ℕ-suc zero    = refl
    <ℕ-suc (suc n) = <ℕ-suc n

    ∸-self : ∀ n → n ∸ n ≡ 0
    ∸-self zero    = refl
    ∸-self (suc n) = ∸-self n

    ent-top : ∀ a → ent a (deg a) ≡ (unit a , unit a)
    ent-top a rewrite <ℕ-suc (deg a) | ∸-self (deg a) = refl

    unit-self : ∀ {m} a → a < m → at0 (unit {m} a) a ≡ 1
    unit-self {suc m} zero    _       = refl
    unit-self {suc m} (suc a) (s≤s l) = unit-self {m} a l

    atom-E : ∀ r a (aN : a < N) (aL : deg a ≤ L) → r < deg a → AboveE r (atomT L a) → E a ≡ true
    atom-E r a aN aL ra h with E a in ea
    ... | true  = refl
    ... | false = ⊥-elim (one≢0 (trans (sym (unit-self a aN)) (subst (λ q → at0 (fst q) a ≡ 0) top (fst (h (deg a) ra) a ea))))
      where
      top : at zr (atomT L a) (deg a) ≡ (unit a , unit a)
      top = trans (rows-atom a aN aL (deg a) aL) (ent-top a)
      one≢0 : 1 ≡ 0 → ⊥
      one≢0 ()

  ----------------------------------------------------------------------
  -- In 𝒟: composites of cells of dimension ≤ r have dimension ≤ r.

  module _ {𝒟 : ωCat} where
    private module 𝒟 = ωCat 𝒟
    open Basics 𝒟 hiding (comp-cong)
    module B𝒟 = Basics 𝒟

    comp-dim : ∀ r n a b p → Dim≤ r a → Dim≤ r b → Dim≤ r (𝒟.comp n a b p)
    comp-dim r n a b p da db with tri n r
    ... | tri< nr =
      trans (𝒟.src-comp-> a b p nr q) (B𝒟.comp-cong n q p da db)
      where
      q : 𝒟.tgt n (𝒟.src r a) ≡ 𝒟.src n (𝒟.src r b)
      q = trans (cong (𝒟.tgt n) da) (trans p (cong (𝒟.src n) (sym db)))
    ... | tri≡ e = subst (Dim≤ r) (sym (collapse (subst (_≤ n) e (≤-refl n)))) db
      where
      collapse : r ≤ n → 𝒟.comp n a b p ≡ b
      collapse rn = trans (B𝒟.comp-cong n p p′ a≡ refl) (𝒟.unit-l n b p′)
        where
        a≡ : a ≡ 𝒟.src n b
        a≡ = trans (sym (tgt-of-dim (dim-up rn da))) p
        p′ : 𝒟.tgt n (𝒟.src n b) ≡ 𝒟.src n b
        p′ = 𝒟.tgt-src-≥ b (≤-refl n)
    ... | tri> rn = subst (Dim≤ r) (sym (collapse (<→≤ rn))) db
      where
      collapse : r ≤ n → 𝒟.comp n a b p ≡ b
      collapse rn = trans (B𝒟.comp-cong n p p′ a≡ refl) (𝒟.unit-l n b p′)
        where
        a≡ : a ≡ 𝒟.src n b
        a≡ = trans (sym (tgt-of-dim (dim-up rn da))) p
        p′ : 𝒟.tgt n (𝒟.src n b) ≡ 𝒟.src n b
        p′ = 𝒟.tgt-src-≥ b (≤-refl n)

    ----------------------------------------------------------------------
    -- The kill lemma.

    module _ (Φ : Functor 𝒟)
             (killed : ∀ a (aN : a < N) (aL : deg a ≤ L) → E a ≡ true →
                       Dim≤ 0 (Functor.F Φ (atom a aN aL))) where
      open Functor Φ

      kill : ∀ r (x : Cell K L) → AboveE r (fst x) → Dim≤ r (F x)
      kill r (x , cx) h = go (generation x cx) cx h
        where
        go : ∀ {x} → Gen x → (cx : IsCell K L x) → AboveE r x → Dim≤ r (F (x , cx))
        go (g-atom a aN aL) cx h with ≤-dec (deg a) r
        ... | inj₁ ar =
          subst (λ c → Dim≤ r (F c)) (≡-cell K L refl)
            (dim-up ar (trans (sym (F-src (deg a) (atom a aN aL))) (cong F (dim-atom a aN aL))))
        ... | inj₂ ra =
          subst (λ c → Dim≤ r (F c)) (≡-cell K L refl)
            (dim-up z≤n (killed a aN aL (atom-E r a aN aL ra h)))
        go (g-comp n {y} {z} gy gz m) cx h =
          subst (Dim≤ r) (sym (trans (cong F (≡-cell K L refl)) (F-comp n (y , cy) (z , cz) (≡-cell K L m) q)))
            (comp-dim r n (F (y , cy)) (F (z , cz)) q (go gy cy hy) (go gz cz hz))
          where
          cy = gen-cell gy
          cz = gen-cell gz
          hs = above-comp r n y z cy m h
          hy = fst hs
          hz = snd hs
          q : 𝒟.tgt n (F (y , cy)) ≡ 𝒟.src n (F (z , cz))
          q = trans (sym (F-tgt n (y , cy))) (trans (cong F (≡-cell K L m)) (F-src n (z , cz)))
