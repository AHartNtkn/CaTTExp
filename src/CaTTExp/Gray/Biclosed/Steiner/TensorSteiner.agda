------------------------------------------------------------------------
-- Strong Steiner under the tensor (ledger C5f): loop-freeness, degrees,
-- disjoint supports and augmentation.
--
-- The basis of a code a ∷ K is the pairs (i, x) with the Leibniz
-- boundary of `Codes.bd`.  Its relation <₁ has two kinds of steps:
--   (i, x) <₁ (j, x)  when i <₁ j in a;
--   (i, x) <₁ (i, y)  when x <₁ y in K, if deg i is even,
--                     and when y <₁ x in K, if deg i is odd.
-- Part 1.  Given heights hA for a and hK for K, the height
--   H (i, x) = hA i · M + s (i, x),
--   s (i, x) = hK x            if deg i is even,
--            = mK ∸ hK x       if deg i is odd,
-- with mK the largest value of hK and M = mK + 1, strictly increases
-- along both kinds of step (`tensor-height`).  So a ∷ K is strongly
-- loop-free whenever a and K are, and by induction every code is when
-- its atoms are (`code-height`).
--
-- Part 2: degrees (`t-degs`), disjoint supports (`t-disj`) and
-- augmentation (`t-aug`) carry over from a and K to a ∷ K.
--
-- Not proved here yet: ∂∂ = 0 and unitality for a ∷ K.  So the full
-- `StrongSteiner` record for a tensor is not yet derived.
-- No postulates.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.TensorSteiner (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes
open import CaTTExp.Gray.Biclosed.Steiner.StrongSteiner
open Codes nmFB

-- the basis of a code
codeFB : Code → FB
codeFB K = record { Cell = El K ; enumC = enumEl K ; fdeg = deg K ; fbd = bd K }

------------------------------------------------------------------------
-- Boolean arithmetic

private
  T-subst : ∀ {b c} → b ≡ c → T b → T c
  T-subst refl p = p

  <-+r : ∀ a b c → T (a <ℕ b) → T (a <ℕ b + c)
  <-+r zero    (suc b) c _ = tt
  <-+r (suc a) (suc b) c p = <-+r a b c p

  <-+l : ∀ a b c → T (b <ℕ c) → T (a + b <ℕ a + c)
  <-+l zero    b c p = p
  <-+l (suc a) b c p = <-+l a b c p

  -- a < b and s < M give a·M + s < b·M + t
  <-lex : ∀ a b M s t → T (a <ℕ b) → T (s <ℕ M) → T (a * M + s <ℕ b * M + t)
  <-lex zero    (suc b) M s t _ p = <-+r s (M + b * M) t (<-+r s M (b * M) p)
  <-lex (suc a) (suc b) M s t q p =
    T-subst (cong₂ _<ℕ_ (sym (+-assoc M (a * M) s)) (sym (+-assoc M (b * M) t)))
            (<-+l M (a * M + s) (b * M + t) (<-lex a b M s t q p))

  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  ≤-max-l : ∀ a b → T (a <ℕ suc (max a b))
  ≤-max-l zero    b       = tt
  ≤-max-l (suc a) zero    = <-suc a
  ≤-max-l (suc a) (suc b) = ≤-max-l a b

  ≤-max-r : ∀ a b c → T (c <ℕ suc b) → T (c <ℕ suc (max a b))
  ≤-max-r a       b       zero    _ = tt
  ≤-max-r zero    b       (suc c) p = p
  ≤-max-r (suc a) zero    (suc c) ()
  ≤-max-r (suc a) (suc b) (suc c) p = ≤-max-r a b c p

  ∸-≤ : ∀ m k → T ((m ∸ k) <ℕ suc m)
  ∸-≤ zero    zero    = tt
  ∸-≤ zero    (suc k) = tt
  ∸-≤ (suc m) zero    = <-suc m
  ∸-≤ (suc m) (suc k) = <-step′ (m ∸ k) m (∸-≤ m k)
    where <-step′ : ∀ a b → T (a <ℕ suc b) → T (a <ℕ suc (suc b))
          <-step′ zero    b       _ = tt
          <-step′ (suc a) zero    ()
          <-step′ (suc a) (suc b) p = <-step′ a b p

  -- a < b ≤ m gives m ∸ b < m ∸ a
  ∸-anti : ∀ m a b → T (a <ℕ b) → T (b <ℕ suc m) → T ((m ∸ b) <ℕ (m ∸ a))
  ∸-anti (suc m) zero    (suc b) _ q = go m b q
    where go : ∀ m b → T (b <ℕ suc m) → T ((m ∸ b) <ℕ suc m)
          go m b q = ∸-≤ m b
  ∸-anti (suc m) (suc a) (suc b) p q = ∸-anti m a b p q
  ∸-anti zero    zero    (suc b) _ ()
  ∸-anti zero    (suc a) (suc b) _ ()

  nz-+ : ∀ a b → T (not ((a + b) ==ℕ 0)) → T (not (a ==ℕ 0)) ⊎ T (not (b ==ℕ 0))
  nz-+ zero    b p = inj₂ p
  nz-+ (suc a) b p = inj₁ tt

  nz-*ˡ : ∀ a b → T (not ((a * b) ==ℕ 0)) → T (not (a ==ℕ 0))
  nz-*ˡ zero    b ()
  nz-*ˡ (suc a) b _ = tt

  nz-*ʳ : ∀ a b → T (not ((a * b) ==ℕ 0)) → T (not (b ==ℕ 0))
  nz-*ʳ a b p = nz-*ˡ b a (T-subst (cong (λ z → not (z ==ℕ 0)) (*-comm a b)) p)

  -- a nonzero indicator is a diagonal entry
  δ-nz : ∀ {A : Set} (E : Enum A) x y → T (not (δ E x y ==ℕ 0)) → x ≡ y
  δ-nz E x y p = go (eqb E x y) refl p
    where
      go : ∀ b → eqb E x y ≡ b → T (not ((if b then 1 else 0) ==ℕ 0)) → x ≡ y
      go true  e _ = eqb-sound E (T-subst (sym e) tt)
      go false e ()

------------------------------------------------------------------------
-- The largest value of a function on an enumeration

maxl : ∀ {A : Set} → List A → (A → Nat) → Nat
maxl []       f = 0
maxl (x ∷ xs) f = max (f x) (maxl xs f)

private
  maxl-≥ : ∀ {A : Set} (E : Enum A) (f : A → Nat) a xs →
           (Σl xs (δ E a) ≡ 0 → ⊥) → T (f a <ℕ suc (maxl xs f))
  maxl-≥ E f a []       nz = ⊥-elim (nz refl)
  maxl-≥ E f a (x ∷ xs) nz = go (eqb E a x) refl
    where
      go : ∀ b → eqb E a x ≡ b → T (f a <ℕ suc (maxl (x ∷ xs) f))
      go true  e with eqb-sound E {a} {x} (T-subst (sym e) tt)
      ... | refl = ≤-max-l (f a) (maxl xs f)
      go false e = ≤-max-r (f x) (maxl xs f) (f a)
                     (maxl-≥ E f a xs (λ z → nz (trans (cong (λ b → (if b then 1 else 0) + Σl xs (δ E a)) e) z)))

  one≢zero : 1 ≡ 0 → ⊥
  one≢zero ()

maxE : ∀ {A : Set} (E : Enum A) (f : A → Nat) a → T (f a <ℕ suc (maxl (els E) f))
maxE E f a = maxl-≥ E f a (els E) (λ z → one≢zero (trans (sym (count E a)) z))

------------------------------------------------------------------------
-- The steps of <₁ on a ∷ K

module _ (a : AC) (K : Code) where
  private
    module SA = SS (fbA a)
    module SK = SS (codeFB K)
    module ST = SS (codeFB (a ∷ K))
    EA = enumA a
    EK = enumEl K

  data Step : El (a ∷ K) → El (a ∷ K) → Set where
    outer : ∀ {i j x} → T (SA.lt₁ i j) → Step (i , x) (j , x)
    evenS : ∀ {i x y} → even (degA a i) ≡ true  → T (SK.lt₁ x y) → Step (i , x) (i , y)
    oddS  : ∀ {i x y} → even (degA a i) ≡ false → T (SK.lt₁ y x) → Step (i , x) (i , y)

  private
    ∨-elim : ∀ {p q} → T (p ∨ q) → T p ⊎ T q
    ∨-elim {true}  _ = inj₁ tt
    ∨-elim {false} r = inj₂ r

    ∨-l : ∀ {p} q → T p → T (p ∨ q)
    ∨-l {true} q _ = tt

    ∨-r : ∀ p {q} → T q → T (p ∨ q)
    ∨-r true  _ = tt
    ∨-r false r = r

    evenB : ∀ d → Σ Bool (λ b → even d ≡ b)
    evenB d = even d , refl

    -- y ∈ ∂⁻ (j , w) ... the boundary entry splits into its two terms
    stepF : ∀ i x j y → T (not (bd (a ∷ K) false (j , y) (i , x) ==ℕ 0)) → Step (i , x) (j , y)
    stepF i x j y p with nz-+ (bdA a false j i * δE K y x) (δ EA j i * bd K (flip (degA a j) false) y x) p
    ... | inj₁ q with δ-nz EK y x (nz-*ʳ (bdA a false j i) (δE K y x) q)
    ...   | refl = outer (∨-l (SA.nz (bdA a true i j)) (nz-*ˡ (bdA a false j i) (δE K y x) q))
    stepF i x j y p | inj₂ q with δ-nz EA j i (nz-*ˡ (δ EA j i) (bd K (flip (degA a j) false) y x) q)
    ... | refl = par (even (degA a i)) refl (nz-*ʳ (δ EA i i) (bd K (flip (degA a i) false) y x) q)
      where
        par : ∀ b → even (degA a i) ≡ b → T (not (bd K (if b then false else true) y x ==ℕ 0)) → Step (i , x) (i , y)
        par true  e r = evenS e (∨-l (SK.nz (bd K true x y)) r)
        par false e r = oddS e (∨-r (SK.nz (bd K false x y)) r)

    stepT : ∀ i x j y → T (not (bd (a ∷ K) true (i , x) (j , y) ==ℕ 0)) → Step (i , x) (j , y)
    stepT i x j y p with nz-+ (bdA a true i j * δE K x y) (δ EA i j * bd K (flip (degA a i) true) x y) p
    ... | inj₁ q with δ-nz EK x y (nz-*ʳ (bdA a true i j) (δE K x y) q)
    ...   | refl = outer (∨-r (SA.nz (bdA a false j i)) (nz-*ˡ (bdA a true i j) (δE K x x) q))
    stepT i x j y p | inj₂ q with δ-nz EA i j (nz-*ˡ (δ EA i j) (bd K (flip (degA a i) true) x y) q)
    ... | refl = par (even (degA a i)) refl (nz-*ʳ (δ EA i i) (bd K (flip (degA a i) true) x y) q)
      where
        par : ∀ b → even (degA a i) ≡ b → T (not (bd K (if b then true else false) x y ==ℕ 0)) → Step (i , x) (i , y)
        par true  e r = evenS e (∨-r (SK.nz (bd K false y x)) r)
        par false e r = oddS e (∨-l (SK.nz (bd K true y x)) r)

  step : ∀ u v → T (ST.lt₁ u v) → Step u v
  step (i , x) (j , y) l with ∨-elim l
  ... | inj₁ p = stepF i x j y p
  ... | inj₂ p = stepT i x j y p

  --------------------------------------------------------------------
  -- The height

  module _ (HA : SA.Height) (HK : SK.Height) where
    private
      hA = SA.Height.h HA
      hK = SK.Height.h HK
      mK = maxl (els EK) hK
      M  = suc mK

    sH : El (a ∷ K) → Nat
    sH (i , x) = if even (degA a i) then hK x else (mK ∸ hK x)

    H : El (a ∷ K) → Nat
    H (i , x) = hA i * M + sH (i , x)

    private
      sH-< : ∀ u → T (sH u <ℕ M)
      sH-< (i , x) = go (even (degA a i))
        where go : ∀ b → T ((if b then hK x else (mK ∸ hK x)) <ℕ M)
              go true  = maxE EK hK x
              go false = ∸-≤ mK (hK x)

      sH-ev : ∀ i x → even (degA a i) ≡ true → sH (i , x) ≡ hK x
      sH-ev i x e rewrite e = refl

      sH-od : ∀ i x → even (degA a i) ≡ false → sH (i , x) ≡ mK ∸ hK x
      sH-od i x e rewrite e = refl

    up : ∀ u v → T (ST.lt₁ u v) → T (H u <ℕ H v)
    up u v l with step u v l
    ... | outer {i} {j} {x} p =
      <-lex (hA i) (hA j) M (sH (i , x)) (sH (j , x)) (SA.Height.up HA i j p) (sH-< (i , x))
    ... | evenS {i} {x} {y} e p =
      <-+l (hA i * M) (sH (i , x)) (sH (i , y))
        (T-subst (cong₂ _<ℕ_ (sym (sH-ev i x e)) (sym (sH-ev i y e))) (SK.Height.up HK x y p))
    ... | oddS {i} {x} {y} e p =
      <-+l (hA i * M) (sH (i , x)) (sH (i , y))
        (T-subst (cong₂ _<ℕ_ (sym (sH-od i x e)) (sym (sH-od i y e)))
          (∸-anti mK (hK y) (hK x) (SK.Height.up HK y x p) (maxE EK hK x)))

    tensor-height : ST.Height
    tensor-height = record { h = H ; up = up }

------------------------------------------------------------------------
-- Every code is strongly loop-free when its atoms are

data AllH : Code → Set where
  []ʰ  : AllH []
  _∷ʰ_ : ∀ {a K} → SS.Height (fbA a) → AllH K → AllH (a ∷ K)

code-height : ∀ K → AllH K → SS.Height (codeFB K)
code-height []      []ʰ        = record { h = λ _ → 0 ; up = λ { tt tt () } }
code-height (a ∷ K) (HA ∷ʰ HK) = tensor-height a K HA (code-height K HK)

------------------------------------------------------------------------
-- Part 2: degrees, disjoint supports, augmentation

private
  notT : ∀ {p} → T (not p) → T p → ⊥
  notT {true}  () _
  notT {false} _ ()

  ∨-elim′ : ∀ {p q} → T (p ∨ q) → T p ⊎ T q
  ∨-elim′ {true}  _ = inj₁ tt
  ∨-elim′ {false} r = inj₂ r

  ==-T : ∀ {m n} → m ≡ n → T (m ==ℕ n)
  ==-T {m} refl = ==ℕ-refl m

  n≢sn : ∀ n → suc n ≡ n → ⊥
  n≢sn zero    ()
  n≢sn (suc n) e = n≢sn n (suc-inj′ e)
    where suc-inj′ : ∀ {a b} → suc a ≡ suc b → a ≡ b
          suc-inj′ refl = refl

  sz : ∀ {n} → suc n ≡ 0 → ⊥
  sz ()

  degAt-from : ∀ p q k → (T (not (p ==ℕ 0)) → T k) → (T (not (q ==ℕ 0)) → T k) →
               T ((not (not (p ==ℕ 0)) ∧ not (not (q ==ℕ 0))) ∨ k)
  degAt-from zero    zero    k f g = tt
  degAt-from zero    (suc q) k f g = g tt
  degAt-from (suc p) q       k f g = f tt

  mul0 : ∀ p q → p * q ≡ 0 → (p ≡ 0) ⊎ (q ≡ 0)
  mul0 zero    q       _ = inj₁ refl
  mul0 (suc p) zero    _ = inj₂ refl
  mul0 (suc p) (suc q) ()

  prod0 : ∀ p q r → p * q ≡ 0 → (p * r + 0) * (q * r + 0) ≡ 0
  prod0 p q r e with mul0 p q e
  ... | inj₁ refl = refl
  ... | inj₂ refl = *-zero (p * r + 0)

  flip-cases : ∀ d → ((flip d true ≡ true) × (flip d false ≡ false)) ⊎ ((flip d true ≡ false) × (flip d false ≡ true))
  flip-cases d with even d
  ... | true  = inj₁ (refl , refl)
  ... | false = inj₂ (refl , refl)

-- in any basis, a nonzero entry allowed by the degree condition is one degree down
deg-of : ∀ (B : FB) x y α → T (SS.degAt B x y) → T (SS.nz B (fbd B α x y)) → suc (fdeg B y) ≡ fdeg B x
deg-of B x y α dg nz with ∨-elim′ {not (SS.nz B (fbd B true x y)) ∧ not (SS.nz B (fbd B false x y))}
                                 {suc (fdeg B y) ==ℕ fdeg B x} dg
... | inj₂ q = ==ℕ-sound _ _ q
deg-of B x y true  dg nz | inj₁ p = ⊥-elim (notT (∧-fst p) nz)
deg-of B x y false dg nz | inj₁ p = ⊥-elim (notT (∧-snd {not (SS.nz B (fbd B true x y))} p) nz)

-- a diagonal entry is zero
diag0 : ∀ (B : FB) α x → T (SS.degAt B x x) → fbd B α x x ≡ 0
diag0 B α x dg = go (fbd B α x x) refl
  where
    go : ∀ n → fbd B α x x ≡ n → fbd B α x x ≡ 0
    go zero    e = e
    go (suc n) e = ⊥-elim (n≢sn _ (deg-of B x x α dg (T-subst (cong (λ m → not (m ==ℕ 0)) (sym e)) tt)))

module _ (a : AC) (K : Code) where
  private
    module SA = SS (fbA a)
    module SK = SS (codeFB K)
    module ST = SS (codeFB (a ∷ K))
    EA = enumA a
    EK = enumEl K
    A  = fbA a
    KB = codeFB K

  module _ (dA : ∀ i j → T (SA.degAt i j)) (dK : ∀ x y → T (SK.degAt x y)) where

    ent-deg : ∀ α i x j y → T (not (bd (a ∷ K) α (i , x) (j , y) ==ℕ 0)) →
              suc (degA a j + deg K y) ≡ degA a i + deg K x
    ent-deg α i x j y p with nz-+ (bdA a α i j * δE K x y) (δ EA i j * bd K (flip (degA a i) α) x y) p
    ... | inj₁ q with δ-nz EK x y (nz-*ʳ (bdA a α i j) (δE K x y) q)
    ...   | refl = cong (_+ deg K x) (deg-of A i j α (dA i j) (nz-*ˡ (bdA a α i j) (δE K x x) q))
    ent-deg α i x j y p | inj₂ q with δ-nz EA i j (nz-*ˡ (δ EA i j) (bd K (flip (degA a i) α) x y) q)
    ... | refl = trans (sym (+-suc (degA a i) (deg K y)))
                   (cong (degA a i +_) (deg-of KB x y (flip (degA a i) α) (dK x y)
                     (nz-*ʳ (δ EA i i) (bd K (flip (degA a i) α) x y) q)))

    t-degs : ∀ u v → T (ST.degAt u v)
    t-degs (i , x) (j , y) =
      degAt-from (bd (a ∷ K) true (i , x) (j , y)) (bd (a ∷ K) false (i , x) (j , y))
                 (suc (degA a j + deg K y) ==ℕ (degA a i + deg K x))
                 (λ p → ==-T (ent-deg true i x j y p)) (λ p → ==-T (ent-deg false i x j y p))

    module _ (jA : ∀ i j → T (SA.disjAt i j)) (jK : ∀ x y → T (SK.disjAt x y)) where
      private
        dz : ∀ i j → eqb EA i j ≡ false → δ EA i j ≡ 0
        dz i j e = cong (λ b → if b then 1 else 0) e

        disj-eq : ∀ i x j y →
          (bdA a true i j * δE K x y + δ EA i j * bd K (flip (degA a i) true) x y) *
          (bdA a false i j * δE K x y + δ EA i j * bd K (flip (degA a i) false) x y) ≡ 0
        disj-eq i x j y = go (eqb EA i j) refl
          where
            go : ∀ b → eqb EA i j ≡ b →
                 (bdA a true i j * δE K x y + δ EA i j * bd K (flip (degA a i) true) x y) *
                 (bdA a false i j * δE K x y + δ EA i j * bd K (flip (degA a i) false) x y) ≡ 0
            go false e rewrite dz i j e =
              prod0 (bdA a true i j) (bdA a false i j) (δE K x y) (==ℕ-sound _ _ (jA i j))
            go true e with eqb-sound EA {i} {j} (T-subst (sym e) tt)
            ... | refl rewrite δ-refl EA i | diag0 A true i (dA i i) | diag0 A false i (dA i i)
                             | +-zero (bd K (flip (degA a i) true) x y) | +-zero (bd K (flip (degA a i) false) x y)
                             with flip-cases (degA a i)
            ...   | inj₁ (p , q) rewrite p | q = ==ℕ-sound _ _ (jK x y)
            ...   | inj₂ (p , q) rewrite p | q =
                      trans (*-comm (bd K false x y) (bd K true x y)) (==ℕ-sound _ _ (jK x y))

      t-disj : ∀ u v → T (ST.disjAt u v)
      t-disj (i , x) (j , y) = ==-T (disj-eq i x j y)

    private
      Σ-ent : ∀ α i x → Σl (els (enumEl (a ∷ K))) (bd (a ∷ K) α (i , x)) ≡
              Σl (els EA) (bdA a α i) + Σl (els EK) (bd K (flip (degA a i) α) x)
      Σ-ent α i x =
        trans (Σ-pairs (els EA) (els EK) (bd (a ∷ K) α (i , x)))
        (trans (Σ-cong (els EA) inner)
        (trans (Σ-+ (els EA) (bdA a α i) (λ j → δ EA i j * SKx))
               (cong (Σl (els EA) (bdA a α i) +_) (trans (Σ-δ EA i (λ _ → SKx)) refl))))
        where
          SKx = Σl (els EK) (bd K (flip (degA a i) α) x)
          inner : ∀ j → Σl (els EK) (λ y → bdA a α i j * δE K x y + δ EA i j * bd K (flip (degA a i) α) x y) ≡
                        bdA a α i j + δ EA i j * SKx
          inner j =
            trans (Σ-+ (els EK) (λ y → bdA a α i j * δE K x y) (λ y → δ EA i j * bd K (flip (degA a i) α) x y))
            (cong₂ _+_ (trans (sym (Σ-*ˡ (els EK) (bdA a α i j) (δE K x)))
                              (trans (cong (bdA a α i j *_) (count EK x)) (*-one (bdA a α i j))))
                       (sym (Σ-*ˡ (els EK) (δ EA i j) (bd K (flip (degA a i) α) x))))

      row0 : ∀ (B : FB) (dg : ∀ x y → T (SS.degAt B x y)) β x → fdeg B x ≡ 0 →
             Σl (els (enumC B)) (fbd B β x) ≡ 0
      row0 B dg β x e = trans (Σ-cong (els (enumC B)) z) (Σ-0 (els (enumC B)))
        where
          z : ∀ y → fbd B β x y ≡ 0
          z y = go (fbd B β x y) refl
            where
              go : ∀ n → fbd B β x y ≡ n → fbd B β x y ≡ 0
              go zero    q = q
              go (suc n) q = ⊥-elim (sz (trans (deg-of B x y β (dg x y)
                               (T-subst (cong (λ m → not (m ==ℕ 0)) (sym q)) tt)) e))

      augEq : ∀ (B : FB) x → fdeg B x ≡ 1 → T (SS.augAt B x) →
              Σl (els (enumC B)) (fbd B true x) ≡ Σl (els (enumC B)) (fbd B false x)
      augEq B x e p with ∨-elim′ {not (fdeg B x ==ℕ 1)} {Σl (els (enumC B)) (fbd B true x) ==ℕ Σl (els (enumC B)) (fbd B false x)} p
      ... | inj₁ q = ⊥-elim (notT q (==-T e))
      ... | inj₂ q = ==ℕ-sound _ _ q

      sum1 : ∀ m n → m + n ≡ 1 → ((m ≡ 0) × (n ≡ 1)) ⊎ ((m ≡ 1) × (n ≡ 0))
      sum1 zero          n e  = inj₁ (refl , e)
      sum1 (suc zero)    zero e = inj₂ (refl , refl)
      sum1 (suc zero)    (suc n) ()
      sum1 (suc (suc m)) n ()

    module _ (gA : ∀ i → T (SA.augAt i)) (gK : ∀ x → T (SK.augAt x)) where
      t-aug : ∀ u → T (ST.augAt u)
      t-aug (i , x) = go ((degA a i + deg K x) ==ℕ 1) refl
        where
          go : ∀ b → ((degA a i + deg K x) ==ℕ 1) ≡ b → T (ST.augAt (i , x))
          go false e = T-subst (cong (λ c → not c ∨ (Σl (els (enumEl (a ∷ K))) (bd (a ∷ K) true (i , x)) ==ℕ
                                                       Σl (els (enumEl (a ∷ K))) (bd (a ∷ K) false (i , x)))) (sym e)) tt
          go true e = ∨-r′ (==-T (trans (Σ-ent true i x) (trans (split (sum1 _ _ (==ℕ-sound _ _ (T-subst (sym e) tt)))) (sym (Σ-ent false i x)))))
            where
              ∨-r′ : ∀ {p q} → T q → T (p ∨ q)
              ∨-r′ {true}  _ = tt
              ∨-r′ {false} r = r
              split : (((degA a i ≡ 0) × (deg K x ≡ 1)) ⊎ ((degA a i ≡ 1) × (deg K x ≡ 0))) →
                      Σl (els EA) (bdA a true i) + Σl (els EK) (bd K (flip (degA a i) true) x) ≡
                      Σl (els EA) (bdA a false i) + Σl (els EK) (bd K (flip (degA a i) false) x)
              split (inj₁ (p , q)) rewrite p =
                cong₂ _+_ (trans (row0 A dA true i p′) (sym (row0 A dA false i p′))) (augEq KB x q (gK x))
                where p′ : fdeg A i ≡ 0
                      p′ = p
              split (inj₂ (p , q)) =
                cong₂ _+_ (augEq A i p (gA i))
                  (trans (row0 KB dK (flip (degA a i) true) x q) (sym (row0 KB dK (flip (degA a i) false) x q)))
