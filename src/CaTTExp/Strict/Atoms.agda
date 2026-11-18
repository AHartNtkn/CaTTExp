------------------------------------------------------------------------
-- Atoms of ν(K) for a finite basis (ledger A5, toward N1).
--
-- For a basis element b of degree n, Steiner's atom ⟨b⟩ has
--   ⟨b⟩ₙ⁻ = ⟨b⟩ₙ⁺ = b,
--   ⟨b⟩ₖ⁻ = (∂⟨b⟩ₖ₊₁⁻)₋,   ⟨b⟩ₖ⁺ = (∂⟨b⟩ₖ₊₁⁺)₊       (k < n),
-- and zero above n (Steiner 2004, §3). With non-negative chains,
-- (∂c)₊ = ∂⁺c ∸ ∂⁻c and (∂c)₋ = ∂⁻c ∸ ∂⁺c, pointwise.
--
-- `atom-cell`: if ∂∂ = 0 on the basis and the basis is unital, every
-- atom is a cell of ν(K) (Steiner 2004, Def. 3.4 and the remark after
-- Def. 3.1).
------------------------------------------------------------------------
module CaTTExp.Strict.Atoms where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero)

------------------------------------------------------------------------
-- Pointwise monus.


_∸c_ : ∀ {m} → Vec Nat m → Vec Nat m → Vec Nat m
[]      ∸c []      = []
(a ∷ u) ∸c (b ∷ v) = (a ∸ b) ∷ (u ∸c v)

private
  ∸-max : ∀ a b → a + (b ∸ a) ≡ b + (a ∸ b)
  ∸-max zero    zero    = refl
  ∸-max zero    (suc b) = cong suc (sym (+-zero b))
  ∸-max (suc a) zero    = cong suc (+-zero a)
  ∸-max (suc a) (suc b) = cong suc (∸-max a b)

  -- ∸-max gives a + (b ∸ a) ≡ b + (a ∸ b); the form we need:
  ∸-split : ∀ a b → a + (b ∸ a) ≡ b + (a ∸ b)
  ∸-split = ∸-max

-- c⁺ + (c⁻ ∸ c⁺) = c⁻ + (c⁺ ∸ c⁻): ∂c = (∂c)₊ − (∂c)₋.
∸c-split : ∀ {m} (u v : Vec Nat m) → u +c (v ∸c u) ≡ v +c (u ∸c v)
∸c-split []      []      = refl
∸c-split (a ∷ u) (b ∷ v) = cong₂ _∷_ (∸-split a b) (∸c-split u v)

------------------------------------------------------------------------
-- Equational helpers in a cancellative commutative monoid of chains.

private
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  +-suc″ : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc″ zero    n = refl
  +-suc″ (suc m) n = cong suc (+-suc″ m n)

  0∸ : ∀ d → 0 ∸ d ≡ 0
  0∸ zero    = refl
  0∸ (suc d) = refl

  ∸-big : ∀ c b d → d ≡ c + b → c ∸ d ≡ 0
  ∸-big zero    b d       p = 0∸ d
  ∸-big (suc c) b zero    ()
  ∸-big (suc c) b (suc d) p = ∸-big c b d (suc-inj p)

  ∸-eq : ∀ a b c d → a + d ≡ c + b → a ∸ b ≡ c ∸ d
  ∸-eq a       zero    c       zero    p = trans (sym (+-zero a)) (trans p (+-zero c))
  ∸-eq zero    b       c       d       p = trans (0∸ b) (sym (∸-big c b d p))
  ∸-eq (suc a) b       zero    d       p = trans (∸-big (suc a) d b (sym p)) (sym (0∸ d))
  ∸-eq (suc a) (suc b) (suc c) d       p = ∸-eq a b (suc c) d (suc-inj (trans p (+-suc″ (suc c) b)))
  ∸-eq (suc a) zero    (suc c) (suc d) p = ∸-eq (suc a) zero c d (suc-inj (trans (sym (+-suc″ (suc a) d)) p))

-- u + x ≡ v + y gives u ∸ y ≡ v ∸ x.
∸c-eq : ∀ {m} (u x v y : Vec Nat m) → u +c x ≡ v +c y → u ∸c y ≡ v ∸c x
∸c-eq []      []      []      []      p = refl
∸c-eq (a ∷ u) (d ∷ x) (c ∷ v) (b ∷ y) p =
  cong₂ _∷_ (∸-eq a b c d (hd p)) (∸c-eq u x v y (tl p))
  where
  hd : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → a ≡ b
  hd refl = refl
  tl : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → u ≡ v
  tl refl = refl

------------------------------------------------------------------------
-- Vectors: lookup and unit vectors.

at : ∀ {A : Set} {m} → A → Vec A m → Nat → A
at d []      i       = d
at d (x ∷ v) zero    = x
at d (x ∷ v) (suc i) = at d v i

unit : ∀ {m} → Nat → Vec Nat m
unit {zero}  i       = []
unit {suc m} zero    = 1 ∷ 0c
unit {suc m} (suc i) = 0 ∷ unit i

------------------------------------------------------------------------
-- Atoms of a finite basis.

module Atom {N : Nat} (B : Basis N) where
  open Basis B

  K = adc B
  open ADC K using () renaming (∂⁺ to dp; ∂⁻ to dm; π to pj)

  deg : Nat → Nat
  deg i = at 0 gdeg i

  -- One step down: (c⁻, c⁺) ↦ ((∂c⁻)₋, (∂c⁺)₊).
  step : Vec Nat N × Vec Nat N → Vec Nat N × Vec Nat N
  step (a , b) = (dm a ∸c dp a) , (dp b ∸c dm b)

  -- ⟨i⟩ at depth k below its top.
  entK : Nat → Nat → Vec Nat N × Vec Nat N
  entK i zero    = unit i , unit i
  entK i (suc k) = step (entK i k)

  -- ⟨i⟩ in degree j.
  ent : Nat → Nat → Vec Nat N × Vec Nat N
  ent i j = if j <ℕ suc (deg i) then entK i (deg i ∸ j) else (0c , 0c)

  tabF : ∀ {m} → (Nat → Vec Nat N × Vec Nat N) → Nat → Vec (Vec Nat N × Vec Nat N) m
  tabF {zero}  f j = []
  tabF {suc m} f j = f j ∷ tabF f (suc j)

  -- The atom as a table of length L + 1.
  atomT : (L : Nat) → Nat → Vec (Vec Nat N × Vec Nat N) (suc L)
  atomT L i = tabF (ent i) 0

  ----------------------------------------------------------------------
  -- Atoms are cells.

  private
    _≗_ : Vec Nat N → Vec Nat N → Set
    _≗_ = _≡_

    mid : ∀ (a b c d : Vec Nat N) → (a +c b) +c (c +c d) ≡ (a +c c) +c (b +c d)
    mid a b c d =
      trans (+c-assoc a b (c +c d))
        (trans (cong (a +c_) (trans (sym (+c-assoc b c d)) (trans (cong (_+c d) (+c-comm b c)) (+c-assoc c b d))))
               (sym (+c-assoc a c (b +c d))))

  -- ∂c⁻ = ∂c⁺ (as signed chains).
  Inv : Vec Nat N × Vec Nat N → Set
  Inv (a , b) = dp a +c dm b ≡ dp b +c dm a

  Bd⁻ : ∀ c → Inv c → dp (fst c) +c fst (step c) ≡ dm (fst c) +c snd (step c)
  Bd⁻ (a , b) I =
    trans (∸c-split (dp a) (dm a)) (cong (dm a +c_) (∸c-eq (dp a) (dm b) (dp b) (dm a) I))

  Bd⁺ : ∀ c → Inv c → dp (snd c) +c fst (step c) ≡ dm (snd c) +c snd (step c)
  Bd⁺ (a , b) I =
    trans (cong (dp b +c_) (∸c-eq (dm a) (dp b) (dm b) (dp a)
                             (trans (+c-comm (dm a) (dp b)) (trans (sym I) (+c-comm (dp a) (dm b))))))
          (∸c-split (dp b) (dm b))

  module Cells
    (dd : ∀ c → dp (dp c) +c dm (dm c) ≡ dp (dm c) +c dm (dp c))
    where

    Inv-step : ∀ c → Inv c → Inv (step c)
    Inv-step (a , b) I = +c-cancel (dp x +c dm y) (dp y +c dm x) (dp (dp a) +c dm (dm a)) goal
      where
      x = fst (step (a , b))
      y = snd (step (a , b))
      E1 : dp a +c x ≡ dm a +c y
      E1 = Bd⁻ (a , b) I
      A : dp (dp a) +c dp x ≡ dp (dm a) +c dp y
      A = trans (sym (lin-+ (dp a) x bplus)) (trans (cong dp E1) (lin-+ (dm a) y bplus))
      Bm : dm (dm a) +c dm y ≡ dm (dp a) +c dm x
      Bm = trans (sym (lin-+ (dm a) y bminus)) (trans (cong dm (sym E1)) (lin-+ (dp a) x bminus))
      goal : (dp x +c dm y) +c (dp (dp a) +c dm (dm a)) ≡ (dp y +c dm x) +c (dp (dp a) +c dm (dm a))
      goal =
        trans (+c-comm (dp x +c dm y) _)
        (trans (mid (dp (dp a)) (dm (dm a)) (dp x) (dm y))
        (trans (cong₂ _+c_ A Bm)
        (trans (mid (dp (dm a)) (dp y) (dm (dp a)) (dm x))
        (trans (cong (_+c (dp y +c dm x)) (sym (dd a)))
               (+c-comm _ (dp y +c dm x))))))

    Inv-entK : ∀ i k → Inv (entK i k)
    Inv-entK i zero    = refl
    Inv-entK i (suc k) = Inv-step (entK i k) (Inv-entK i k)

    module Deg
      (deg-dp : ∀ j c → pj (suc j) c ≡ c → pj j (dp c) ≡ dp c)
      (deg-dm : ∀ j c → pj (suc j) c ≡ c → pj j (dm c) ≡ dm c)
      where

      private
        ==-r : ∀ n → (n ==ℕ n) ≡ true
        ==-r zero    = refl
        ==-r (suc n) = ==-r n

        if-same : ∀ (b : Bool) (x : Nat) → (if b then x else x) ≡ x
        if-same true  x = refl
        if-same false x = refl

        hdV : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → a ≡ b
        hdV refl = refl
        tlV : ∀ {m} {a b : Nat} {u v : Vec Nat m} → _≡_ {A = Vec Nat (suc m)} (a ∷ u) (b ∷ v) → u ≡ v
        tlV refl = refl

      unit-deg′ : ∀ {m} (gs : Vec Nat m) i → prj (at 0 gs i) gs (unit i) ≡ unit i
      unit-deg′ []       i       = refl
      unit-deg′ (g ∷ gs) zero    rewrite ==-r g = cong (1 ∷_) (prj-0 g gs)
      unit-deg′ (g ∷ gs) (suc i) = cong₂ _∷_ (if-same (g ==ℕ at 0 gs i) 0) (unit-deg′ gs i)

      ∸c-deg : ∀ {m} j (gs : Vec Nat m) u v → prj j gs u ≡ u → prj j gs (u ∸c v) ≡ u ∸c v
      ∸c-deg j []       []      []      p = refl
      ∸c-deg j (g ∷ gs) (a ∷ u) (b ∷ v) p with g ==ℕ j
      ... | true  = cong ((a ∸ b) ∷_) (∸c-deg j gs u v (tlV p))
      ... | false = cong₂ _∷_ (trans (sym (0∸ b)) (cong (_∸ b) (hdV p))) (∸c-deg j gs u v (tlV p))

      deg-entK : ∀ i k m → deg i ≡ k + m →
                 (pj m (fst (entK i k)) ≡ fst (entK i k)) × (pj m (snd (entK i k)) ≡ snd (entK i k))
      deg-entK i zero    m e rewrite sym e = unit-deg′ gdeg i , unit-deg′ gdeg i
      deg-entK i (suc k) m e =
        let (da , db) = deg-entK i k (suc m) (trans e (sym (+-suc″ k m)))
            (a , b) = entK i k
        in ∸c-deg m gdeg (dm a) (dp a) (deg-dm m a da) ,
           ∸c-deg m gdeg (dp b) (dm b) (deg-dp m b db)

      ------------------------------------------------------------------
      -- Positions of the atom table.

      private
        lt-t : ∀ j k → (j <ℕ suc (j + k)) ≡ true
        lt-t zero    k = refl
        lt-t (suc j) k = lt-t j k

        lt-f : ∀ n j → (suc (n + j) <ℕ suc n) ≡ false
        lt-f zero    j = refl
        lt-f (suc n) j = lt-f n j

        ∸-+ : ∀ j k → (j + k) ∸ j ≡ k
        ∸-+ zero    k = refl
        ∸-+ (suc j) k = ∸-+ j k

      ent-in : ∀ i j k → deg i ≡ j + k → ent i j ≡ entK i k
      ent-in i j k e rewrite e | lt-t j k | ∸-+ j k = refl

      ent-out : ∀ i j → ent i (suc (deg i + j)) ≡ (0c , 0c)
      ent-out i j rewrite lt-f (deg i) j = refl

      private
        lt-irr : ∀ n → (n <ℕ n) ≡ false
        lt-irr zero    = refl
        lt-irr (suc n) = lt-irr n

      ent-out0 : ∀ i → ent i (suc (deg i)) ≡ (0c , 0c)
      ent-out0 i rewrite lt-irr (deg i) = refl

      private
        lt-f2 : ∀ n k → (suc (n + k) <ℕ n) ≡ false
        lt-f2 zero    k = refl
        lt-f2 (suc n) k = lt-f2 n k

      ent-out2 : ∀ i k → ent i (suc (suc (deg i + k))) ≡ (0c , 0c)
      ent-out2 i k rewrite lt-f2 (deg i) k = refl

      Ent′ = Ent K 0
      Bd0 : ∀ (u : Vec Nat N) → dp 0c +c u ≡ dm 0c +c u
      Bd0 u = trans (cong (_+c u) (lin-0 bplus)) (cong (_+c u) (sym (lin-0 bminus)))

      Ent-zero : ∀ j (u : Vec Nat N) → Ent′ j (u , u) (0c , 0c)
      Ent-zero j u = prj-0 j gdeg , prj-0 j gdeg , Bd0 u , Bd0 u

      +-comm′ : ∀ m n → m + n ≡ n + m
      +-comm′ = +-comm

      -- Every consecutive pair of entries satisfies the cell conditions.
      ent-ok : ∀ i j → Ent′ (suc j) (ent i j) (ent i (suc j))
      ent-ok i j = go (cmp j (deg i))
        where
        data Cmp (j n : Nat) : Set where
          lt : ∀ k → n ≡ suc j + k → Cmp j n
          eq : n ≡ j → Cmp j n
          gt : ∀ k → j ≡ suc (n + k) → Cmp j n
        cmp : ∀ j n → Cmp j n
        cmp zero    zero    = eq refl
        cmp zero    (suc n) = lt n refl
        cmp (suc j) zero    = gt j refl
        cmp (suc j) (suc n) with cmp j n
        ... | lt k e = lt k (cong suc e)
        ... | eq e   = eq (cong suc e)
        ... | gt k e = gt k (cong suc e)
        go : Cmp j (deg i) → Ent′ (suc j) (ent i j) (ent i (suc j))
        go (lt k e) rewrite ent-in i (suc j) k e
                          | ent-in i j (suc k) (trans e (sym (+-suc″ j k))) =
          let c = entK i k
              (da , db) = deg-entK i k (suc j) (trans e (+-comm′ (suc j) k))
          in da , db , Bd⁻ c (Inv-entK i k) , Bd⁺ c (Inv-entK i k)
        go (eq e) rewrite ent-in i j 0 (trans e (sym (+-zero j)))
                        | sym e | ent-out0 i =
          Ent-zero (suc (deg i)) (unit i)
        go (gt k e) rewrite e | ent-out i k | ent-out2 i k =
          Ent-zero (suc (suc (deg i + k))) 0c

      ------------------------------------------------------------------
      -- The atom is a cell.

      Cnd-tab : ∀ {m} L (f : Nat → Vec Nat N × Vec Nat N) →
                (∀ j → Ent K L (suc j) (f j) (f (suc j))) →
                ∀ j → Cnd K L (suc j) (f j) (tabF {m} f (suc j))
      Cnd-tab {zero}  L f h j = tt
      Cnd-tab {suc m} L f h j = h j , Cnd-tab {m} L f h (suc j)

      Last-tab : ∀ L m (f : Nat → Vec Nat N × Vec Nat N) j →
                 fst (f (m + j)) ≡ snd (f (m + j)) → Last K L (tabF {suc m} f j)
      Last-tab L zero    f j p = p
      Last-tab L (suc m) f j p = Last-tab L m f (suc j) (subst (λ q → fst (f q) ≡ snd (f q)) (sym (+-suc″ m j)) p)

      -- Unitality of the basis (Steiner Def. 3.4), and atoms of dimension
      -- at most L.
      Unital : Nat → Set
      Unital i = (augm gdeg (fst (ent i 0)) ≡ 1) × (augm gdeg (snd (ent i 0)) ≡ 1)

      ent-last : ∀ L i k → L ≡ deg i + k → fst (ent i L) ≡ snd (ent i L)
      ent-last L i zero    e rewrite e | +-zero (deg i) | ent-in i (deg i) 0 (sym (+-zero (deg i))) = refl
      ent-last L i (suc k) e rewrite e | +-suc″ (deg i) k | ent-out i k = refl

      atom-cell : ∀ L i → Unital i → ∀ k → L ≡ deg i + k → IsCell K L (atomT L i)
      atom-cell L i (u⁻ , u⁺) k eL =
        (fst d0 , snd d0 , u⁻ , u⁺) ,
        Cnd-tab {L} L (ent i) (ent-ok i) 0 ,
        Last-tab L L (ent i) 0 (subst (λ q → fst (ent i q) ≡ snd (ent i q)) (sym (+-zero L)) (last k eL))
        where
        d0 : (pj 0 (fst (ent i 0)) ≡ fst (ent i 0)) × (pj 0 (snd (ent i 0)) ≡ snd (ent i 0))
        d0 rewrite ent-in i 0 (deg i) refl = deg-entK i (deg i) 0 (sym (+-zero (deg i)))
        last = ent-last L i
