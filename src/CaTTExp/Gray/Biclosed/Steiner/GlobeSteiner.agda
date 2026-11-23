------------------------------------------------------------------------
-- Globes are strong Steiner in every dimension (ledger C5e).
--
-- `globe-ss n : SS.StrongSteiner (globeFB n)` for all n.  Every
-- boundary of a globe cell is a single cell (`gb`), so each condition of
-- `StrongSteiner` reduces to facts about gb:
--   * gb β x is defined exactly when deg x ≥ 1, one degree down
--     (`gb-deg`, `gb-pos`);
--   * gb true x and gb false x are the target and the source cell of
--     the same index (`gbv`), so ∂⁺ and ∂⁻ have disjoint supports;
--   * gb β (tgt j) = gb β (src j) (`gb-ts`), so ∂∂ = 0;
--   * the height h(sᵢ) = i, h(top) = n, h(tᵢ) = n + 1 + (n − 1 − i)
--     strictly increases along <₁ (`up`).
-- No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.GlobeSteiner where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes
open import CaTTExp.Gray.Biclosed.Steiner.StrongSteiner

------------------------------------------------------------------------
-- Small facts

private
  <-suc : ∀ a → T (a <ℕ suc a)
  <-suc zero    = tt
  <-suc (suc a) = <-suc a

  <-step : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
  <-step zero    b       _ = tt
  <-step (suc a) (suc b) p = <-step a b p

  <-+r : ∀ a b c → T (a <ℕ b) → T (a <ℕ b + c)
  <-+r zero    (suc b) c _ = tt
  <-+r (suc a) (suc b) c p = <-+r a b c p

  <-+l : ∀ a b c → T (b <ℕ c) → T (a + b <ℕ a + c)
  <-+l zero    b c p = p
  <-+l (suc a) b c p = <-+l a b c p

  <-plus : ∀ a b → T (a <ℕ a + suc b)
  <-plus zero    b = tt
  <-plus (suc a) b = <-plus a b

  toℕ-< : ∀ {n} (i : Fin n) → T (toℕ i <ℕ n)
  toℕ-< {suc n} fz     = tt
  toℕ-< {suc n} (fs i) = toℕ-< i

  ==-T : ∀ {a b} → a ≡ b → T (a ==ℕ b)
  ==-T {a} refl = ==ℕ-refl a

  ∨-r : ∀ a {b} → T b → T (a ∨ b)
  ∨-r true  _ = tt
  ∨-r false p = p

  ∨-elim : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
  ∨-elim {true}  _ = inj₁ tt
  ∨-elim {false} p = inj₂ p

  suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-inj refl = refl

  T-subst : ∀ {b c} → b ≡ c → T b → T c
  T-subst refl p = p

------------------------------------------------------------------------
-- rv i = n − 1 − toℕ i

rv : ∀ {n} → Fin n → Nat
rv {suc n} fz     = n
rv {suc n} (fs i) = rv i

rv-inj : ∀ {n} (i : Fin n) → rv (inject₁ i) ≡ suc (rv i)
rv-inj {suc n} fz     = refl
rv-inj {suc n} (fs i) = rv-inj i

rv-max : ∀ n → rv (fromℕ n) ≡ 0
rv-max zero    = refl
rv-max (suc n) = rv-max n

------------------------------------------------------------------------
-- The structure of gb

gdeg-side : ∀ {n} β (i : Fin n) → gdeg (side β i) ≡ toℕ i
gdeg-side true  i = refl
gdeg-side false i = refl

gb-deg : ∀ {n} β (x w : GCell n) → gb β x ≡ just w → suc (gdeg w) ≡ gdeg x
gb-deg {zero}  β top          w ()
gb-deg {suc m} β top          _ refl = cong suc (trans (gdeg-side β (fromℕ m)) (toℕ-fromℕ m))
gb-deg         β (src fz)     w ()
gb-deg         β (src (fs i)) _ refl = cong suc (trans (gdeg-side β (inject₁ i)) (toℕ-inject₁ i))
gb-deg         β (tgt fz)     w ()
gb-deg         β (tgt (fs i)) _ refl = cong suc (trans (gdeg-side β (inject₁ i)) (toℕ-inject₁ i))

gb-pos : ∀ {n} β (x : GCell n) d → gdeg x ≡ suc d →
         Σ (GCell n) (λ w → (gb β x ≡ just w) × (gdeg w ≡ d))
gb-pos {zero}  β top          d ()
gb-pos {suc m} β top          d e =
  side β (fromℕ m) , refl , trans (gdeg-side β (fromℕ m)) (trans (toℕ-fromℕ m) (suc-inj e))
gb-pos         β (src fz)     d ()
gb-pos         β (src (fs i)) d e =
  side β (inject₁ i) , refl , trans (gdeg-side β (inject₁ i)) (trans (toℕ-inject₁ i) (suc-inj e))
gb-pos         β (tgt fz)     d ()
gb-pos         β (tgt (fs i)) d e =
  side β (inject₁ i) , refl , trans (gdeg-side β (inject₁ i)) (trans (toℕ-inject₁ i) (suc-inj e))

-- the two boundaries: both absent, or the target and source of one index
data GBV {n} (x : GCell n) : Set where
  none : gb true x ≡ nothing → gb false x ≡ nothing → GBV x
  some : ∀ j → gb true x ≡ just (tgt j) → gb false x ≡ just (src j) → GBV x

gbv : ∀ {n} (x : GCell n) → GBV x
gbv {zero}  top      = none refl refl
gbv {suc m} top      = some (fromℕ m) refl refl
gbv (src fz)         = none refl refl
gbv (src (fs i))     = some (inject₁ i) refl refl
gbv (tgt fz)         = none refl refl
gbv (tgt (fs i))     = some (inject₁ i) refl refl

gb-ts : ∀ {n} β (j : Fin n) → gb β (tgt j) ≡ gb β (src j)
gb-ts β fz     = refl
gb-ts β (fs j) = refl

------------------------------------------------------------------------
-- The height: h(sᵢ) = i, h(top) = n, h(tᵢ) = n + 1 + rv i

hG : ∀ {n} → GCell n → Nat
hG {n} top     = n
hG     (src i) = toℕ i
hG {n} (tgt i) = n + suc (rv i)

-- x ∈ ∂⁻y
hA : ∀ {n} (y x : GCell n) → gb false y ≡ just x → T (hG x <ℕ hG y)
hA {zero}  top          x ()
hA {suc m} top          _ refl = T-subst (cong (λ a → a <ℕ suc m) (sym (toℕ-fromℕ m))) (<-suc m)
hA         (src fz)     x ()
hA         (src (fs i)) _ refl = T-subst (cong (λ a → a <ℕ suc (toℕ i)) (sym (toℕ-inject₁ i))) (<-suc (toℕ i))
hA         (tgt fz)     x ()
hA {suc m} (tgt (fs i)) _ refl =
  T-subst (cong (λ a → a <ℕ suc m + suc (rv i)) (sym (toℕ-inject₁ i)))
          (<-+r (toℕ i) (suc m) (suc (rv i)) (<-step (toℕ i) m (toℕ-< i)))

-- y ∈ ∂⁺x
hB : ∀ {n} (x y : GCell n) → gb true x ≡ just y → T (hG x <ℕ hG y)
hB {zero}  top          y ()
hB {suc m} top          _ refl = T-subst (cong (λ a → suc m <ℕ suc m + suc a) (sym (rv-max m))) (<-plus (suc m) 0)
hB         (src fz)     y ()
hB {suc m} (src (fs i)) _ refl = <-+r (suc (toℕ i)) (suc m) (suc (rv (inject₁ i))) (toℕ-< i)
hB         (tgt fz)     y ()
hB {suc m} (tgt (fs i)) _ refl =
  T-subst (cong (λ a → suc m + suc (rv i) <ℕ suc m + suc a) (sym (rv-inj i)))
          (<-+l (suc m) (suc (rv i)) (suc (suc (rv i))) (<-suc (rv i)))

------------------------------------------------------------------------
-- The conditions for λDⁿ

module _ (n : Nat) where
  private
    E  = enumG n
    cs = els E
    I  = ind E

  open SS (globeFB n)

  bindM : Maybe (GCell n) → (GCell n → Maybe (GCell n)) → Maybe (GCell n)
  bindM nothing  f = nothing
  bindM (just x) f = f x

  mb : Maybe (GCell n) → (GCell n → Nat) → Nat
  mb nothing  F = 0
  mb (just w) F = F w

  ΣM : ∀ m (F : GCell n → Nat) → Σl cs (λ y → I m y * F y) ≡ mb m F
  ΣM nothing  F = Σ-0 cs
  ΣM (just w) F = Σ-δ E w F

  ΣI : ∀ m → Σl cs (I m) ≡ mb m (λ _ → 1)
  ΣI nothing  = Σ-0 cs
  ΣI (just w) = count E w

  ind-nz : ∀ m w → T (nz (I m w)) → m ≡ just w
  ind-nz nothing  w ()
  ind-nz (just v) w p = go (eqb E v w) refl p
    where
      go : ∀ b → eqb E v w ≡ b → T (nz (if b then 1 else 0)) → just v ≡ just w
      go true  e _ = cong just (eqb-sound E (T-subst (sym e) tt))
      go false e ()

  ind-0 : ∀ β x y → (suc (gdeg y) ≡ gdeg x → ⊥) → I (gb β x) y ≡ 0
  ind-0 β x y ne = go (gb β x) refl
    where
      go : ∀ m → gb β x ≡ m → I m y ≡ 0
      go nothing  _ = refl
      go (just w) e = go′ (eqb E w y) refl
        where
          go′ : ∀ b → eqb E w y ≡ b → (if b then 1 else 0) ≡ 0
          go′ true  e′ with eqb-sound E {w} {y} (T-subst (sym e′) tt)
          ... | refl = ⊥-elim (ne (gb-deg β x w e))
          go′ false e′ = refl

  --------------------------------------------------------------------
  -- degrees

  private
    deg-lemma : ∀ a b k → a ≡ 0 → b ≡ 0 → T ((not (nz a) ∧ not (nz b)) ∨ k)
    deg-lemma .0 .0 k refl refl = tt

  degs : ∀ x y → T (degAt x y)
  degs x y = go (suc (gdeg y) ==ℕ gdeg x) refl
    where
      go : ∀ b → (suc (gdeg y) ==ℕ gdeg x) ≡ b → T (degAt x y)
      go true  e = ∨-r (not (nz (I (gb true x) y)) ∧ not (nz (I (gb false x) y))) (T-subst (sym e) tt)
      go false e = deg-lemma _ _ _ (ind-0 true x y ne) (ind-0 false x y ne)
        where
          ne : suc (gdeg y) ≡ gdeg x → ⊥
          ne p = ==-false (suc (gdeg y)) (gdeg x) e p

  --------------------------------------------------------------------
  -- disjoint supports

  private
    ts : ∀ (i j : Fin n) y → I (just (tgt i)) y * I (just (src j)) y ≡ 0
    ts i j top     = refl
    ts i j (src k) = refl
    ts i j (tgt k) = *-zero (if eqFin i k then 1 else 0)

    disj-eq : ∀ x y → I (gb true x) y * I (gb false x) y ≡ 0
    disj-eq x y with gbv x
    ... | none et es rewrite et = refl
    ... | some j et es rewrite et | es = ts j j y

  disj : ∀ x y → T (disjAt x y)
  disj x y = ==-T (disj-eq x y)

  --------------------------------------------------------------------
  -- ∂∂ = 0

  private
    ts-ind : ∀ β (j : Fin n) z → I (gb β (tgt j)) z ≡ I (gb β (src j)) z
    ts-ind β j z = cong (λ m → I m z) (gb-ts β j)

    chain-eq : ∀ x z →
      Σl cs (λ y → I (gb true x) y * I (gb true y) z + I (gb false x) y * I (gb false y) z) ≡
      Σl cs (λ y → I (gb true x) y * I (gb false y) z + I (gb false x) y * I (gb true y) z)
    chain-eq x z =
      trans (Σ-+ cs (λ y → I (gb true x) y * I (gb true y) z) (λ y → I (gb false x) y * I (gb false y) z))
      (trans (cong₂ _+_ (ΣM (gb true x) (λ y → I (gb true y) z)) (ΣM (gb false x) (λ y → I (gb false y) z)))
      (trans (core (gbv x))
      (sym (trans (Σ-+ cs (λ y → I (gb true x) y * I (gb false y) z) (λ y → I (gb false x) y * I (gb true y) z))
                  (cong₂ _+_ (ΣM (gb true x) (λ y → I (gb false y) z)) (ΣM (gb false x) (λ y → I (gb true y) z)))))))
      where
        core : GBV x →
               mb (gb true x) (λ y → I (gb true y) z) + mb (gb false x) (λ y → I (gb false y) z) ≡
               mb (gb true x) (λ y → I (gb false y) z) + mb (gb false x) (λ y → I (gb true y) z)
        core (none et es) rewrite et | es = refl
        core (some j et es) rewrite et | es =
          trans (cong (_+ I (gb false (src j)) z) (ts-ind true j z))
          (trans (+-comm (I (gb true (src j)) z) (I (gb false (src j)) z))
                 (cong (_+ I (gb true (src j)) z) (sym (ts-ind false j z))))

  chain : ∀ x z → T (chainAt x z)
  chain x z = ==-T (chain-eq x z)

  --------------------------------------------------------------------
  -- augmentation

  private
    aug-eq : ∀ x → Σl cs (I (gb true x)) ≡ Σl cs (I (gb false x))
    aug-eq x with gbv x
    ... | none et es rewrite et | es = refl
    ... | some j et es rewrite et | es = trans (count E (tgt j)) (sym (count E (src j)))

  aug : ∀ x → T (augAt x)
  aug x = ∨-r (not (gdeg x ==ℕ 1)) (==-T (aug-eq x))

  --------------------------------------------------------------------
  -- unitality

  iterB : Bool → Nat → Maybe (GCell n) → Maybe (GCell n)
  iterB α zero    m = m
  iterB α (suc k) m = bindM (iterB α k m) (gb α)

  private
    ∸-disj : ∀ a b → a * b ≡ 0 → a ∸ b ≡ a
    ∸-disj zero    zero    _  = refl
    ∸-disj zero    (suc b) _  = refl
    ∸-disj (suc a) zero    _  = refl
    ∸-disj (suc a) (suc b) ()

    part-disj : ∀ α w z → part α (I (gb true w) z) (I (gb false w) z) ≡ I (gb α w) z
    part-disj true  w z = ∸-disj _ _ (disj-eq w z)
    part-disj false w z = ∸-disj _ _ (trans (*-comm (I (gb false w) z) (I (gb true w) z)) (disj-eq w z))

    mb-bind : ∀ α m z → part α (mb m (λ y → I (gb true y) z)) (mb m (λ y → I (gb false y) z)) ≡ I (bindM m (gb α)) z
    mb-bind α nothing  z = part0 α
      where part0 : ∀ α → part α 0 0 ≡ 0
            part0 true  = refl
            part0 false = refl
    mb-bind α (just w) z = part-disj α w z

    down-eq : ∀ α k m z → down α k (I m) z ≡ I (iterB α k m) z
    down-eq α zero    m z = refl
    down-eq α (suc k) m z =
      trans (cong₂ (part α)
        (trans (Σ-cong cs (λ y → cong (_* I (gb true y) z) (down-eq α k m y))) (ΣM (iterB α k m) (λ y → I (gb true y) z)))
        (trans (Σ-cong cs (λ y → cong (_* I (gb false y) z) (down-eq α k m y))) (ΣM (iterB α k m) (λ y → I (gb false y) z))))
      (mb-bind α (iterB α k m) z)

    iter-just : ∀ α k d (x : GCell n) → gdeg x ≡ k + d →
                Σ (GCell n) (λ w → (iterB α k (just x) ≡ just w) × (gdeg w ≡ d))
    iter-just α zero    d x e = x , refl , e
    iter-just α (suc k) d x e with iter-just α k (suc d) x (trans e (sym (+-suc k d)))
    ... | w′ , p , dw′ with gb-pos α w′ d dw′
    ...   | w , q , dw rewrite p = w , q , dw

  unital : ∀ α x → T (unitAt α x)
  unital α x with iter-just α (gdeg x) 0 x (sym (+-zero (gdeg x)))
  ... | w , p , _ =
    ==-T (trans (Σ-cong cs (down-eq α (gdeg x) (just x)))
         (trans (cong (λ m → Σl cs (I m)) p) (count E w)))

  --------------------------------------------------------------------
  -- the height

  private
    up : ∀ x y → T (lt₁ x y) → T (hG x <ℕ hG y)
    up x y l with ∨-elim l
    ... | inj₁ p = hA y x (ind-nz (gb false y) x p)
    ... | inj₂ p = hB x y (ind-nz (gb true x) y p)

  globe-ss : StrongSteiner
  globe-ss = record
    { degs = degs ; disj = disj ; chain = chain ; aug = aug ; unital = unital
    ; height = record { h = hG ; up = up } }

-- every globe is strong Steiner
globes-all : ∀ n → SS.StrongSteiner (globeFB n)
globes-all = globe-ss
