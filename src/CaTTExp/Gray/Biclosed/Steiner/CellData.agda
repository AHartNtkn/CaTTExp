------------------------------------------------------------------------
-- Cell data for a basis element (ledger C5f, unitality).
--
-- For a basis element i of degree P, Steiner's atom ⟨i⟩ is the family
-- of chains ⟨i⟩^α_p, p ≤ P, obtained from i by taking the positive or
-- negative part of the boundary P − p times (`SS.down`).  `CellData B i`
-- records the facts about such a family that unitality of a tensor
-- needs:
--   * each chain ch α p is concentrated in degree p, is i at p = P and
--     vanishes above P;
--   * globularity, as an equation of natural numbers:
--       ∂⁺ ch α (p+1) + ch⁻ p = ∂⁻ ch α (p+1) + ch⁺ p,
--     i.e. ∂ (ch α (p+1)) = ch⁺ p − ch⁻ p;
--   * ch⁺ p and ch⁻ p have disjoint supports for p < P;
--   * ε (ch α 0) = 1.
-- From cell data, ch α p is the positive or negative part of
-- ∂ (ch α (p+1)) (`rec`), so the chains are those computed by `down`
-- (`down-ch`), and the basis element is unital (`cd-unital`).
-- Conversely, in a basis satisfying the degree condition, ∂∂ = 0 and
-- unitality, every element has cell data (`atomCD`).
-- No postulates.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.CellData where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB; Cell; enumC; fdeg; fbd)
open import CaTTExp.Gray.Biclosed.Steiner.StrongSteiner

------------------------------------------------------------------------
-- Arithmetic

T-subst : ∀ {b c} → b ≡ c → T b → T c
T-subst refl p = p

==-T : ∀ {m n} → m ≡ n → T (m ==ℕ n)
==-T {m} refl = ==ℕ-refl m

nz-+ : ∀ a b → T (not ((a + b) ==ℕ 0)) → T (not (a ==ℕ 0)) ⊎ T (not (b ==ℕ 0))
nz-+ zero    b p = inj₂ p
nz-+ (suc a) b p = inj₁ tt

nz-*ˡ : ∀ a b → T (not ((a * b) ==ℕ 0)) → T (not (a ==ℕ 0))
nz-*ˡ zero    b ()
nz-*ˡ (suc a) b _ = tt

nz-*ʳ : ∀ a b → T (not ((a * b) ==ℕ 0)) → T (not (b ==ℕ 0))
nz-*ʳ a b p = nz-*ˡ b a (T-subst (cong (λ z → not (z ==ℕ 0)) (*-comm a b)) p)

nz-suc : ∀ {n m} → n ≡ suc m → T (not (n ==ℕ 0))
nz-suc refl = tt

mul0 : ∀ p q → p * q ≡ 0 → (p ≡ 0) ⊎ (q ≡ 0)
mul0 zero    q       _ = inj₁ refl
mul0 (suc p) zero    _ = inj₂ refl
mul0 (suc p) (suc q) ()

+∸ : ∀ a b → (a + b) ∸ a ≡ b
+∸ zero    b = refl
+∸ (suc a) b = +∸ a b

∸+ : ∀ a b → a ∸ (a + b) ≡ 0
∸+ zero    zero    = refl
∸+ zero    (suc b) = refl
∸+ (suc a) b = ∸+ a b

∸-cancelˡ : ∀ b c d → (b + c) ∸ (b + d) ≡ c ∸ d
∸-cancelˡ zero    c d = refl
∸-cancelˡ (suc b) c d = ∸-cancelˡ b c d

-- a − b = c − d as integers gives a ∸ b ≡ c ∸ d
∸-diff : ∀ a b c d → a + d ≡ b + c → a ∸ b ≡ c ∸ d
∸-diff a b c d e =
  trans (sym (∸-cancelˡ d a b))
  (trans (cong (_∸ (d + b)) (trans (+-comm d a) e))
  (trans (cong ((b + c) ∸_) (+-comm d b)) (∸-cancelˡ b c d)))

-- both sides are max m n
∸-max : ∀ m n → m + (n ∸ m) ≡ n + (m ∸ n)
∸-max zero    zero    = refl
∸-max zero    (suc n) = cong suc (sym (+-zero n))
∸-max (suc m) zero    = cong suc (+-zero m)
∸-max (suc m) (suc n) = cong suc (∸-max m n)

∸-disj : ∀ m n → (m ∸ n) * (n ∸ m) ≡ 0
∸-disj zero    zero    = refl
∸-disj zero    (suc n) = refl
∸-disj (suc m) zero    = *-zero (suc m)
∸-disj (suc m) (suc n) = ∸-disj m n

-- p − n = x − y with x, y of disjoint supports: the parts are x and y
part-eq : ∀ p n x y → p + y ≡ n + x → x * y ≡ 0 → (p ∸ n ≡ x) × (n ∸ p ≡ y)
part-eq p n x y e z with mul0 x y z
... | inj₁ refl = (trans (cong (p ∸_) n′) (∸+ p y)) , (trans (cong (_∸ p) n′) (+∸ p y))
  where n′ : n ≡ p + y
        n′ = sym (trans e (+-zero n))
... | inj₂ refl = trans (cong (_∸ n) p′) (+∸ n x) , trans (cong (n ∸_) p′) (∸+ n x)
  where p′ : p ≡ n + x
        p′ = trans (sym (+-zero p)) e

-- the two parts of D⁺ and of D⁻, when D⁺ ≡ D⁻ as integers
part-glob : ∀ Pt Nt Pf Nf → Pt + Nf ≡ Nt + Pf →
            (Pt + (Nf ∸ Pf) ≡ Nt + (Pt ∸ Nt)) × (Pf + (Nf ∸ Pf) ≡ Nf + (Pt ∸ Nt))
part-glob Pt Nt Pf Nf e =
  trans (cong (Pt +_) d₂) (∸-max Pt Nt) ,
  trans (∸-max Pf Nf) (cong (Nf +_) (sym d₁))
  where
    d₁ : Pt ∸ Nt ≡ Pf ∸ Nf
    d₁ = ∸-diff Pt Nt Pf Nf e
    d₂ : Nf ∸ Pf ≡ Nt ∸ Pt
    d₂ = ∸-diff Nf Pf Nt Pt (trans (+-comm Nf Pt) (trans e (+-comm Nt Pf)))

part-glob-disj : ∀ Pt Nt Pf Nf → Pt + Nf ≡ Nt + Pf → (Pt ∸ Nt) * (Nf ∸ Pf) ≡ 0
part-glob-disj Pt Nt Pf Nf e = trans (cong (_* (Nf ∸ Pf)) (∸-diff Pt Nt Pf Nf e)) (∸-disj Pf Nf)

-- b + c = a + d, from three equations sharing the a's
cancel4 : ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ →
          a₁ + b₁ ≡ a₂ + b₂ → a₃ + b₃ ≡ a₄ + b₄ → a₁ + a₄ ≡ a₃ + a₂ → b₄ + b₁ ≡ b₂ + b₃
cancel4 a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ e₁ e₂ e₃ =
  +-cancelˡ (a₁ + a₄)
    (trans (cong ((a₁ + a₄) +_) (+-comm b₄ b₁))
    (trans (+-inter a₁ a₄ b₁ b₄)
    (trans (cong₂ _+_ e₁ (sym e₂))
    (trans (+-inter a₂ b₂ a₃ b₃)
           (cong (_+ (b₂ + b₃)) (trans (+-comm a₂ a₃) (sym e₃)))))))

<-step : ∀ a b → T (a <ℕ b) → T (a <ℕ suc b)
<-step zero    b       _ = tt
<-step (suc a) zero    ()
<-step (suc a) (suc b) p = <-step a b p

∸-suc : ∀ P r → T (r <ℕ P) → P ∸ r ≡ suc (P ∸ suc r)
∸-suc (suc P) zero    _ = refl
∸-suc (suc P) (suc r) p = ∸-suc P r p

∸-self : ∀ P → P ∸ P ≡ 0
∸-self zero    = refl
∸-self (suc P) = ∸-self P

∸-≥ : ∀ P p → T (not (p <ℕ P)) → P ∸ p ≡ 0
∸-≥ zero    zero    _ = refl
∸-≥ zero    (suc p) _ = refl
∸-≥ (suc P) zero    ()
∸-≥ (suc P) (suc p) q = ∸-≥ P p q

<-self : ∀ n → T (n <ℕ suc n)
<-self zero    = tt
<-self (suc n) = <-self n

∸-lt : ∀ P r → T ((P ∸ r) <ℕ suc P)
∸-lt zero    zero    = tt
∸-lt zero    (suc r) = tt
∸-lt (suc P) zero    = <-self P
∸-lt (suc P) (suc r) = <-step (P ∸ r) (suc P) (∸-lt P r)

∸-∸ : ∀ P r → T (r <ℕ suc P) → P ∸ (P ∸ r) ≡ r
∸-∸ P       zero    _ = ∸-self P
∸-∸ zero    (suc r) ()
∸-∸ (suc P) (suc r) q = trans (∸-suc (suc P) (P ∸ r) (∸-lt P r)) (cong suc (∸-∸ P r q))

notT : ∀ {p} → T (not p) → T p → ⊥
notT {true}  () _
notT {false} _ ()

∨-elim′ : ∀ {p q} → T (p ∨ q) → T p ⊎ T q
∨-elim′ {true}  _ = inj₁ tt
∨-elim′ {false} r = inj₂ r

------------------------------------------------------------------------
-- Selection by a Boolean

sel : Bool → Nat → Nat
sel true  n = n
sel false n = 0

sel-T : ∀ {b} n → T b → sel b n ≡ n
sel-T {true} n _ = refl

sel-F : ∀ {b} n → b ≡ false → sel b n ≡ 0
sel-F n refl = refl

------------------------------------------------------------------------
-- Cell data

module CD (B : FB) where
  open SS B
  E  = enumC B
  cs = els E
  d  = fbd B
  dg = fdeg B

  -- the boundary ∂^β of a chain before taking parts
  dP : Bool → Chain → Chain
  dP β c y = Σl cs (λ x → c x * d β x y)

  record CellData (i : Cell B) : Set where
    field
      ch    : Bool → Nat → Chain
      conc  : ∀ α p j → T (nz (ch α p j)) → dg j ≡ p
      top   : ∀ α j → ch α (dg i) j ≡ δ E i j
      above : ∀ α p j → T (dg i <ℕ p) → ch α p j ≡ 0
      glob  : ∀ α p k → dP true (ch α (suc p)) k + ch false p k ≡ dP false (ch α (suc p)) k + ch true p k
      disj  : ∀ p j → T (p <ℕ dg i) → ch true p j * ch false p j ≡ 0
      unit  : ∀ α → Σl cs (ch α 0) ≡ 1

  module _ {i : Cell B} (C : CellData i) where
    open CellData C

    private
      P = dg i

    -- the chains are the parts of the boundary of the next one
    rec : ∀ α p j → T (p <ℕ P) → ch α p j ≡ bdC α (ch α (suc p)) j
    rec true  p j q = sym (fst (part-eq (dP true (ch true (suc p)) j) (dP false (ch true (suc p)) j)
                                         (ch true p j) (ch false p j) (glob true p j) (disj p j q)))
    rec false p j q = sym (snd (part-eq (dP true (ch false (suc p)) j) (dP false (ch false (suc p)) j)
                                         (ch true p j) (ch false p j) (glob false p j) (disj p j q)))

    bdC-cong : ∀ α (c c′ : Chain) → (∀ x → c x ≡ c′ x) → ∀ y → bdC α c y ≡ bdC α c′ y
    bdC-cong α c c′ e y =
      cong₂ (part α) (Σ-cong cs (λ x → cong (_* d true x y) (e x)))
                     (Σ-cong cs (λ x → cong (_* d false x y) (e x)))

    down-ch : ∀ α r → T (r <ℕ suc P) → ∀ j → down α r (δ E i) j ≡ ch α (P ∸ r) j
    down-ch α zero    _ j = sym (top α j)
    down-ch α (suc r) q j =
      trans (bdC-cong α (down α r (δ E i)) (ch α (P ∸ r)) (down-ch α r (<-step r P q)) j)
      (trans (bdC-cong α (ch α (P ∸ r)) (ch α (suc (P ∸ suc r)))
                       (λ x → cong (λ n → ch α n x) (∸-suc P r q)) j)
             (sym (rec α (P ∸ suc r) j (lt P r q))))
      where lt : ∀ P r → T (suc r <ℕ suc P) → T ((P ∸ suc r) <ℕ P)
            lt zero    r       ()
            lt (suc P) zero    _ = <-self P
            lt (suc P) (suc r) q = <-step (P ∸ suc r) P (lt P r q)

    cd-unital : ∀ α → T (unitAt α i)
    cd-unital α = ==-T (trans (Σ-cong cs (down-ch α P (<-self P)))
                       (trans (Σ-cong cs (λ j → cong (λ n → ch α n j) (∸-self P))) (unit α)))

  ----------------------------------------------------------------------
  -- Cell data of a basis element, from the Steiner conditions

  -- a nonzero entry allowed by the degree condition is one degree down
  deg-ofB : ∀ x y α → T (degAt x y) → T (nz (d α x y)) → suc (dg y) ≡ dg x
  deg-ofB x y α dg′ n with ∨-elim′ {not (nz (d true x y)) ∧ not (nz (d false x y))} {suc (dg y) ==ℕ dg x} dg′
  ... | inj₂ q = ==ℕ-sound _ _ q
  deg-ofB x y true  dg′ n | inj₁ p = ⊥-elim (notT (∧-fst p) n)
  deg-ofB x y false dg′ n | inj₁ p = ⊥-elim (notT (∧-snd {not (nz (d true x y))} p) n)

  -- the boundary of a chain concentrated in degree n + 1 is concentrated in degree n
  dP-conc : (∀ x y → T (degAt x y)) → ∀ (c : Chain) n → (∀ x → T (nz (c x)) → dg x ≡ suc n) →
            ∀ β j → T (nz (dP β c j)) → dg j ≡ n
  dP-conc dgs c n cc β j = go cs
    where
      go : ∀ xs → T (nz (Σl xs (λ x → c x * d β x j))) → dg j ≡ n
      go []       ()
      go (x ∷ xs) p with nz-+ (c x * d β x j) (Σl xs (λ x → c x * d β x j)) p
      ... | inj₂ q = go xs q
      ... | inj₁ q = suc-inj (trans (deg-ofB x j β (dgs x j) (nz-*ʳ (c x) (d β x j) q)) (cc x (nz-*ˡ (c x) (d β x j) q)))
        where suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
              suc-inj refl = refl

  -- ∂∂ = 0, extended linearly to chains
  dd : ∀ (c : Chain) β γ z → dP γ (dP β c) z ≡ Σl cs (λ x → c x * Σl cs (λ y → d β x y * d γ y z))
  dd c β γ z =
    trans (Σ-cong cs (λ y → Σ-*ʳ cs (d γ y z) (λ x → c x * d β x y)))
    (trans (Σ-swap cs cs (λ y x → (c x * d β x y) * d γ y z))
           (Σ-cong cs (λ x → trans (Σ-cong cs (λ y → *-assoc (c x) (d β x y) (d γ y z)))
                                   (sym (Σ-*ˡ cs (c x) (λ y → d β x y * d γ y z))))))

  chain-lin : (∀ x z → T (chainAt x z)) → ∀ (c : Chain) z →
    dP true (dP true c) z + dP false (dP false c) z ≡ dP false (dP true c) z + dP true (dP false c) z
  chain-lin chs c z =
    trans (cong₂ _+_ (dd c true true z) (dd c false false z))
    (trans (sym (Σ-+ cs (λ x → c x * Σl cs (λ y → d true x y * d true y z))
                        (λ x → c x * Σl cs (λ y → d false x y * d false y z))))
    (trans (Σ-cong cs (λ x →
             trans (sym (distribˡ (c x) (Σl cs (λ y → d true x y * d true y z)) (Σl cs (λ y → d false x y * d false y z))))
             (trans (cong (c x *_) (ce x))
                    (distribˡ (c x) (Σl cs (λ y → d true x y * d false y z)) (Σl cs (λ y → d false x y * d true y z))))))
    (trans (Σ-+ cs (λ x → c x * Σl cs (λ y → d true x y * d false y z))
                   (λ x → c x * Σl cs (λ y → d false x y * d true y z)))
           (sym (cong₂ _+_ (dd c true false z) (dd c false true z))))))
    where
      ce : ∀ x → Σl cs (λ y → d true x y * d true y z) + Σl cs (λ y → d false x y * d false y z) ≡
                 Σl cs (λ y → d true x y * d false y z) + Σl cs (λ y → d false x y * d true y z)
      ce x = trans (sym (Σ-+ cs (λ y → d true x y * d true y z) (λ y → d false x y * d false y z)))
             (trans (==ℕ-sound _ _ (chs x z))
                    (Σ-+ cs (λ y → d true x y * d false y z) (λ y → d false x y * d true y z)))

  dP-+ : ∀ β (c c′ : Chain) z → dP β (λ y → c y + c′ y) z ≡ dP β c z + dP β c′ z
  dP-+ β c c′ z = trans (Σ-cong cs (λ y → distribʳ (c y) (c′ y) (d β y z))) (Σ-+ cs (λ y → c y * d β y z) (λ y → c′ y * d β y z))

  dP-cong : ∀ β (c c′ : Chain) → (∀ y → c y ≡ c′ y) → ∀ z → dP β c z ≡ dP β c′ z
  dP-cong β c c′ e z = Σ-cong cs (λ y → cong (_* d β y z) (e y))

  module Atom (dgs : ∀ x y → T (degAt x y)) (chs : ∀ x z → T (chainAt x z))
              (uns : ∀ α x → T (unitAt α x)) (i : Cell B) where
    P = dg i

    e : Bool → Nat → Chain
    e α r = down α r (δ E i)

    -- ∂ (e⁺ r) = ∂ (e⁻ r) as integers
    Equiv : Nat → Set
    Equiv r = ∀ k → dP true (e true r) k + dP false (e false r) k ≡ dP false (e true r) k + dP true (e false r) k

    -- globularity at depth r
    R : Nat → Set
    R r = ∀ α k → dP true (e α r) k + e false (suc r) k ≡ dP false (e α r) k + e true (suc r) k

    equiv→R : ∀ r → Equiv r → R r
    equiv→R r eq true  k = fst (part-glob (dP true (e true r) k) (dP false (e true r) k)
                                          (dP true (e false r) k) (dP false (e false r) k) (eq k))
    equiv→R r eq false k = snd (part-glob (dP true (e true r) k) (dP false (e true r) k)
                                          (dP true (e false r) k) (dP false (e false r) k) (eq k))

    R→equiv : ∀ r → R r → Equiv (suc r)
    R→equiv r g z =
      sym (cancel4 (dP true (dP true c) z) (dP true (dP false c) z) (dP false (dP true c) z) (dP false (dP false c) z)
                   (dP true (e false (suc r)) z) (dP true (e true (suc r)) z)
                   (dP false (e false (suc r)) z) (dP false (e true (suc r)) z)
                   (lin true) (lin false) (chain-lin chs c z))
      where
        c = e true r
        -- ∂^γ of the depth-r globularity equation for α = true
        lin : ∀ γ → dP γ (dP true c) z + dP γ (e false (suc r)) z ≡ dP γ (dP false c) z + dP γ (e true (suc r)) z
        lin γ = trans (sym (dP-+ γ (dP true c) (e false (suc r)) z))
                (trans (dP-cong γ _ _ (g true) z) (dP-+ γ (dP false c) (e true (suc r)) z))

    equiv : ∀ r → Equiv r
    equiv zero    k = +-comm (dP true (δ E i) k) (dP false (δ E i) k)
    equiv (suc r) = R→equiv r (equiv→R r (equiv r))

    -- e α r is concentrated in degree P ∸ r, for r ≤ P
    e-conc : ∀ α r → T (r <ℕ suc P) → ∀ j → T (nz (e α r j)) → dg j ≡ P ∸ r
    e-conc α zero    _ j n = cong dg (sym (eqb-sound E (eqT (eqb E i j) n)))
      where eqT : ∀ b → T (nz (if b then 1 else 0)) → T b
            eqT true  _ = tt
            eqT false ()
    e-conc α (suc r) q j n =
      dP-conc dgs (e α r) (P ∸ suc r) (λ x m → trans (e-conc α r (<-step r P q) x m) (∸-suc P r q))
              α j (pn α n)
      where
        pn : ∀ α → T (nz (bdC α (e α r) j)) → T (nz (dP α (e α r) j))
        pn true  m = ∸-nz (dP true (e true r) j) (dP false (e true r) j) m
          where ∸-nz : ∀ a b → T (nz (a ∸ b)) → T (nz a)
                ∸-nz zero    zero    ()
                ∸-nz zero    (suc b) ()
                ∸-nz (suc a) b       _ = tt
        pn false m = ∸-nz (dP false (e false r) j) (dP true (e false r) j) m
          where ∸-nz : ∀ a b → T (nz (a ∸ b)) → T (nz a)
                ∸-nz zero    zero    ()
                ∸-nz zero    (suc b) ()
                ∸-nz (suc a) b       _ = tt

    ch : Bool → Nat → Chain
    ch α p j = sel (p <ℕ suc P) (e α (P ∸ p) j)

    ch-lo : ∀ α p j → T (p <ℕ suc P) → ch α p j ≡ e α (P ∸ p) j
    ch-lo α p j q = sel-T (e α (P ∸ p) j) q

    ch-hi : ∀ α p j → (p <ℕ suc P) ≡ false → ch α p j ≡ 0
    ch-hi α p j q = sel-F (e α (P ∸ p) j) q

    private
      lt-dec : ∀ a b → ((a <ℕ b) ≡ true) ⊎ ((a <ℕ b) ≡ false)
      lt-dec a b with a <ℕ b
      ... | true  = inj₁ refl
      ... | false = inj₂ refl

      ≡T : ∀ {b} → b ≡ true → T b
      ≡T refl = tt

      ≡F : ∀ {b} → b ≡ false → T (not b)
      ≡F refl = tt

      F≡ : ∀ {b} → T (not b) → b ≡ false
      F≡ {false} _ = refl

      lt-asym : ∀ a b → T (a <ℕ b) → (b <ℕ suc a) ≡ false
      lt-asym zero    (suc b) _ = refl
      lt-asym (suc a) (suc b) p = lt-asym a b p

    a-conc : ∀ α p j → T (nz (ch α p j)) → dg j ≡ p
    a-conc α p j n with lt-dec p (suc P)
    ... | inj₂ h = ⊥-elim (z (T-subst (cong nz (ch-hi α p j h)) n))
      where z : T (nz 0) → ⊥
            z ()
    ... | inj₁ h = trans (e-conc α (P ∸ p) (∸-lt P p) j (T-subst (cong nz (ch-lo α p j (≡T h))) n))
                         (∸-∸ P p (≡T h))

    a-top : ∀ α j → ch α P j ≡ δ E i j
    a-top α j = trans (ch-lo α P j (<-self P)) (cong (λ n → e α n j) (∸-self P))

    a-above : ∀ α p j → T (P <ℕ p) → ch α p j ≡ 0
    a-above α p j q = ch-hi α p j (lt-asym P p q)

    a-glob : ∀ α p k → dP true (ch α (suc p)) k + ch false p k ≡ dP false (ch α (suc p)) k + ch true p k
    a-glob α p k with lt-dec p P
    ... | inj₁ h =
      trans (cong₂ _+_ (dP-cong true _ _ (λ j → ch-lo α (suc p) j (≡T h)) k) (lo false))
      (trans (equiv→R (P ∸ suc p) (equiv (P ∸ suc p)) α k)
             (sym (cong₂ _+_ (dP-cong false _ _ (λ j → ch-lo α (suc p) j (≡T h)) k) (lo true))))
      where
        lo : ∀ γ → ch γ p k ≡ e γ (suc (P ∸ suc p)) k
        lo γ = trans (ch-lo γ p k (<-step p P (≡T h))) (cong (λ n → e γ n k) (∸-suc P p (≡T h)))
    ... | inj₂ h =
      trans (cong (_+ ch false p k) (z true))
      (trans (cong (0 +_) same) (cong (_+ ch true p k) (sym (z false))))
      where
        z : ∀ β → dP β (ch α (suc p)) k ≡ 0
        z β = trans (dP-cong β _ (λ _ → 0) (λ j → ch-hi α (suc p) j h) k) (Σ-0 cs)
        same : ch false p k ≡ ch true p k
        same = cong (sel (p <ℕ suc P)) (trans (cong (λ n → e false n k) (∸-≥ P p (≡F h)))
                                         (sym (cong (λ n → e true n k) (∸-≥ P p (≡F h)))))

    a-disj : ∀ p j → T (p <ℕ P) → ch true p j * ch false p j ≡ 0
    a-disj p j q =
      trans (cong₂ _*_ (lo true) (lo false))
            (part-glob-disj (dP true (e true r) j) (dP false (e true r) j)
                            (dP true (e false r) j) (dP false (e false r) j) (equiv r j))
      where
        r = P ∸ suc p
        lo : ∀ γ → ch γ p j ≡ e γ (suc r) j
        lo γ = trans (ch-lo γ p j (<-step p P q)) (cong (λ n → e γ n j) (∸-suc P p q))

    a-unit : ∀ α → Σl cs (ch α 0) ≡ 1
    a-unit α = trans (Σ-cong cs (λ j → ch-lo α 0 j tt)) (==ℕ-sound _ _ (uns α i))

    atomCD : CellData i
    atomCD = record { ch = ch ; conc = a-conc ; top = a-top ; above = a-above
                    ; glob = a-glob ; disj = a-disj ; unit = a-unit }
