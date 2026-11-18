------------------------------------------------------------------------
-- Atom generation for ν(K) (ledger A5, step N1; Steiner 2004, §5).
--
-- For a finite basis listed in an order with negative faces before and
-- positive faces after (supp ∂⁻bᵢ ⊆ [0, i), supp ∂⁺bᵢ ⊆ (i, N): the
-- strongly loop-free case, e.g. the order of `Strict.Order`), with
-- ∂∂ = 0, ∂ lowering degree, ε∂ = 0 on 1-chains and a unital basis,
-- every cell of ν(K) is a composite of atoms:
--
--   generation : ∀ x → IsCell K L x → Gen x
--
-- The proof follows Steiner's decomposition (Props. 5.1, 5.2, 5.4,
-- 5.5 and Thm 5.6), with the order replacing loop-freeness:
--
--  * (peel, Prop. 5.1 in binary form) if the rows of a cell x above s
--    split as p + q, where p and q satisfy the boundary conditions
--    above s and (∂p_{s+1})₋ is disjoint from (∂q_{s+1})₊, then
--    x = y #ₛ z with y, z cells whose rows above s are p and q.
--  * (Prop. 5.2) if the rows of x above s+1 are those of an atom ⟨a⟩
--    (or zero), then row s+1 is ⟨a⟩_{s+1} + w for a chain w ≥ 0, and
--    the rows above s are those of ⟨a⟩ + Σ_{c ∈ w} ⟨c⟩.
--  * Listing these atoms in the basis order and peeling the least one
--    gives pieces whose rows above s are those of one atom (Prop. 5.4).
--  * At s = 0 such a cell is the atom (Prop. 5.5, by unitality).
------------------------------------------------------------------------
module CaTTExp.Strict.Generation where

open import CaTTExp.Prelude
open import CaTTExp.Strict.Omega using (_≤_; z≤n; s≤s; _<_; ≤-refl; ≤-trans; ≤-suc; <→≤; <-irrefl; ≤-<-⊥)
open import CaTTExp.Strict.Tables
open import CaTTExp.Strict.Nu
open import CaTTExp.Strict.FreeADC
open import CaTTExp.Strict.Atoms
open import CaTTExp.Strict.CMonSolver
open import CaTTExp.Strict.Bag using (+-comm; +-assoc; +-zero; +-suc; +-cancelˡ; +-cancelʳ)
open import CaTTExp.Gray.Cover using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Natural numbers.

private
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  0∸ : ∀ d → 0 ∸ d ≡ 0
  0∸ zero    = refl
  0∸ (suc d) = refl

-- m ≤ n with an additive witness.
_≼_ : Nat → Nat → Set
m ≼ n = Σ Nat (λ k → m + k ≡ n)

∸0→≼ : ∀ b a → b ∸ a ≡ 0 → b ≼ a
∸0→≼ zero    a       _ = a , refl
∸0→≼ (suc b) zero    ()
∸0→≼ (suc b) (suc a) p = let (k , e) = ∸0→≼ b a p in k , cong suc e

∸-+ : ∀ b n → b ≼ n → (n ∸ b) + b ≡ n
∸-+ zero    n       _       = +-zero n
∸-+ (suc b) zero    (k , ())
∸-+ (suc b) (suc n) (k , e) = trans (+-suc (n ∸ b) b) (cong suc (∸-+ b n (k , suc-inj e)))

≤-dec : ∀ m n → (m ≤ n) ⊎ (n < m)
≤-dec zero    n       = inj₁ z≤n
≤-dec (suc m) zero    = inj₂ (s≤s z≤n)
≤-dec (suc m) (suc n) with ≤-dec m n
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

<-split : ∀ {s n} → s < n → Σ Nat (λ k → n ≡ s + suc k)
<-split {zero}  {suc n} (s≤s p) = n , refl
<-split {suc s} {suc n} (s≤s p) = let (k , e) = <-split p in k , cong suc e

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step = ≤-suc

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s p) = p

------------------------------------------------------------------------
-- Three-way comparison, as data for rewriting.

data Ord3 : Set where
  LT EQ GT : Ord3

cmp3 : Nat → Nat → Ord3
cmp3 zero    zero    = EQ
cmp3 zero    (suc _) = LT
cmp3 (suc _) zero    = GT
cmp3 (suc i) (suc s) = cmp3 i s

cmp3-lt : ∀ {i s} → i < s → cmp3 i s ≡ LT
cmp3-lt {zero}  {suc s} _       = refl
cmp3-lt {suc i} {suc s} (s≤s p) = cmp3-lt p

cmp3-eq : ∀ i → cmp3 i i ≡ EQ
cmp3-eq zero    = refl
cmp3-eq (suc i) = cmp3-eq i

cmp3-gt : ∀ {i s} → s < i → cmp3 i s ≡ GT
cmp3-gt {suc i} {zero}  _       = refl
cmp3-gt {suc i} {suc s} (s≤s p) = cmp3-gt p

sel3 : ∀ {A : Set} → Ord3 → A → A → A → A
sel3 LT a b c = a
sel3 EQ a b c = b
sel3 GT a b c = c

data View3 (i s : Nat) : Set where
  vlt : i < s → View3 i s
  veq : i ≡ s → View3 i s
  vgt : s < i → View3 i s

view3 : ∀ i s → View3 i s
view3 zero    zero    = veq refl
view3 zero    (suc s) = vlt (s≤s z≤n)
view3 (suc i) zero    = vgt (s≤s z≤n)
view3 (suc i) (suc s) with view3 i s
... | vlt p = vlt (s≤s p)
... | veq p = veq (cong suc p)
... | vgt p = vgt (s≤s p)

------------------------------------------------------------------------
-- Chains pointwise.

at0 : ∀ {m} → Vec Nat m → Nat → Nat
at0 = at 0

vext : ∀ {m} (u v : Vec Nat m) → (∀ d → at0 u d ≡ at0 v d) → u ≡ v
vext []      []      h = refl
vext (a ∷ u) (b ∷ v) h = cong₂ _∷_ (h 0) (vext u v (λ d → h (suc d)))

at-+c : ∀ {m} (u v : Vec Nat m) d → at0 (u +c v) d ≡ at0 u d + at0 v d
at-+c []      []      d       = refl
at-+c (a ∷ u) (b ∷ v) zero    = refl
at-+c (a ∷ u) (b ∷ v) (suc d) = at-+c u v d

at-∸c : ∀ {m} (u v : Vec Nat m) d → at0 (u ∸c v) d ≡ at0 u d ∸ at0 v d
at-∸c []      []      d       = refl
at-∸c (a ∷ u) (b ∷ v) zero    = refl
at-∸c (a ∷ u) (b ∷ v) (suc d) = at-∸c u v d

at-0c : ∀ {m} d → at0 (0c {m}) d ≡ 0
at-0c {zero}  d       = refl
at-0c {suc m} zero    = refl
at-0c {suc m} (suc d) = at-0c {m} d

-- Supports: Lo t u is supp u ⊆ [0, t), Hi t u is supp u ⊆ [t, ∞).
Lo Hi : ∀ {m} → Nat → Vec Nat m → Set
Lo t u = ∀ d → t ≤ d → at0 u d ≡ 0
Hi t u = ∀ d → d < t → at0 u d ≡ 0

Lo-weak : ∀ {m t} {u : Vec Nat m} → Lo t u → Lo (suc t) u
Lo-weak h d p = h d (≤-trans (≤-suc (≤-refl _)) p)

Hi-weak : ∀ {m t} {u : Vec Nat m} → Hi (suc t) u → Hi t u
Hi-weak h d p = h d (≤-suc p)

∸c-Lo : ∀ {m t} (u v : Vec Nat m) → Lo t u → Lo t (u ∸c v)
∸c-Lo u v h d p = trans (at-∸c u v d) (trans (cong (_∸ at0 v d) (h d p)) (0∸ (at0 v d)))

∸c-Hi : ∀ {m t} (u v : Vec Nat m) → Hi t u → Hi t (u ∸c v)
∸c-Hi u v h d p = trans (at-∸c u v d) (trans (cong (_∸ at0 v d) (h d p)) (0∸ (at0 v d)))

unit-Lo : ∀ {m} i → Lo (suc i) (unit {m} i)
unit-Lo {zero}  i       d       p       = refl
unit-Lo {suc m} zero    zero    ()
unit-Lo {suc m} zero    (suc d) p       = at-0c {m} d
unit-Lo {suc m} (suc i) zero    ()
unit-Lo {suc m} (suc i) (suc d) (s≤s p) = unit-Lo {m} i d p

unit-Hi : ∀ {m} i → Hi i (unit {m} i)
unit-Hi {zero}  i       d       p       = refl
unit-Hi {suc m} zero    d       ()
unit-Hi {suc m} (suc i) zero    p       = refl
unit-Hi {suc m} (suc i) (suc d) (s≤s p) = unit-Hi {m} i d p

-- Linear maps vanish where every used column vanishes.
⊙-at : ∀ {m} k (v : Vec Nat m) d → at0 v d ≡ 0 → at0 (k ⊙ v) d ≡ 0
⊙-at {m} zero    v d p = at-0c {m} d
⊙-at {m} (suc k) v d p = trans (at-+c v (k ⊙ v) d) (cong₂ _+_ p (⊙-at k v d p))

lin-supp : ∀ {M m} (c : Vec Nat m) (vs : Vec (Vec Nat M) m) d →
           (∀ i → (at0 c i ≡ 0) ⊎ (at0 (at 0c vs i) d ≡ 0)) → at0 (lin c vs) d ≡ 0
lin-supp {M} []      []       d h = at-0c {M} d
lin-supp {M} (k ∷ c) (v ∷ vs) d h =
  trans (at-+c (k ⊙ v) (lin c vs) d) (cong₂ _+_ (hd (h 0)) (lin-supp c vs d (λ i → h (suc i))))
  where
  hd : (k ≡ 0) ⊎ (at0 v d ≡ 0) → at0 (k ⊙ v) d ≡ 0
  hd (inj₁ refl) = at-0c {M} d
  hd (inj₂ p)    = ⊙-at k v d p

------------------------------------------------------------------------
-- Tables from row functions.

le-+ : ∀ m j → j ≤ m + j
le-+ zero    j = ≤-refl j
le-+ (suc m) j = ≤-suc (le-+ m j)

≤→+ : ∀ {m n} → m ≤ n → Σ Nat (λ k → n ≡ m + k)
≤→+ {n = n} z≤n = n , refl
≤→+ (s≤s p) = let (k , e) = ≤→+ p in k , cong suc e

module _ {A : Set} where
  tabG : ∀ {m} → (Nat → A) → Nat → Vec A m
  tabG {zero}  f j = []
  tabG {suc m} f j = f j ∷ tabG f (suc j)

  tabG-ext : ∀ {m} (f g : Nat → A) j → (∀ i → j ≤ i → i < m + j → f i ≡ g i) → tabG {m} f j ≡ tabG g j
  tabG-ext {zero}  f g j h = refl
  tabG-ext {suc m} f g j h =
    cong₂ _∷_ (h j (≤-refl j) (s≤s (le-+ m j)))
      (tabG-ext {m} f g (suc j) (λ i p q → h i (≤-trans (≤-suc (≤-refl j)) p) (subst (λ n → i < n) (+-suc m j) q)))

  tabG-shift : ∀ {m} (f : Nat → A) j → tabG {m} f (suc j) ≡ tabG (λ i → f (suc i)) j
  tabG-shift {zero}  f j = refl
  tabG-shift {suc m} f j = cong (f (suc j) ∷_) (tabG-shift {m} f (suc j))

  tab-at : ∀ {m} (d : A) (x : Vec A m) → x ≡ tabG (at d x) 0
  tab-at d []      = refl
  tab-at d (e ∷ r) = cong (e ∷_) (trans (tab-at d r) (sym (tabG-shift (at d (e ∷ r)) 0)))

------------------------------------------------------------------------
-- Hypotheses on the basis.

dP dM : ∀ {N} → Basis N → Vec Nat N → Vec Nat N
dP B c = lin c (Basis.bplus B)
dM B c = lin c (Basis.bminus B)

record Hyp {N : Nat} (B : Basis N) : Set where
  field
    -- ∂∂ = 0 on chains.
    dd     : ∀ c → dP B (dP B c) +c dM B (dM B c) ≡ dP B (dM B c) +c dM B (dP B c)
    -- ∂ lowers degree by one.
    deg-dp : ∀ j c → prj (suc j) (Basis.gdeg B) c ≡ c → prj j (Basis.gdeg B) (dP B c) ≡ dP B c
    deg-dm : ∀ j c → prj (suc j) (Basis.gdeg B) c ≡ c → prj j (Basis.gdeg B) (dM B c) ≡ dM B c
    -- The basis order: negative faces before, positive faces after.
    ordm   : ∀ i d → i ≤ d → at0 (at 0c (Basis.bminus B) i) d ≡ 0
    ordp   : ∀ i d → d ≤ i → at0 (at 0c (Basis.bplus B) i) d ≡ 0
    -- ε∂ = 0 on 1-chains.
    aug1   : ∀ c → prj 1 (Basis.gdeg B) c ≡ c → augm (Basis.gdeg B) (dP B c) ≡ augm (Basis.gdeg B) (dM B c)
    -- Unital basis (Steiner Def. 3.4).
    unital : ∀ i → Atom.Cells.Deg.Unital B dd deg-dp deg-dm i

module Gen {N : Nat} (B : Basis N) (H : Hyp B) (L : Nat) where
  open Basis B
  open Hyp H
  open Atom B
  open Cells dd
  open Deg deg-dp deg-dm

  private
    𝕄 = chainMon N
    dp dm : Vec Nat N → Vec Nat N
    dp = dP B
    dm = dM B

  open Solver 𝕄

  Row : Set
  Row = Vec Nat N × Vec Nat N

  RF : Set
  RF = Nat → Row

  0R : Row
  0R = 0c , 0c

  _+R_ : Row → Row → Row
  _+R_ = _+P_ 𝕄

  InD : Nat → Vec Nat N → Set
  InD j u = prj j gdeg u ≡ u

  ----------------------------------------------------------------------
  -- Supports of boundaries and atoms.

  dm-Lo : ∀ t c → Lo (suc t) c → Lo t (dm c)
  dm-Lo t c h d td = lin-supp c bminus d f
    where
    f : ∀ i → (at0 c i ≡ 0) ⊎ (at0 (at 0c bminus i) d ≡ 0)
    f i with ≤-dec (suc t) i
    ... | inj₁ p       = inj₁ (h i p)
    ... | inj₂ (s≤s q) = inj₂ (ordm i d (≤-trans q td))

  dp-Hi : ∀ t c → Hi t c → Hi (suc t) (dp c)
  dp-Hi t c h d (s≤s dt) = lin-supp c bplus d f
    where
    f : ∀ i → (at0 c i ≡ 0) ⊎ (at0 (at 0c bplus i) d ≡ 0)
    f i with ≤-dec t i
    ... | inj₁ p = inj₂ (ordp i d (≤-trans dt p))
    ... | inj₂ q = inj₁ (h i q)

  entK-Lo  : ∀ i k → Lo (suc i) (fst (entK i k))
  entK-Lo1 : ∀ i k → Lo i (fst (entK i (suc k)))
  entK-Lo i zero    = unit-Lo {N} i
  entK-Lo i (suc k) = Lo-weak {N} {i} {fst (entK i (suc k))} (entK-Lo1 i k)
  entK-Lo1 i k = ∸c-Lo {N} {i} (dm (fst (entK i k))) (dp (fst (entK i k))) (dm-Lo i (fst (entK i k)) (entK-Lo i k))

  entK-Hi  : ∀ i k → Hi i (snd (entK i k))
  entK-Hi1 : ∀ i k → Hi (suc i) (snd (entK i (suc k)))
  entK-Hi i zero    = unit-Hi {N} i
  entK-Hi i (suc k) = Hi-weak {N} {i} {snd (entK i (suc k))} (entK-Hi1 i k)
  entK-Hi1 i k = ∸c-Hi {N} {suc i} (dp (snd (entK i k))) (dm (snd (entK i k))) (dp-Hi i (snd (entK i k)) (entK-Hi i k))

  -- Below the top, ⟨a⟩⁻ lies before a and ⟨a⟩⁺ after a.
  ent-sides : ∀ a s → s < deg a → Lo a (fst (ent a s)) × Hi (suc a) (snd (ent a s))
  ent-sides a s p with <-split p
  ... | k , e rewrite ent-in a s (suc k) e = entK-Lo1 a k , entK-Hi1 a k

  disj-LH : ∀ a (u v : Vec Nat N) → Lo a u → Hi (suc a) v → ∀ d → (at0 u d ≡ 0) ⊎ (at0 v d ≡ 0)
  disj-LH a u v hu hv d with ≤-dec a d
  ... | inj₁ p = inj₁ (hu d p)
  ... | inj₂ q = inj₂ (hv d (≤-suc q))

  ----------------------------------------------------------------------
  -- Row functions satisfying the cell conditions above s.

  record Good (s : Nat) (p : RF) : Set where
    field
      g-deg⁻ : InD (suc s) (fst (p (suc s)))
      g-deg⁺ : InD (suc s) (snd (p (suc s)))
      g-inv  : Inv (p (suc s))
      g-ent  : ∀ j → suc s ≤ j → j < L → Ent K L (suc j) (p j) (p (suc j))
      g-last : fst (p L) ≡ snd (p L)
  open Good

  Ent-0 : ∀ j (r : Row) → fst r ≡ snd r → Ent K L j r 0R
  Ent-0 j r e = prj-0 j gdeg , prj-0 j gdeg , B0 , B0
    where
    B0 : dp 0c +c fst r ≡ dm 0c +c snd r
    B0 = trans (Bd0 (fst r)) (cong (dm 0c +c_) e)

  Good-ent : ∀ a s → s < deg a → deg a ≤ L → Good s (ent a)
  Good-ent a s p q with <-split p | ≤→+ q
  ... | k , e | k′ , e′ = record
    { g-deg⁻ = fst dg ; g-deg⁺ = snd dg ; g-inv = inv
    ; g-ent  = λ j _ _ → ent-ok a j
    ; g-last = ent-last L a k′ e′ }
    where
    e1 : deg a ≡ suc s + k
    e1 = trans e (+-suc s k)
    dg : InD (suc s) (fst (ent a (suc s))) × InD (suc s) (snd (ent a (suc s)))
    dg rewrite ent-in a (suc s) k e1 = deg-entK a k (suc s) (trans e1 (+-comm (suc s) k))
    inv : Inv (ent a (suc s))
    inv rewrite ent-in a (suc s) k e1 = Inv-entK a k

  -- The chain w as a row in degree s + 1.
  W : Nat → Vec Nat N → RF
  W s w j = sel3 (cmp3 j (suc s)) 0R (w , w) 0R

  W-diag : ∀ s w j → fst (W s w j) ≡ snd (W s w j)
  W-diag s w j with cmp3 j (suc s)
  ... | LT = refl
  ... | EQ = refl
  ... | GT = refl

  W-top : ∀ s w → W s w (suc s) ≡ (w , w)
  W-top s w rewrite cmp3-eq s = refl

  W-above : ∀ s w j → suc s < j → W s w j ≡ 0R
  W-above s w j p rewrite cmp3-gt p = refl

  Good-W : ∀ s w → InD (suc s) w → Good s (W s w)
  Good-W s w dw = record
    { g-deg⁻ = subst (λ r → InD (suc s) (fst r)) (sym (W-top s w)) dw
    ; g-deg⁺ = subst (λ r → InD (suc s) (snd r)) (sym (W-top s w)) dw
    ; g-inv  = subst Inv (sym (W-top s w)) refl
    ; g-ent  = λ j p _ → subst (Ent K L (suc j) (W s w j)) (sym (W-above s w (suc j) (s≤s p)))
                           (Ent-0 (suc j) (W s w j) (W-diag s w j))
    ; g-last = W-diag s w L }

  Inv-add : ∀ (r r′ : Row) → Inv r → Inv r′ → Inv (r +R r′)
  Inv-add (a , b) (c , d) h h′ =
    trans (cong₂ _+c_ (lin-+ a c bplus) (lin-+ b d bminus))
    (trans (solve ((` 0 ⊞ ` 1) ⊞ (` 2 ⊞ ` 3)) ((` 0 ⊞ ` 2) ⊞ (` 1 ⊞ ` 3)) ρ tt)
    (trans (cong₂ _+c_ h h′)
    (trans (solve ((` 4 ⊞ ` 5) ⊞ (` 6 ⊞ ` 7)) ((` 4 ⊞ ` 6) ⊞ (` 5 ⊞ ` 7)) ρ tt)
           (sym (cong₂ _+c_ (lin-+ b d bplus) (lin-+ a c bminus))))))
    where
    ρ = lk (dp a ∷ dp c ∷ dm b ∷ dm d ∷ dp b ∷ dm a ∷ dp d ∷ dm c ∷ [])

  InD-add : ∀ j u v → InD j u → InD j v → InD j (u +c v)
  InD-add j u v hu hv = trans (prj-+ j gdeg u v) (cong₂ _+c_ hu hv)

  Ent-add : ∀ j (r r′ e e′ : Row) → Ent K L j r e → Ent K L j r′ e′ → Ent K L j (r +R r′) (e +R e′)
  Ent-add j r r′ e e′ (d1 , d2 , b1 , b2) (d1′ , d2′ , b1′ , b2′) =
    InD-add j _ _ d1 d1′ , InD-add j _ _ d2 d2′ ,
    Bd-add K L r r′ (fst e) (fst e′) b1 b1′ , Bd-add K L r r′ (snd e) (snd e′) b2 b2′

  Good-add : ∀ s p q → Good s p → Good s q → Good s (λ j → p j +R q j)
  Good-add s p q gp gq = record
    { g-deg⁻ = InD-add (suc s) _ _ (g-deg⁻ gp) (g-deg⁻ gq)
    ; g-deg⁺ = InD-add (suc s) _ _ (g-deg⁺ gp) (g-deg⁺ gq)
    ; g-inv  = Inv-add (p (suc s)) (q (suc s)) (g-inv gp) (g-inv gq)
    ; g-ent  = λ j a b → Ent-add (suc j) (p j) (q j) (p (suc j)) (q (suc j)) (g-ent gp j a b) (g-ent gq j a b)
    ; g-last = cong₂ _+c_ (g-last gp) (g-last gq) }

  ----------------------------------------------------------------------
  -- Cells as row functions.

  CellF : RF → Set
  CellF f = Ent0 K L (f 0) × (∀ j → j < L → Ent K L (suc j) (f j) (f (suc j))) × (fst (f L) ≡ snd (f L))

  Tb : Set
  Tb = Tab 𝕄 (suc L)

  private
    Cnd-tabB : ∀ {m} (f : RF) j → (∀ i → j ≤ i → i < m + j → Ent K L (suc i) (f i) (f (suc i))) →
               Cnd K L (suc j) (f j) (tabG {m = m} f (suc j))
    Cnd-tabB {zero}  f j h = tt
    Cnd-tabB {suc m} f j h =
      h j (≤-refl j) (s≤s (le-+ m j)) ,
      Cnd-tabB {m} f (suc j) (λ i p q → h i (≤-trans (≤-suc (≤-refl j)) p) (subst (λ n → i < n) (+-suc m j) q))

    Last-tabG : ∀ m (f : RF) j → fst (f (m + j)) ≡ snd (f (m + j)) → Last K L (tabG {m = suc m} f j)
    Last-tabG zero    f j p = p
    Last-tabG (suc m) f j p = Last-tabG m f (suc j) (subst (λ q → fst (f q) ≡ snd (f q)) (sym (+-suc m j)) p)

    Cnd-at : ∀ {m} j (p : Row) (r : Vec Row m) → Cnd K L (suc j) p r →
             ∀ k → k < m → Ent K L (suc (k + j)) (at 0R (p ∷ r) k) (at 0R r k)
    Cnd-at j p (e ∷ r) (h , c) zero    _       = h
    Cnd-at j p (e ∷ r) (h , c) (suc k) (s≤s q) =
      subst (λ n → Ent K L (suc n) (at 0R (e ∷ r) k) (at 0R r k)) (+-suc k j) (Cnd-at (suc j) e r c k q)

    Last-at : ∀ {m} (x : Vec Row (suc m)) → Last K L x → fst (at 0R x m) ≡ snd (at 0R x m)
    Last-at {zero}  (e ∷ [])      l = l
    Last-at {suc m} (e ∷ (e′ ∷ r)) l = Last-at {m} (e′ ∷ r) l

  CellF→IsCell : ∀ f → CellF f → IsCell K L (tabG f 0)
  CellF→IsCell f (e0 , ents , last) =
    e0 ,
    Cnd-tabB {L} f 0 (λ i _ q → ents i (subst (λ n → i < n) (+-zero L) q)) ,
    Last-tabG L f 0 (subst (λ n → fst (f n) ≡ snd (f n)) (sym (+-zero L)) last)

  IsCell→CellF : ∀ (x : Tb) → IsCell K L x → CellF (at 0R x)
  IsCell→CellF (e ∷ r) (e0 , c , l) =
    e0 ,
    (λ j q → subst (λ n → Ent K L (suc n) (at 0R (e ∷ r) j) (at 0R r j)) (+-zero j) (Cnd-at 0 e r c j q)) ,
    Last-at (e ∷ r) l

  atomT≡ : ∀ {m} (f : RF) j → tabF {m} f j ≡ tabG f j
  atomT≡ {zero}  f j = refl
  atomT≡ {suc m} f j = cong (f j ∷_) (atomT≡ {m} f (suc j))

  ----------------------------------------------------------------------
  -- Boundaries and composites of tables, row by row.

  compF : Nat → RF → RF → RF
  compF s f g i = sel3 (cmp3 i s) (f i) (fst (f i) , snd (g i)) (f i +R g i)

  srcF tgtF : Nat → RF → RF
  srcF s f i = sel3 (cmp3 i s) (f i) (fst (f i) , fst (f i)) 0R
  tgtF s f i = sel3 (cmp3 i s) (f i) (snd (f i) , snd (f i)) 0R

  tabE : ∀ {m} (f g : RF) j → (∀ i → j ≤ i → f i ≡ g i) → tabG {m = m} f j ≡ tabG g j
  tabE f g j h = tabG-ext f g j (λ i p _ → h i p)

  private
    add-tab : ∀ {m} (f g : RF) j → add 𝕄 (tabG {m = m} f j) (tabG g j) ≡ tabG (λ i → f i +R g i) j
    add-tab {zero}  f g j = refl
    add-tab {suc m} f g j = cong ((f j +R g j) ∷_) (add-tab {m} f g (suc j))

    zeros-tab : ∀ {m} j → zeros 𝕄 {m} ≡ tabG {m = m} (λ _ → 0R) j
    zeros-tab {zero}  j = refl
    zeros-tab {suc m} j = cong (0R ∷_) (zeros-tab {m} (suc j))

    lt-suc : ∀ j n → j < suc (n + j)
    lt-suc j n = s≤s (le-+ n j)

  comp-tab : ∀ {m} n j (f g : RF) → compT 𝕄 n (tabG {m = m} f j) (tabG g j) ≡ tabG (compF (n + j) f g) j
  comp-tab {zero}  n       j f g = refl
  comp-tab {suc m} zero    j f g =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (fst (f j) , snd (g j)) (f j +R g j)) (sym (cmp3-eq j)))
      (trans (add-tab {m} f g (suc j))
        (tabE (λ i → f i +R g i) (compF j f g) (suc j)
          (λ i p → cong (λ o → sel3 o (f i) (fst (f i) , snd (g i)) (f i +R g i)) (sym (cmp3-gt p)))))
  comp-tab {suc m} (suc n) j f g =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (fst (f j) , snd (g j)) (f j +R g j)) (sym (cmp3-lt (lt-suc j n))))
      (trans (comp-tab {m} n (suc j) f g) (cong (λ k → tabG (compF k f g) (suc j)) (+-suc n j)))

  src-tab : ∀ {m} n j (f : RF) → srcT 𝕄 n (tabG {m = m} f j) ≡ tabG (srcF (n + j) f) j
  src-tab {zero}  n       j f = refl
  src-tab {suc m} zero    j f =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (fst (f j) , fst (f j)) 0R) (sym (cmp3-eq j)))
      (trans (zeros-tab {m} (suc j))
        (tabE (λ _ → 0R) (srcF j f) (suc j)
          (λ i p → cong (λ o → sel3 o (f i) (fst (f i) , fst (f i)) 0R) (sym (cmp3-gt p)))))
  src-tab {suc m} (suc n) j f =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (fst (f j) , fst (f j)) 0R) (sym (cmp3-lt (lt-suc j n))))
      (trans (src-tab {m} n (suc j) f) (cong (λ k → tabG (srcF k f) (suc j)) (+-suc n j)))

  tgt-tab : ∀ {m} n j (f : RF) → tgtT 𝕄 n (tabG {m = m} f j) ≡ tabG (tgtF (n + j) f) j
  tgt-tab {zero}  n       j f = refl
  tgt-tab {suc m} zero    j f =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (snd (f j) , snd (f j)) 0R) (sym (cmp3-eq j)))
      (trans (zeros-tab {m} (suc j))
        (tabE (λ _ → 0R) (tgtF j f) (suc j)
          (λ i p → cong (λ o → sel3 o (f i) (snd (f i) , snd (f i)) 0R) (sym (cmp3-gt p)))))
  tgt-tab {suc m} (suc n) j f =
    cong₂ _∷_ (cong (λ o → sel3 o (f j) (snd (f j) , snd (f j)) 0R) (sym (cmp3-lt (lt-suc j n))))
      (trans (tgt-tab {m} n (suc j) f) (cong (λ k → tabG (tgtF k f) (suc j)) (+-suc n j)))

  ----------------------------------------------------------------------
  -- Peeling (Steiner Prop. 5.1, binary form).

  Disj : Nat → RF → RF → Set
  Disj s p q = ∀ d → (at0 (dm (fst (p (suc s))) ∸c dp (fst (p (suc s)))) d ≡ 0)
                   ⊎ (at0 (dp (snd (q (suc s))) ∸c dm (snd (q (suc s)))) d ≡ 0)

  record Split (s : Nat) (f p q : RF) : Set where
    field
      y z   : RF
      cy    : CellF y
      cz    : CellF z
      yp    : ∀ j → s < j → y j ≡ p j
      zq    : ∀ j → s < j → z j ≡ q j
      match : tgtT 𝕄 s (tabG {m = suc L} y 0) ≡ srcT 𝕄 s (tabG z 0)
      comp  : compT 𝕄 s (tabG {m = suc L} y 0) (tabG z 0) ≡ tabG f 0

  natMon : CMon
  natMon = record { M = Nat ; ε = 0 ; _⊕_ = _+_ ; ⊕-id = λ _ → refl ; ⊕-comm = +-comm ; ⊕-assoc = +-assoc }

  open Solver natMon using () renaming
    (`_ to #_; _⊞_ to _⊕ₑ_; ∅ to ∅ₙ; solve to solveₙ; by-lin to by-linₙ; lk to lkₙ; _∷ʰ_ to _∷ₙ_; []ʰ to []ₙ)

  augm-+ : ∀ {m} (gs u v : Vec Nat m) → augm gs (u +c v) ≡ augm gs u + augm gs v
  augm-+ []       []      []      = refl
  augm-+ (g ∷ gs) (a ∷ u) (b ∷ v) with g ==ℕ 0
  ... | true  = trans (cong ((a + b) +_) (augm-+ gs u v))
                  (solveₙ ((# 0 ⊕ₑ # 1) ⊕ₑ (# 2 ⊕ₑ # 3)) ((# 0 ⊕ₑ # 2) ⊕ₑ (# 1 ⊕ₑ # 3))
                          (lkₙ (a ∷ b ∷ augm gs u ∷ augm gs v ∷ [])) tt)
  ... | false = augm-+ gs u v

  private
    exp2 : ∀ (u v : Vec Nat N) d → at0 (u +c v) d ≡ at0 u d + at0 v d
    exp2 = at-+c
    exp3 : ∀ (u v w : Vec Nat N) d → at0 ((u +c v) +c w) d ≡ (at0 u d + at0 v d) + at0 w d
    exp3 u v w d = trans (at-+c (u +c v) w d) (cong (_+ at0 w d) (at-+c u v d))
    pt : ∀ {u v : Vec Nat N} d → u ≡ v → at0 u d ≡ at0 v d
    pt d e = cong (λ w → at0 w d) e
    nat-cancel : ∀ a b c → a + c ≡ b + c → a ≡ b
    nat-cancel a b c = +-cancelʳ c a b

  module Peel (s : Nat) (sL : s < L) (f p q : RF) (cf : CellF f) (gp : Good s p) (gq : Good s q)
              (split : ∀ j → s < j → j ≤ L → f j ≡ p j +R q j) (dj : Disj s p q) where

    X⁻ X⁺ P⁻ P⁺ Q⁻ Q⁺ : Vec Nat N
    X⁻ = fst (f s)
    X⁺ = snd (f s)
    P⁻ = fst (p (suc s))
    P⁺ = snd (p (suc s))
    Q⁻ = fst (q (suc s))
    Q⁺ = snd (q (suc s))

    -- The middle row: X⁻ + ∂P⁻.
    m : Vec Nat N
    m = (X⁻ +c dp P⁻) ∸c dm P⁻

    row-deg : ∀ j → j ≤ L → InD j (fst (f j)) × InD j (snd (f j))
    row-deg zero    _ = fst (fst cf) , fst (snd (fst cf))
    row-deg (suc j) q′ = let (a , b , _ , _) = fst (snd cf) j q′ in a , b

    F1 : (dp P⁻ +c dp Q⁻) +c X⁻ ≡ (dm P⁻ +c dm Q⁻) +c X⁺
    F1 = trans (cong (_+c X⁻) (sym (lin-+ P⁻ Q⁻ bplus)))
           (trans (subst (λ r → dp (fst r) +c X⁻ ≡ dm (fst r) +c X⁺) (split (suc s) (≤-refl (suc s)) sL)
                         (fst (snd (snd (fst (snd cf) s sL)))))
                  (cong (_+c X⁺) (lin-+ P⁻ Q⁻ bminus)))

    le : ∀ d → at0 (dm P⁻) d ≼ at0 (X⁻ +c dp P⁻) d
    le d with dj d
    ... | inj₁ e =
      let (k , ek) = ∸0→≼ (at0 (dm P⁻) d) (at0 (dp P⁻) d) (trans (sym (at-∸c (dm P⁻) (dp P⁻) d)) e)
      in k + at0 X⁻ d ,
         trans (sym (+-assoc (at0 (dm P⁻) d) k (at0 X⁻ d)))
           (trans (cong (_+ at0 X⁻ d) ek) (trans (+-comm (at0 (dp P⁻) d) (at0 X⁻ d)) (sym (at-+c X⁻ (dp P⁻) d))))
    ... | inj₂ e =
      let (t , et) = ∸0→≼ (at0 (dp Q⁺) d) (at0 (dm Q⁺) d) (trans (sym (at-∸c (dp Q⁺) (dm Q⁺) d)) e)
          a = at0 (dp P⁻) d ; b = at0 (dm P⁻) d ; x = at0 X⁻ d ; y = at0 X⁺ d
          qp = at0 (dp Q⁻) d ; qm = at0 (dm Q⁻) d ; qp′ = at0 (dp Q⁺) d
          h2 : (a + qp) + x ≡ (b + qm) + y
          h2 = trans (sym (exp3 (dp P⁻) (dp Q⁻) X⁻ d)) (trans (pt d F1) (exp3 (dm P⁻) (dm Q⁻) X⁺ d))
          h1 : qp + (qp′ + t) ≡ qp′ + qm
          h1 = trans (cong (qp +_) et) (trans (sym (exp2 (dp Q⁻) (dm Q⁺) d)) (trans (pt d (g-inv gq)) (exp2 (dp Q⁺) (dm Q⁻) d)))
      in t + y ,
         trans (by-linₙ nat-cancel (sym h2 ∷ₙ h1 ∷ₙ []ₙ) (b + (t + y)) (x + a)
                  (solveₙ ((# 0 ⊕ₑ (# 7 ⊕ₑ # 3)) ⊕ₑ (((# 1 ⊕ₑ # 4) ⊕ₑ # 2) ⊕ₑ ((# 6 ⊕ₑ # 5) ⊕ₑ ∅ₙ)))
                          ((# 2 ⊕ₑ # 1) ⊕ₑ (((# 0 ⊕ₑ # 5) ⊕ₑ # 3) ⊕ₑ ((# 4 ⊕ₑ (# 6 ⊕ₑ # 7)) ⊕ₑ ∅ₙ)))
                          (lkₙ (b ∷ a ∷ x ∷ y ∷ qp ∷ qm ∷ qp′ ∷ t ∷ [])) tt))
               (sym (at-+c X⁻ (dp P⁻) d))

    -- Bd (X⁻, m) P⁻.
    M1 : dp P⁻ +c X⁻ ≡ dm P⁻ +c m
    M1 = vext _ _ λ d →
      trans (at-+c (dp P⁻) X⁻ d)
      (trans (trans (+-comm (at0 (dp P⁻) d) (at0 X⁻ d)) (sym (at-+c X⁻ (dp P⁻) d)))
      (trans (sym (∸-+ (at0 (dm P⁻) d) (at0 (X⁻ +c dp P⁻) d) (le d)))
      (trans (+-comm _ (at0 (dm P⁻) d))
      (sym (trans (at-+c (dm P⁻) m d) (cong (at0 (dm P⁻) d +_) (at-∸c (X⁻ +c dp P⁻) (dm P⁻) d)))))))

    M2 : dp P⁺ +c X⁻ ≡ dm P⁺ +c m
    M2 = by-lin +c-cancel (M1 ∷ʰ sym (g-inv gp) ∷ʰ []ʰ) _ _
           (solve ((` 0 ⊞ ` 1) ⊞ ((` 2 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 5) ⊞ ∅)))
                  ((` 5 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 1) ⊞ ((` 0 ⊞ ` 2) ⊞ ∅)))
                  (lk (dp P⁺ ∷ X⁻ ∷ dm P⁻ ∷ m ∷ dp P⁻ ∷ dm P⁺ ∷ [])) tt)

    M3 : dp Q⁻ +c m ≡ dm Q⁻ +c X⁺
    M3 = by-lin +c-cancel (F1 ∷ʰ sym M1 ∷ʰ []ʰ) _ _
           (solve ((` 0 ⊞ ` 1) ⊞ (((` 2 ⊞ ` 3) ⊞ ` 4) ⊞ ((` 5 ⊞ ` 6) ⊞ ∅)))
                  ((` 3 ⊞ ` 4) ⊞ (((` 5 ⊞ ` 0) ⊞ ` 6) ⊞ ((` 2 ⊞ ` 1) ⊞ ∅)))
                  (lk (dp Q⁻ ∷ m ∷ dm P⁻ ∷ dm Q⁻ ∷ X⁺ ∷ dp P⁻ ∷ X⁻ ∷ [])) tt)

    M4 : dp Q⁺ +c m ≡ dm Q⁺ +c X⁺
    M4 = by-lin +c-cancel (M3 ∷ʰ sym (g-inv gq) ∷ʰ []ʰ) _ _
           (solve ((` 0 ⊞ ` 1) ⊞ ((` 2 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 5) ⊞ ∅)))
                  ((` 5 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 1) ⊞ ((` 0 ⊞ ` 2) ⊞ ∅)))
                  (lk (dp Q⁺ ∷ m ∷ dm Q⁻ ∷ X⁺ ∷ dp Q⁻ ∷ dm Q⁺ ∷ [])) tt)

    -- The boundary of m is that of X⁻ (∂∂ = 0).
    M5 : ∀ u v → dp X⁻ +c u ≡ dm X⁻ +c v → dp m +c u ≡ dm m +c v
    M5 u v E3 = by-lin +c-cancel (sym E1 ∷ʰ E2 ∷ʰ E3 ∷ʰ dd P⁻ ∷ʰ []ʰ) _ _
      (solve ((` 0 ⊞ ` 1) ⊞ ((` 2 ⊞ ` 3) ⊞ ((` 4 ⊞ ` 5) ⊞ ((` 6 ⊞ ` 7) ⊞ ((` 8 ⊞ ` 9) ⊞ ∅)))))
             ((` 5 ⊞ ` 7) ⊞ ((` 8 ⊞ ` 0) ⊞ ((` 9 ⊞ ` 6) ⊞ ((` 3 ⊞ ` 1) ⊞ ((` 2 ⊞ ` 4) ⊞ ∅)))))
             (lk (dp m ∷ u ∷ dp (dp P⁻) ∷ dp X⁻ ∷ dm (dm P⁻) ∷ dm m ∷ dm X⁻ ∷ v ∷ dp (dm P⁻) ∷ dm (dp P⁻) ∷ [])) tt)
      where
      E1 : dp (dp P⁻) +c dp X⁻ ≡ dp (dm P⁻) +c dp m
      E1 = trans (sym (lin-+ (dp P⁻) X⁻ bplus)) (trans (cong dp M1) (lin-+ (dm P⁻) m bplus))
      E2 : dm (dp P⁻) +c dm X⁻ ≡ dm (dm P⁻) +c dm m
      E2 = trans (sym (lin-+ (dp P⁻) X⁻ bminus)) (trans (cong dm M1) (lin-+ (dm P⁻) m bminus))

    m-deg : InD s m
    m-deg = ∸c-deg s gdeg (X⁻ +c dp P⁻) (dm P⁻)
              (InD-add s X⁻ (dp P⁻) (fst (row-deg s (<→≤ sL))) (deg-dp s P⁻ (g-deg⁻ gp)))

    m-aug : s ≡ 0 → augm gdeg m ≡ 1
    m-aug refl = trans (nat-cancel (augm gdeg m) (augm gdeg X⁻) (augm gdeg (dm P⁻))
                         (trans (+-comm (augm gdeg m) (augm gdeg (dm P⁻))) (trans (sym (augm-+ gdeg (dm P⁻) m))
                           (trans (cong (augm gdeg) (sym M1))
                             (trans (augm-+ gdeg (dp P⁻) X⁻)
                               (trans (cong (_+ augm gdeg X⁻) (aug1 P⁻ (g-deg⁻ gp))) (+-comm (augm gdeg (dm P⁻)) (augm gdeg X⁻))))))))
                       (fst (snd (snd (fst cf))))

    y z : RF
    y i = sel3 (cmp3 i s) (f i) (X⁻ , m) (p i)
    z i = sel3 (cmp3 i s) (f i) (m , X⁺) (q i)

    y-lt : ∀ i → i < s → y i ≡ f i
    y-lt i h rewrite cmp3-lt h = refl
    y-eq : y s ≡ (X⁻ , m)
    y-eq rewrite cmp3-eq s = refl
    y-gt : ∀ i → s < i → y i ≡ p i
    y-gt i h rewrite cmp3-gt h = refl
    z-lt : ∀ i → i < s → z i ≡ f i
    z-lt i h rewrite cmp3-lt h = refl
    z-eq : z s ≡ (m , X⁺)
    z-eq rewrite cmp3-eq s = refl
    z-gt : ∀ i → s < i → z i ≡ q i
    z-gt i h rewrite cmp3-gt h = refl

    private
      Ent-tr : ∀ j {r r′ e e′} → r ≡ r′ → e ≡ e′ → Ent K L j r e → Ent K L j r′ e′
      Ent-tr j refl refl h = h

      lt-of-eq : ∀ j → suc j ≡ s → j < s
      lt-of-eq j e = subst (λ k → suc j ≤ k) e (≤-refl (suc j))

      -- The row below s, for s = suc j.
      below : ∀ j → j < L → suc j ≡ s →
              InD (suc j) X⁻ × InD (suc j) X⁺ × InD (suc j) m ×
              (dp X⁻ +c fst (f j) ≡ dm X⁻ +c snd (f j)) × (dp X⁺ +c fst (f j) ≡ dm X⁺ +c snd (f j))
      below j jL e =
        let (d1 , d2 , b1 , b2) = subst (λ k → Ent K L (suc j) (f j) (f k)) e (fst (snd cf) j jL)
        in d1 , d2 , subst (λ k → InD k m) (sym e) m-deg , b1 , b2

    ent-y : ∀ j → j < L → Ent K L (suc j) (y j) (y (suc j))
    ent-y j jL with view3 j s
    ... | vgt h = Ent-tr (suc j) (sym (y-gt j h)) (sym (y-gt (suc j) (≤-suc h))) (g-ent gp j h jL)
    ... | veq e = subst (λ k → Ent K L (suc k) (y k) (y (suc k))) (sym e)
                    (Ent-tr (suc s) (sym y-eq) (sym (y-gt (suc s) (≤-refl _))) (g-deg⁻ gp , g-deg⁺ gp , M1 , M2))
    ... | vlt h with view3 (suc j) s
    ...   | vlt h′ = Ent-tr (suc j) (sym (y-lt j h)) (sym (y-lt (suc j) h′)) (fst (snd cf) j jL)
    ...   | vgt h′ = ⊥-elim (≤-<-⊥ h h′)
    ...   | veq e  =
      let (d1 , d2 , dm′ , b1 , b2) = below j jL e
      in Ent-tr (suc j) (sym (y-lt j h)) (sym (trans (cong y e) y-eq)) (d1 , dm′ , b1 , M5 _ _ b1)

    ent-z : ∀ j → j < L → Ent K L (suc j) (z j) (z (suc j))
    ent-z j jL with view3 j s
    ... | vgt h = Ent-tr (suc j) (sym (z-gt j h)) (sym (z-gt (suc j) (≤-suc h))) (g-ent gq j h jL)
    ... | veq e = subst (λ k → Ent K L (suc k) (z k) (z (suc k))) (sym e)
                    (Ent-tr (suc s) (sym z-eq) (sym (z-gt (suc s) (≤-refl _))) (g-deg⁻ gq , g-deg⁺ gq , M3 , M4))
    ... | vlt h with view3 (suc j) s
    ...   | vlt h′ = Ent-tr (suc j) (sym (z-lt j h)) (sym (z-lt (suc j) h′)) (fst (snd cf) j jL)
    ...   | vgt h′ = ⊥-elim (≤-<-⊥ h h′)
    ...   | veq e  =
      let (d1 , d2 , dm′ , b1 , b2) = below j jL e
      in Ent-tr (suc j) (sym (z-lt j h)) (sym (trans (cong z e) z-eq)) (dm′ , d2 , M5 _ _ b1 , b2)

    ent0-y : Ent0 K L (y 0)
    ent0-y with view3 0 s
    ... | vlt h = subst (Ent0 K L) (sym (y-lt 0 h)) (fst cf)
    ... | vgt ()
    ... | veq e =
      let (dX , dX′ , aX , aX′) = subst (λ k → Ent0 K L (f k)) e (fst cf)
      in subst (Ent0 K L) (sym (trans (cong y e) y-eq)) (dX , subst (λ k → InD k m) (sym e) m-deg , aX , m-aug (sym e))

    ent0-z : Ent0 K L (z 0)
    ent0-z with view3 0 s
    ... | vlt h = subst (Ent0 K L) (sym (z-lt 0 h)) (fst cf)
    ... | vgt ()
    ... | veq e =
      let (dX , dX′ , aX , aX′) = subst (λ k → Ent0 K L (f k)) e (fst cf)
      in subst (Ent0 K L) (sym (trans (cong z e) z-eq)) (subst (λ k → InD k m) (sym e) m-deg , dX′ , m-aug (sym e) , aX′)

    cy : CellF y
    cy = ent0-y , ent-y , subst (λ r → fst r ≡ snd r) (sym (y-gt L sL)) (g-last gp)

    cz : CellF z
    cz = ent0-z , ent-z , subst (λ r → fst r ≡ snd r) (sym (z-gt L sL)) (g-last gq)

    private
      match-pt : ∀ i → tgtF s y i ≡ srcF s z i
      match-pt i with view3 i s
      ... | vlt h = trans (cong (λ o → sel3 o (y i) (snd (y i) , snd (y i)) 0R) (cmp3-lt h))
                      (trans (y-lt i h) (sym (trans (cong (λ o → sel3 o (z i) (fst (z i) , fst (z i)) 0R) (cmp3-lt h)) (z-lt i h))))
      ... | vgt h = trans (cong (λ o → sel3 o (y i) (snd (y i) , snd (y i)) 0R) (cmp3-gt h))
                      (sym (cong (λ o → sel3 o (z i) (fst (z i) , fst (z i)) 0R) (cmp3-gt h)))
      ... | veq refl =
        trans (cong (λ o → sel3 o (y s) (snd (y s) , snd (y s)) 0R) (cmp3-eq s))
          (trans (cong (λ r → (snd r , snd r)) y-eq)
            (sym (trans (cong (λ o → sel3 o (z s) (fst (z s) , fst (z s)) 0R) (cmp3-eq s))
                        (cong (λ r → (fst r , fst r)) z-eq))))

      comp-pt : ∀ i → i ≤ L → compF s y z i ≡ f i
      comp-pt i iL with view3 i s
      ... | vlt h = trans (cong (λ o → sel3 o (y i) (fst (y i) , snd (z i)) (y i +R z i)) (cmp3-lt h)) (y-lt i h)
      ... | vgt h = trans (cong (λ o → sel3 o (y i) (fst (y i) , snd (z i)) (y i +R z i)) (cmp3-gt h))
                      (trans (cong₂ _+R_ (y-gt i h) (z-gt i h)) (sym (split i h iL)))
      ... | veq refl =
        trans (cong (λ o → sel3 o (y s) (fst (y s) , snd (z s)) (y s +R z s)) (cmp3-eq s))
          (cong₂ _,_ (cong fst y-eq) (cong snd z-eq))

      s0 : s + 0 ≡ s
      s0 = +-zero s

    result : Split s f p q
    result = record
      { y = y ; z = z ; cy = cy ; cz = cz ; yp = y-gt ; zq = z-gt
      ; match = trans (tgt-tab s 0 y)
                  (trans (cong (λ k → tabG (tgtF k y) 0) s0)
                  (trans (tabE (tgtF s y) (srcF s z) 0 (λ i _ → match-pt i))
                  (trans (cong (λ k → tabG (srcF k z) 0) (sym s0)) (sym (src-tab s 0 z)))))
      ; comp  = trans (comp-tab s 0 y z)
                  (trans (cong (λ k → tabG (compF k y z) 0) s0)
                  (tabG-ext (compF s y z) f 0
                    (λ i _ q′ → comp-pt i (subst (λ k → i ≤ k) (+-zero L) (≤-pred q′)))))
      }

  peel : ∀ s → s < L → (f p q : RF) → CellF f → Good s p → Good s q →
         (∀ j → s < j → j ≤ L → f j ≡ p j +R q j) → Disj s p q → Split s f p q
  peel s sL f p q cf gp gq sp dj = Peel.result s sL f p q cf gp gq sp dj
