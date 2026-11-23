------------------------------------------------------------------------
-- Strong Steiner bases, certified by a sound check (ledger C5d).
--
-- The transfer from 𝔖̂ to the literal 𝔖 (notes/gray-model-formal-plan.md,
-- "Relation to 𝔖") uses Steiner's theorem that ν is fully faithful on
-- strong Steiner complexes.  This module states, for a finite basis
-- `FB`, the conditions of a strong Steiner complex with that basis
-- (Steiner 2004, Def. 2.2, 3.5, 3.6; Ara–Maltsiniotis 1607.00668 §2):
--
--   * degrees:  ∂^α x has support in degree deg x − 1;
--   * basis:    ∂⁺x and ∂⁻x have disjoint supports (so ∂ = ∂⁺ − ∂⁻
--               is the positive/negative decomposition);
--   * chain:    ∂∂ = 0, written over ℕ as
--               ∂⁺∂⁺x + ∂⁻∂⁻x = ∂⁺∂⁻x + ∂⁻∂⁺x;
--   * augment.: ε∂⁺x = ε∂⁻x for x of degree 1;
--   * unital:   ε⟨x⟩⁻₀ = ε⟨x⟩⁺₀ = 1, where ⟨x⟩^α_q is ∂^α applied
--               deg x − q times to x;
--   * strongly loop-free: the relation x <₁ y (x ∈ ∂⁻y or y ∈ ∂⁺x)
--               generates a partial order.
--
-- `strongSteiner? B` checks all of these over the finite enumeration.
-- `sound` turns `T (strongSteiner? B)` into the pointwise conditions
-- and, for loop-freeness, a height function strictly increasing along
-- <₁ (`Height`), from which `acyclic`: no nonempty <₁-path returns to
-- its start.  So a named basis is certified strong Steiner by `tt`.
-- The check is sound but not proved complete: nothing here shows that
-- it returns true on every strong Steiner basis (that would need the
-- computed height `hgt` to increase along <₁ on every loop-free basis).
--
-- Checked here: globes λDⁿ for n ≤ 4 (`globes`), and a loop basis
-- (1-cells p → q and q → p) is rejected (`loop-rejected`) while
-- passing every other condition (`loop-rest`).
-- Globes of every dimension, and closure under the Gray tensor
-- (Steiner 2004; Ara–Maltsiniotis 1607.00668 App. A), are cited, not
-- proved here.
------------------------------------------------------------------------
module CaTTExp.Gray.Biclosed.Steiner.StrongSteiner where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Steiner.Arith
open import CaTTExp.Gray.Biclosed.Steiner.Sum
open import CaTTExp.Gray.Biclosed.Steiner.Codes

------------------------------------------------------------------------
-- Checks over a finite enumeration

allb : ∀ {A : Set} → List A → (A → Bool) → Bool
allb []       p = true
allb (x ∷ xs) p = p x ∧ allb xs p

private
  one≢zero : 1 ≡ 0 → ⊥
  one≢zero ()

  all-at : ∀ {A : Set} (E : Enum A) (p : A → Bool) a xs → T (allb xs p) →
           (Σl xs (δ E a) ≡ 0 → ⊥) → T (p a)
  all-at E p a []       _ nz = ⊥-elim (nz refl)
  all-at E p a (x ∷ xs) h nz = go (eqb E a x) refl
    where
      go : ∀ b → eqb E a x ≡ b → T (p a)
      go true  e with eqb-sound E {a} {x} (subst T (sym e) tt)
      ... | refl = ∧-fst h
      go false e = all-at E p a xs (∧-snd {p x} h)
                     (λ z → nz (trans (cong (λ b → (if b then 1 else 0) + Σl xs (δ E a)) e) z))

allE : ∀ {A : Set} (E : Enum A) (p : A → Bool) → T (allb (els E) p) → ∀ a → T (p a)
allE E p h a = all-at E p a (els E) h (λ z → one≢zero (trans (sym (count E a)) z))

------------------------------------------------------------------------
-- Order facts for the Boolean _<ℕ_

<-trans : ∀ a b c → T (a <ℕ b) → T (b <ℕ c) → T (a <ℕ c)
<-trans zero    (suc b) (suc c) _ _ = tt
<-trans (suc a) (suc b) (suc c) p q = <-trans a b c p q

<-irrefl : ∀ a → T (a <ℕ a) → ⊥
<-irrefl (suc a) p = <-irrefl a p

------------------------------------------------------------------------
-- The conditions

module SS (B : FB) where
  private
    E  = enumC B
    cs = els E
    d  = fbd B
    dg = fdeg B

  Chain : Set
  Chain = Cell B → Nat

  bdC : Bool → Chain → Chain
  bdC α c y = Σl cs (λ x → c x * d α x y)

  -- ⟨x⟩^α after k steps down
  down : Bool → Nat → Chain → Chain
  down α zero    c = c
  down α (suc k) c = bdC α (down α k c)

  nz : Nat → Bool
  nz n = not (n ==ℕ 0)

  degAt : Cell B → Cell B → Bool
  degAt x y = (not (nz (d true x y)) ∧ not (nz (d false x y))) ∨ (suc (dg y) ==ℕ dg x)

  disjAt : Cell B → Cell B → Bool
  disjAt x y = (d true x y * d false x y) ==ℕ 0

  chainAt : Cell B → Cell B → Bool
  chainAt x z =
    Σl cs (λ y → d true x y * d true y z + d false x y * d false y z) ==ℕ
    Σl cs (λ y → d true x y * d false y z + d false x y * d true y z)

  augAt : Cell B → Bool
  augAt x = not (dg x ==ℕ 1) ∨ (Σl cs (d true x) ==ℕ Σl cs (d false x))

  unitAt : Bool → Cell B → Bool
  unitAt α x = Σl cs (down α (dg x) (δ E x)) ==ℕ 1

  -- x <₁ y
  lt₁ : Cell B → Cell B → Bool
  lt₁ x y = nz (d false y x) ∨ nz (d true x y)

  -- longest <₁-path ending at y, after k rounds
  step : (Cell B → Nat) → Cell B → Nat
  step h y = max (h y) (maxl cs)
    where maxl : List (Cell B) → Nat
          maxl []       = 0
          maxl (x ∷ xs) = max (if lt₁ x y then suc (h x) else 0) (maxl xs)

  rounds : Nat → Cell B → Nat
  rounds zero    _ = 0
  rounds (suc k) y = step (rounds k) y

  hgt : Cell B → Nat
  hgt = rounds (len cs)
    where len : List (Cell B) → Nat
          len []       = 0
          len (_ ∷ xs) = suc (len xs)

  hgtAt : Cell B → Cell B → Bool
  hgtAt x y = not (lt₁ x y) ∨ (hgt x <ℕ hgt y)

  all2 : (Cell B → Cell B → Bool) → Bool
  all2 p = allb cs (λ x → allb cs (p x))

  strongSteiner? : Bool
  strongSteiner? =
    all2 degAt ∧ all2 disjAt ∧ all2 chainAt ∧ allb cs augAt ∧
    allb cs (unitAt true) ∧ allb cs (unitAt false) ∧ all2 hgtAt

  ----------------------------------------------------------------------
  -- Loop-freeness from a height

  record Height : Set where
    field
      h  : Cell B → Nat
      up : ∀ x y → T (lt₁ x y) → T (h x <ℕ h y)

  -- nonempty <₁-paths
  data Path⁺ : Cell B → Cell B → Set where
    one  : ∀ {x y} → T (lt₁ x y) → Path⁺ x y
    _∷ᵖ_ : ∀ {x y z} → T (lt₁ x y) → Path⁺ y z → Path⁺ x z

  module _ (H : Height) where
    open Height H
    path-up : ∀ {x y} → Path⁺ x y → T (h x <ℕ h y)
    path-up (one p)   = up _ _ p
    path-up {x} {z} (_∷ᵖ_ {y = y} p q) = <-trans (h x) (h y) (h z) (up _ _ p) (path-up q)

    acyclic : ∀ {x} → Path⁺ x x → ⊥
    acyclic {x} p = <-irrefl (h x) (path-up p)

  ----------------------------------------------------------------------
  -- Soundness of the check

  record StrongSteiner : Set where
    field
      degs   : ∀ x y → T (degAt x y)
      disj   : ∀ x y → T (disjAt x y)
      chain  : ∀ x z → T (chainAt x z)
      aug    : ∀ x → T (augAt x)
      unital : ∀ α x → T (unitAt α x)
      height : Height

  private
    ∨-elim : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
    ∨-elim {true}  _ = inj₁ tt
    ∨-elim {false} p = inj₂ p

    notT : ∀ {a} → T (not a) → T a → ⊥
    notT {true}  () _
    notT {false} _ ()

    all2E : ∀ p → T (all2 p) → ∀ x y → T (p x y)
    all2E p q x y = allE E (p x) (allE E (λ x → allb cs (p x)) q x) y

  sound : T strongSteiner? → StrongSteiner
  sound ok = record
    { degs   = all2E degAt c₁
    ; disj   = all2E disjAt c₂
    ; chain  = all2E chainAt c₃
    ; aug    = allE E augAt c₄
    ; unital = un
    ; height = record { h = hgt ; up = upH }
    }
    where
      c₁ = ∧-fst ok
      r₁ = ∧-snd {all2 degAt} ok
      c₂ = ∧-fst r₁
      r₂ = ∧-snd {all2 disjAt} r₁
      c₃ = ∧-fst r₂
      r₃ = ∧-snd {all2 chainAt} r₂
      c₄ = ∧-fst r₃
      r₄ = ∧-snd {allb cs augAt} r₃
      c₅ = ∧-fst r₄
      r₅ = ∧-snd {allb cs (unitAt true)} r₄
      c₆ = ∧-fst r₅
      c₇ = ∧-snd {allb cs (unitAt false)} r₅
      un : ∀ α x → T (unitAt α x)
      un true  = allE E (unitAt true) c₅
      un false = allE E (unitAt false) c₆
      upH : ∀ x y → T (lt₁ x y) → T (hgt x <ℕ hgt y)
      upH x y l with ∨-elim (all2E hgtAt c₇ x y)
      ... | inj₁ n = ⊥-elim (notT n l)
      ... | inj₂ p = p

------------------------------------------------------------------------
-- Globes up to dimension 4

globes : T (SS.strongSteiner? (globeFB 0)) × T (SS.strongSteiner? (globeFB 1)) ×
         T (SS.strongSteiner? (globeFB 2)) × T (SS.strongSteiner? (globeFB 3)) ×
         T (SS.strongSteiner? (globeFB 4))
globes = tt , tt , tt , tt , tt

------------------------------------------------------------------------
-- A loop is rejected: points p, q and 1-cells a : p → q, b : q → p.
-- Every condition but loop-freeness holds (p <₁ a <₁ q <₁ b <₁ p).

private
  ldeg : Fin 4 → Nat
  ldeg fz                = 0
  ldeg (fs fz)           = 0
  ldeg (fs (fs _))       = 1

  -- a = 2 : p → q,  b = 3 : q → p
  lbd : Bool → Fin 4 → Fin 4 → Nat
  lbd false (fs (fs fz))      fz      = 1
  lbd true  (fs (fs fz))      (fs fz) = 1
  lbd false (fs (fs (fs fz))) (fs fz) = 1
  lbd true  (fs (fs (fs fz))) fz      = 1
  lbd _     _                 _       = 0

loopFB : FB
loopFB = record { Cell = Fin 4 ; enumC = enumFin 4 ; fdeg = ldeg ; fbd = lbd }

module _ where
  open SS loopFB
  loop-rejected : strongSteiner? ≡ false
  loop-rejected = refl

  -- only loop-freeness fails
  loop-rest : T (all2 degAt ∧ all2 disjAt ∧ all2 chainAt ∧ allb (els (enumFin 4)) augAt ∧
                 allb (els (enumFin 4)) (unitAt true) ∧ allb (els (enumFin 4)) (unitAt false))
  loop-rest = tt
