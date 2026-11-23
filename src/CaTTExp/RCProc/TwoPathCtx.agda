------------------------------------------------------------------------
-- The strong order up to dimension 2 on a CaTT context (`Key2Ctx`), the
-- hypothesis of Theorem A (ledger S20 (i), stage 3f).
--
-- A context Γ gives an abstract 2-computad (`ctxComp2`, see
-- CaTTExp.RCProc.TwoPath): its 1-variables e : x → y (variable
-- endpoints, base type ⋆), and its 2-variables α : s ⇒ t over a → b,
-- whose boundaries s and t may be composite 1-cells. `Key2Ctx Γ` asks
-- for
--
--  * a key on variables,
--  * for each 2-variable, its two boundaries as lists of 1-variables
--    (`p⁻ α`, `p⁺ α`) whose bags are the tops of the strict images
--    ⟦ s ⟧ (η Γ) and ⟦ t ⟧ (η Γ),
--  * the strong order conditions of TwoPath.Key2 for these data:
--    key x < key e < key y for every e : x → y; the boundaries are
--    1-paths a → b with key a < key b; key e < key α on ∂⁻ α and
--    key α < key e on ∂⁺ α.
--
-- This is Steiner's strong loop-freeness truncated at dimension 2. It
-- is expected (on paper, not proved here) to hold for pasting contexts
-- and for the cylinders Q↑Y of the naturality filler; it cannot hold
-- for g, h : f ⇒ f (it would need key f < key g < key f), where
-- Theorem A itself fails, since g ∗₁ h and h ∗₁ g have the same strict
-- image (not formalized).
--
-- Not tied down here: the endpoints a, b that `order` gives for each
-- 2-variable's boundary paths are not required to be the endpoints
-- declared in α's type in Γ.
--
-- `tups-≋` turns bag equality of strict-image tops (singleton tuples)
-- into the bag equality used by TwoPath.exchange-complete.
------------------------------------------------------------------------
module CaTTExp.RCProc.TwoPathCtx where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Strict.Bag using (Bag; Tuple; _≈_; count; at; eqT)
open import CaTTExp.Strict.Cell using (top)
open import CaTTExp.Strict.Interp ∅ (λ ()) using (⟦_⟧; η)
open import CaTTExp.RCProc.TwoPath

------------------------------------------------------------------------
-- The 2-computad of a context.

-- 1-variables e : x → y.
Var1 : Ctx → Nat → Set
Var1 Γ e = Σ Nat λ x → Σ Nat λ y → lookup Γ e ≡ just (arr ⋆ (var x) (var y))

-- 2-variables α : s ⇒ t over a → b.
Var2 : Ctx → Nat → Set
Var2 Γ α = Σ Nat λ a → Σ Nat λ b → Σ Tm λ s → Σ Tm λ t →
           lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t)

private
  srcV tgtV : Maybe Ty → Nat
  srcV (just (arr ⋆ (var x) _)) = x
  srcV _                        = 0
  tgtV (just (arr ⋆ _ (var y))) = y
  tgtV _                        = 0

src₀ tgt₀ : Ctx → Nat → Nat
src₀ Γ e = srcV (lookup Γ e)
tgt₀ Γ e = tgtV (lookup Γ e)

src₀-ok : ∀ Γ e {x y} → lookup Γ e ≡ just (arr ⋆ (var x) (var y)) → src₀ Γ e ≡ x
src₀-ok Γ e p rewrite p = refl

tgt₀-ok : ∀ Γ e {x y} → lookup Γ e ≡ just (arr ⋆ (var x) (var y)) → tgt₀ Γ e ≡ y
tgt₀-ok Γ e p rewrite p = refl

ctxComp2 : Ctx → (key : Nat → Nat) → (p⁻ p⁺ : Nat → List Nat) → Comp2
ctxComp2 Γ key p⁻ p⁺ = record
  { E = Var1 Γ ; s₀ = src₀ Γ ; t₀ = tgt₀ Γ
  ; G = Var2 Γ ; ∂⁻ = p⁻ ; ∂⁺ = p⁺ ; key = key }

------------------------------------------------------------------------
-- Singleton tuples.

tups : List Nat → Bag
tups []      = []
tups (v ∷ L) = (v ∷ []) ∷ tups L

private
  ∧-true : ∀ b → (b ∧ true) ≡ b
  ∧-true true  = refl
  ∧-true false = refl

  count-tups : ∀ a L → count (a ∷ []) (tups L) ≡ cnt a L
  count-tups a []      = refl
  count-tups a (x ∷ L) rewrite ∧-true (a ==ℕ x) with a ==ℕ x
  ... | true  = cong suc (count-tups a L)
  ... | false = count-tups a L

tups-≋ : ∀ L M → tups L ≈ tups M → L ≋ M
tups-≋ L M p = mk≋ λ a → trans (sym (count-tups a L)) (trans (at p (a ∷ [])) (count-tups a M))

------------------------------------------------------------------------
-- The hypothesis of Theorem A.

record Key2Ctx (Γ : Ctx) : Set where
  field
    key   : Nat → Nat
    p⁻ p⁺ : Nat → List Nat
    order : TwoPaths.Key2 (ctxComp2 Γ key p⁻ p⁺)
    img⁻  : ∀ α {a b s t} → lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t) →
            top (⟦ s ⟧ (η Γ)) ≈ tups (p⁻ α)
    img⁺  : ∀ α {a b s t} → lookup Γ α ≡ just (arr (arr ⋆ (var a) (var b)) s t) →
            top (⟦ t ⟧ (η Γ)) ≈ tups (p⁺ α)

  comp2 : Comp2
  comp2 = ctxComp2 Γ key p⁻ p⁺
