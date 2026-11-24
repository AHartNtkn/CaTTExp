------------------------------------------------------------------------
-- Ledger F12d (notes/descent-vs-init.md §5b): universality of finite
-- coproducts (U-⊔, U-∅) as a rule of its own.
--
--   (U-⊔)  f : W → A ⊔ B  ⟹  [π, π′] : (W ×_{A⊔B} A) ⊔ (W ×_{A⊔B} B) → W  inv
--   (U-∅)  f : W → ∅      ⟹  f inv
--
-- Machine-checked (no postulates), 1-truncated shadows:
--   * Part A, soundness shadow in Set (Model A): the comparison has a
--     two-sided inverse up to pointwise equality, and ∅ is strict.  The
--     soundness claim proper, in Cat_ω, is cited in the note (DESC-grpd
--     soundness, spec §9.2), not encoded.
--   * Part B, U-⊔ is strictly weaker than DESC-grpd: in the frame 2
--     (Model B), U-⊔ and U-∅ hold but the coproduct injections of
--     ⊤ ⊔ ⊤ are not disjoint, while disjointness is a theorem of DESC-grpd.
--   * Part C, U-⊔ is not derivable without DESC: Model D
--     (CaTTExp.Descent.GlueNotUniversal, `not-universal`) satisfies the
--     non-DESC rules (argued there) and has a map z : 𝟙 → D₀ + 𝟙 whose
--     comparison P₁ + P₂ → 𝟙 has no inverse.  Re-exported below.
--
-- Scope and honesty notes.
--   * Model B is the poset 2 as a category: pullbacks are meets,
--     coproducts are joins, ∅ = false.  That Model B (and Model D)
--     satisfy the other non-DESC rules is argued in
--     notes/descent-vs-init.md §3, not encoded.
------------------------------------------------------------------------
module CaTTExp.Descent.CoprodUniversality where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Part A: Set

module SetModel where

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  inl≢inr : ∀ {A B : Set} {a : A} {b : B} → inl {B = B} a ≡ inr b → ⊥
  inl≢inr ()

  module _ {W A B : Set} (f : W → A ⊎ B) where

    -- the pullbacks of the two injections along f
    PA PB : Set
    PA = Σ W (λ w → Σ A (λ a → f w ≡ inl a))
    PB = Σ W (λ w → Σ B (λ b → f w ≡ inr b))

    comparison : PA ⊎ PB → W
    comparison (inl (w , _)) = w
    comparison (inr (w , _)) = w

    -- the inverse, by case analysis on f w
    split′ : (w : W) (x : A ⊎ B) → f w ≡ x → PA ⊎ PB
    split′ w (inl a) e = inl (w , a , e)
    split′ w (inr b) e = inr (w , b , e)

    split : W → PA ⊎ PB
    split w = split′ w (f w) refl

    comparison-split′ : ∀ w x (e : f w ≡ x) → comparison (split′ w x e) ≡ w
    comparison-split′ w (inl a) e = refl
    comparison-split′ w (inr b) e = refl

    comparison-split : ∀ w → comparison (split w) ≡ w
    comparison-split w = comparison-split′ w (f w) refl

    -- split′ does not depend on how f w was named (uses K)
    split-irr : ∀ w x (e : f w ≡ x) → split′ w x e ≡ split w
    split-irr w x refl = refl

    split-comparison : ∀ u → split (comparison u) ≡ u
    split-comparison (inl (w , a , e)) = sym (split-irr w (inl a) e)
    split-comparison (inr (w , b , e)) = sym (split-irr w (inr b) e)

  -- U-∅: a map into ∅ is invertible
  strict-∅ : ∀ {W : Set} (f : W → ⊥) →
             Σ (⊥ → W) (λ g → (∀ w → g (f w) ≡ w))
  strict-∅ f = ⊥-elim , λ w → ⊥-elim (f w)

------------------------------------------------------------------------
-- Part B: the frame 2

module FrameTwo where

  -- the poset 2 as a category: a map a → b is a proof of a ≤ b
  Hom : Bool → Bool → Set
  Hom a b = T (not a ∨ b)

  -- pullback over a ⊔ b is the meet, coproduct is the join
  -- U-⊔: if w ≤ a ∨ b then w ≤ (w ∧ a) ∨ (w ∧ b); the reverse map
  -- (w ∧ a) ∨ (w ∧ b) ≤ w always exists.
  U-⊔ : ∀ w a b → Hom w (a ∨ b) → Hom w ((w ∧ a) ∨ (w ∧ b))
  U-⊔ false a     b     _ = tt
  U-⊔ true  true  b     _ = tt
  U-⊔ true  false true  _ = tt
  U-⊔ true  false false ()

  U-⊔-back : ∀ w a b → Hom ((w ∧ a) ∨ (w ∧ b)) w
  U-⊔-back false a     b     = tt
  U-⊔-back true  true  b     = tt
  U-⊔-back true  false true  = tt
  U-⊔-back true  false false = tt

  U-∅ : ∀ w → Hom w false → Hom false w
  U-∅ w _ = tt

  -- not disjoint: the pullback of the two injections ⊤ → ⊤ ⊔ ⊤ is
  -- true ∧ true = true, which is not initial (there is no map true → false)
  not-disjoint : Hom (true ∧ true) false → ⊥
  not-disjoint ()

------------------------------------------------------------------------
-- Part C: Model D

open import CaTTExp.Descent.GlueNotUniversal public
  using () renaming (not-universal to U-⊔-fails-in-Model-D)
