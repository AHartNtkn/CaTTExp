------------------------------------------------------------------------
-- The `ord` coherence rule: marking every object of a head `ord`
-- computes its side condition in the Gray quotient, which recovers
-- two-tier L from uniform L (notes/ord-recovers-two-tier.md; ledger S16(b)).
--
-- No checker for the uniform side condition exists yet (ledger S3), so,
-- as in CaTTExp.Uniform.Marks, the two side-condition procedures are
-- taken as data (`Oracle`): the uniform one, SC_{V+S}, and the two-tier
-- one on the projected head, SC_𝔉, related by the projection π
-- (spec §2.3, ledger S2: a uniform witness projects to a two-tier one).
--
-- Part 1 proves, on that data:
--   * with every object `ord`, the rule set accepts exactly the
--     two-tier heads                                  (recovers)
--   * with no `ord`, it accepts exactly the uniform heads
--                                                      (conservative)
--   * it never accepts more than two-tier L            (within-two-tier)
--   * adding marks only adds heads                     (mark-mono)
--
-- Part 2 proves the path-level form of the semantic step: a map of
-- top-dimensional letter paths into a monoid that sends every inner
-- letter to the unit factors through erasing the inner letters
-- (the projection π on a path of letters, notes/uniform-marks.md (F1),
-- (F3)).  The full statement, that a strict model killing the inner
-- letters factors through F_{V+S}(Γ) → 𝔉(Γ), is requirement 4 together
-- with the definition of inner letters; it is proved on paper only.
------------------------------------------------------------------------

module CaTTExp.Uniform.OrdCoh where

open import CaTTExp.Prelude

------------------------------------------------------------------------
-- Booleans

T-≡ : ∀ {b} → T b → b ≡ true
T-≡ {true} _ = refl

≡-T : ∀ {b} → b ≡ true → T b
≡-T refl = tt

------------------------------------------------------------------------
-- Part 1. The rule, on side-condition data.

record Oracle (H : Set) : Set where
  field
    scU  : H → Bool                    -- SC_{V+S}(Γ, t → u)
    scG  : H → Bool                    -- SC_𝔉 on the projected head
    incl : ∀ h → T (scU h) → T (scG h) -- π of a uniform witness

module Rules {H : Set} (O : Oracle H) where
  open Oracle O

  -- `allOrd h` : every object variable of the head's pasting context is
  -- sent by the substitution to an object variable marked `ord`.
  -- (COH)     : the uniform coherence rule, always available.
  -- (COH-ord) : the two-tier side condition, available when allOrd.
  accept : Bool → H → Bool
  accept allOrd h = scU h ∨ (allOrd ∧ scG h)

  recovers : ∀ h → accept true h ≡ scG h
  recovers h with scU h | incl h
  ... | true  | i = sym (T-≡ (i tt))
  ... | false | _ = refl

  conservative : ∀ h → accept false h ≡ scU h
  conservative h with scU h
  ... | true  = refl
  ... | false = refl

  within-two-tier : ∀ b h → T (accept b h) → T (scG h)
  within-two-tier b h p with scU h | incl h
  ... | true  | i = i tt
  ... | false | _ = ∧-snd {b} p

  mark-mono : ∀ h → T (accept false h) → T (accept true h)
  mark-mono h p = ≡-T (trans (recovers h) (T-≡ (within-two-tier false h p)))

------------------------------------------------------------------------
-- Part 2. Path-level factorization through erasing inner letters.

record Monoid : Set₁ where
  field
    Carrier : Set
    ε       : Carrier
    _·_     : Carrier → Carrier → Carrier
    idl     : ∀ x → ε · x ≡ x

module Erase {L : Set} (inner : L → Bool) (M : Monoid)
             (σ : L → Monoid.Carrier M)
             (kill : ∀ ℓ → T (inner ℓ) → σ ℓ ≡ Monoid.ε M)
  where
  open Monoid M

  -- evaluation of a ∗-path of letters (composition in diagrammatic order)
  ev : List L → Carrier
  ev []       = ε
  ev (ℓ ∷ w) = σ ℓ · ev w

  -- the projection on paths: inner letters become identities
  π : List L → List L
  π = filter (λ ℓ → not (inner ℓ))

  private
    step : ∀ ℓ w (b : Bool) → inner ℓ ≡ b → ev w ≡ ev (π w) →
           σ ℓ · ev w ≡ ev (if not b then ℓ ∷ π w else π w)
    step ℓ w true  e ih =
      trans (cong (λ x → x · ev w) (kill ℓ (≡-T e))) (trans (idl (ev w)) ih)
    step ℓ w false e ih = cong (λ x → σ ℓ · x) ih

  factor : ∀ w → ev w ≡ ev (π w)
  factor []       = refl
  factor (ℓ ∷ w) = step ℓ w (inner ℓ) refl (factor w)

  -- two paths with the same projection have the same value
  coherent : ∀ v w → π v ≡ π w → ev v ≡ ev w
  coherent v w e = trans (factor v) (trans (cong ev e) (sym (factor w)))
