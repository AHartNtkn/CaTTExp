------------------------------------------------------------------------
-- The optional judgement Γ ⊢hpol (design-decisions.md §2.7, ledger B25):
-- a decidable syntactic class of named contexts whose free strict
-- ω-category is known to agree with the free weak one. It is NOT a
-- premise of any kernel rule; it only lets a weight presentation use
-- the base itself instead of a resolution.
--
-- First base rule (this module): "positive path 2-polygraphs":
--   * object variables  x : ⋆;
--   * 1-cells  f : x → y  between earlier object variables;
--   * 2-cells  α : s ⇒ t  where s and t are NONEMPTY composites
--     (`comp` trees) of earlier 1-cell variables with matching
--     endpoints.
-- Every member is a 2-polygraph in which no generator has an identity
-- in its boundary (a nonempty path of generators is never an identity
-- in the free strict 2-category), i.e. a positive 2-polygraph, so it
-- is homotopical by Chanavat (arXiv 2603.22242, Cor. 3.39). That
-- theorem is cited, not formalised. `hpol?` is a boolean test (it
-- also requires every bound name to be fresh); that it selects
-- exactly the positive path 2-polygraphs among named contexts is
-- argued informally here, not proved. The examples are checked.
--
-- Further base rules to add (design-decisions.md §2.2 and homotopy-
-- polygraphs r5): pasting contexts, orientals, positive-to-one,
-- no-matching positive 3-polygraphs, top weight ≤ 2, and closure
-- under suspension.
------------------------------------------------------------------------
module CaTTExp.Lim.Hpol where

open import CaTTExp.Prelude
open import CaTTExp.Pure hiding (∅)
open import CaTTExp.Lim.Named
open import CaTTExp.Lim.Terms

private
  v : Nat → Tm
  v = var

  -- The coherence head (pasting context and type) of `comp`.
  compHead : Maybe (Ctx × Ty)
  compHead with comp (v 0) (v 0) (v 0) (v 0) (v 0)
  ... | coh Γ A _ = just (Γ , A)
  ... | _         = nothing

  isCompHead : Ctx → Ty → Bool
  isCompHead Γ A with compHead
  ... | just (Γ′ , A′) = (Γ ==Ctx Γ′) ∧ (A ==Ty A′)
  ... | nothing        = false

  isObj : NCtx → Name → Bool
  isObj Γ x with typeOf Γ x
  ... | just ⋆ = true
  ... | _      = false

  -- Endpoints of a nonempty path of 1-cell variables, if the term is one.
  path : NCtx → Tm → Maybe (Name × Name)
  path Γ (var f) with typeOf Γ f
  ... | just (arr ⋆ (var a) (var b)) = just (a , b)
  ... | _ = nothing
  path Γ (coh Γc Ac (((((⟨⟩ ,ₛ var x) ,ₛ var y) ,ₛ p) ,ₛ var z) ,ₛ q))
    with isCompHead Γc Ac | path Γ p | path Γ q
  ... | true | just (a , b) | just (b′ , c) =
        if (a ==ℕ x) ∧ (b ==ℕ y) ∧ (b′ ==ℕ y) ∧ (c ==ℕ z) then just (a , c) else nothing
  ... | _ | _ | _ = nothing
  path Γ _ = nothing

  sameEnds : Maybe (Name × Name) → Maybe (Name × Name) → Name → Name → Bool
  sameEnds (just (a , b)) (just (a′ , b′)) x y =
    (a ==ℕ x) ∧ (b ==ℕ y) ∧ (a′ ==ℕ x) ∧ (b′ ==ℕ y)
  sameEnds _ _ _ _ = false

  entryOK : NCtx → Ty → Bool
  entryOK Γ ⋆ = true
  entryOK Γ (arr ⋆ (var a) (var b)) = isObj Γ a ∧ isObj Γ b
  entryOK Γ (arr (arr ⋆ (var a) (var b)) s t) =
    isObj Γ a ∧ isObj Γ b ∧ sameEnds (path Γ s) (path Γ t) a b
  entryOK Γ _ = false

private
  bound : NCtx → Name → Bool
  bound ∅ n = false
  bound (K ▹ x ∶ _) n = (n ==ℕ x) ∨ bound K n

hpol? : NCtx → Bool
hpol? ∅           = true
hpol? (Γ ▹ x ∶ A) = hpol? Γ ∧ not (bound Γ x) ∧ entryOK Γ A

-- The judgement Γ ⊢hpol (first base rule).
_⊢hpol : NCtx → Set
Γ ⊢hpol = T (hpol? Γ)

------------------------------------------------------------------------
-- Examples.

private
  _⇒⋆_ : Nat → Nat → Ty
  a ⇒⋆ b = arr ⋆ (v a) (v b)

-- Parallel pair x ⇉ y (equalizers): a graph.
Γpair : NCtx
Γpair = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (0 ⇒⋆ 1)

pair-hpol : Γpair ⊢hpol
pair-hpol = tt

-- x, a : x → x, μ : a · a ⇒ a.
Γmu : NCtx
Γmu = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)
        ▹ 2 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 0) (v 1) (v 0) (v 1)) (v 1)

mu-hpol : Γmu ⊢hpol
mu-hpol = tt

-- The bubble x, σ : 1_x ⇒ 1_x is not in the class.
Γbub : NCtx
Γbub = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ arr (0 ⇒⋆ 0) (idc (v 0)) (idc (v 0))

bubble-not-hpol : hpol? Γbub ≡ false
bubble-not-hpol = refl

-- A 2-cell between paths with mismatched endpoints is rejected.
Γbad : NCtx
Γbad = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (1 ⇒⋆ 0)
         ▹ 4 ∶ arr (0 ⇒⋆ 1) (v 2) (v 3)

bad-not-hpol : hpol? Γbad ≡ false
bad-not-hpol = refl

-- Shadowing is rejected (independent review counterexample).
Γsh : NCtx
Γsh = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ ⋆ ▹ 2 ∶ (0 ⇒⋆ 1) ▹ 3 ∶ (1 ⇒⋆ 0) ▹ 1 ∶ (0 ⇒⋆ 0)
        ▹ 4 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 1) (v 2) (v 0) (v 3)) (v 1)

sh-not-hpol : hpol? Γsh ≡ false
sh-not-hpol = refl

selfloop-not-hpol : hpol? (∅ ▹ 0 ∶ ⋆ ▹ 0 ∶ (0 ⇒⋆ 0)) ≡ false
selfloop-not-hpol = refl

-- Composites of length 2 on both sides: x, f g h k : x → x,
-- β : f · g ⇒ h · k.
Γsq : NCtx
Γsq = ∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0) ▹ 2 ∶ (0 ⇒⋆ 0) ▹ 3 ∶ (0 ⇒⋆ 0) ▹ 4 ∶ (0 ⇒⋆ 0)
        ▹ 5 ∶ arr (0 ⇒⋆ 0) (comp (v 0) (v 0) (v 1) (v 0) (v 2))
                           (comp (v 0) (v 0) (v 3) (v 0) (v 4))

sq-hpol : Γsq ⊢hpol
sq-hpol = tt

-- An identity on one side only is rejected.
oneid-not-hpol : hpol? (∅ ▹ 0 ∶ ⋆ ▹ 1 ∶ (0 ⇒⋆ 0)
                          ▹ 2 ∶ arr (0 ⇒⋆ 0) (v 1) (idc (v 0))) ≡ false
oneid-not-hpol = refl
