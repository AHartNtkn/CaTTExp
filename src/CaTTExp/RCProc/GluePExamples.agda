------------------------------------------------------------------------
-- Checks of RCProc.GlueP by evaluation.  Γ is the chain f, g, h of three
-- 1-cells (itself ctxOf of a tree).  The associator (f;g);h ⇛ f;(g;h)
-- is built as a glue cell over the chain tree from the images of the
-- three edges only (the objects come by unification), and composed
-- with its reverse by transT?; a mismatched composite is refused.
------------------------------------------------------------------------
module CaTTExp.RCProc.GluePExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps
open import CaTTExp.RCProc.GlueP

private
  T₃ : Tree
  T₃ = node (leaf ∷ leaf ∷ leaf ∷ [])

  Γ : Ctx
  Γ = ctxOf T₃

  wΓ : Γ ⊢ctx
  wΓ = treeCtx T₃

  -- levels: x0 y1 f2 z3 g4 w5 h6
  imgs : List (Nat × TTm Γ)
  imgs = (2 , from-just (varT wΓ 2)) ∷ (4 , from-just (varT wΓ 4)) ∷ (6 , from-just (varT wΓ 6)) ∷ []

  c0 : ∀ {Δ} → Maybe (TTm Δ) → Maybe (TTm Δ) → Maybe (TTm Δ)
  c0 a b = a >>= λ x → b >>= λ y → rcomp? 0 0 x y

  assocL assocR : ∀ {Δ} → (Nat → Maybe (TTm Δ)) → Maybe (TTm Δ × TTm Δ)
  assocL v = c0 (c0 (v 2) (v 4)) (v 6) >>= λ a → c0 (v 2) (c0 (v 4) (v 6)) >>= λ b → just (a , b)
  assocR v = assocL v >>= λ ab → just (snd ab , fst ab)

  α α⁻ : Maybe (TTm Γ)
  α  = glueT wΓ T₃ imgs assocL
  α⁻ = glueT wΓ T₃ imgs assocR

_ : is-just α ≡ true
_ = refl

_ : is-just (α >>= λ a → α⁻ >>= λ b → transT? a b) ≡ true
_ = refl

-- α ; α is refused: its junction (f;g);h ≠ f;(g;h).
_ : is-just (α >>= λ a → transT? a a) ≡ false
_ = refl
