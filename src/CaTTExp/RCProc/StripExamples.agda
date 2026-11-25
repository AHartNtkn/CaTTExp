------------------------------------------------------------------------
-- A check of RCProc.Strip.stripR by evaluation.  Γ is the 1-disc
-- x, y, f : x → y.  K is the unitor f ⇛ f ;₀ 1_y (an invertible 2-cell),
-- t = u = 1_f, and V : t ;₁ K ⇛ u ;₁ K the identity.  stripR builds
-- t ⇛ u through the seven steps (two unit cells, two associators,
-- whiskered cancellations and V ;₁ K⁻), with rcP on Γ (globular) as
-- the recursion oracle for the inverse and the cancellations.
------------------------------------------------------------------------
module CaTTExp.RCProc.StripExamples where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.RCProc using (rcP)
open import CaTTExp.RCProc.TypedSub
open import CaTTExp.RCProc.TypedOps using (ansT)
open import CaTTExp.RCProc.GlueP using (treeCtx; varT)
open import CaTTExp.RCProc.Strip

private
  T₁ : Tree
  T₁ = node (leaf ∷ [])

  Γ : Ctx
  Γ = ctxOf T₁

  wΓ : Γ ⊢ctx
  wΓ = treeCtx T₁

  recP : Rec Γ
  recP a b = decTy (ty b) (ty a) >>= λ p →
             rcP (der a) (subst (Γ ⊢tm tm b ∶_) p (der b)) >>= λ r → just (ansT r)

  f : Maybe (TTm Γ)
  f = varT wΓ 2

  κ t V : Maybe (TTm Γ)
  κ = f >>= λ f′ → tgtT f′ >>= idT >>= λ one → comp2? 0 f′ one >>= recP f′
  t = f >>= idT
  V = t >>= λ t′ → κ >>= λ K′ → comp2? 1 t′ K′ >>= λ tK → recP tK tK

  res : Maybe (TTm Γ)
  res = t >>= λ t′ → κ >>= λ K′ → V >>= λ V′ → stripR wΓ recP t′ t′ K′ V′

_ : is-just κ ≡ true
_ = refl

_ : is-just V ≡ true
_ = refl

_ : is-just res ≡ true
_ = refl

-- With V replaced by K (not a cell t ;₁ K ⇛ u ;₁ K) the junctions fail.
_ : is-just (t >>= λ t′ → κ >>= λ K′ → stripR wΓ recP t′ t′ K′ K′) ≡ false
_ = refl
