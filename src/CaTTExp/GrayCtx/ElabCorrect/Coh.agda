------------------------------------------------------------------------
-- Correctness of Elab.cohT (ledger S20 (ii), step 2).
--
-- cohT Γ τ build cells builds the source and target inside the pasting
-- context P = ctxOf τ with `build`, and the substitution with `fill`.
-- If build's source and target are typed in P with a common type A and
-- satisfy the side condition, the keys tops T cover P, and the images
-- are those of a typed σ₀ : P, then cohT returns coh P (A, s → u) σ₀
-- and it is well typed. Everything but σ₀ is about the shape (T and
-- build) alone.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.ElabCorrect.Coh where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab using (cohT; tops; tyOf)
open import CaTTExp.Derived using (ps-ctx)
open import CaTTExp.GrayCtx.ElabCorrect.Fill

-- The facts about a shape: the builder's output is typed in P and
-- satisfies the side condition, and the tops cover P.
record ShapeOK (τ : Tree) (build : Ctx → Maybe (Tm × Tm)) : Set where
  constructor shapeOK
  field
    src tgt : Tm
    ty      : Ty
    built   : build (ctxOf τ) ≡ just (src , tgt)
    src-wf  : ctxOf τ ⊢tm src ∶ ty
    tgt-wf  : ctxOf τ ⊢tm tgt ∶ ty
    side-ok : T (cattSide (ctxOf τ) ty src tgt)
    cover   : T (covers (ctxOf τ) (tops τ))
open ShapeOK public

cohT-ok : ∀ {Γ σ₀} τ build (sh : ShapeOK τ build) → Γ ⊢sub σ₀ ∶ ctxOf τ →
          (cohT Γ τ build (mapL (lookupₛ σ₀) (tops τ))
             ≡ just (coh (ctxOf τ) (arr (ty sh) (src sh) (tgt sh)) σ₀))
          × (Γ ⊢tm coh (ctxOf τ) (arr (ty sh) (src sh) (tgt sh)) σ₀
                ∶ arr (ty sh) (src sh) (tgt sh) [ σ₀ ]ty)
cohT-ok {Γ} {σ₀} τ build sh s =
  trans (bind-just {m = build (ctxOf τ)} (built sh))
  (trans (bind-just {m = tyOf (ctxOf τ) (src sh)} (tyOf-typed (src-wf sh)))
  (trans (bind-just {m = zipA' } (zipA-zipK (tops τ) σ₀))
         (bind-just {m = fill Γ (ctxOf τ) (zipK (tops τ) σ₀)}
                    (fill-ok (tops τ) s pT (cover sh))))) ,
  coh-wf pT (ps-ctx pT) (arr-wf (src-wf sh) (tgt-wf sh)) (side-ok sh) s
  where
  pT = snd (psOf τ)
  open import CaTTExp.GrayCtx.Elab using (zipA; fill)
  zipA' = zipA (tops τ) (mapL (lookupₛ σ₀) (tops τ))
