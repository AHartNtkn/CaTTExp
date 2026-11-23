------------------------------------------------------------------------
-- Deep type derivations (ledger S26i (2)).
--
-- `DTy Γ A`: A is well formed together with every iterated boundary:
-- for A = arr B s u, DTy Γ B and s, u : B. A deep derivation gives an
-- ordinary one (`dty-ty`); the converse is presupposition (tm-ty) on
-- the boundaries, which a proof of a binder's res-wf cannot call (it
-- is what tm-ty's binder case needs). So the typing of naturality
-- cylinders in binder syntax carries deep types, computed from
--
--  * a deep context (`DCtx`: every entry's type deep), for variables;
--  * pure CaTT, for coherences over embedded pure pasting contexts
--    (pure presupposition, CaTTExp.Derived.tm-ty, embedded);
--  * substitution, which preserves deep types (`dty[]`).
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Binder.Signature
import CaTTExp.Binder.Mark as BM
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Pure as P
import CaTTExp.Derived as Dv

module CaTTExp.Binder.Deep
  (𝕊 : Signature)
  (side : Signature.Ctx 𝕊 → Signature.Ty 𝕊 → Signature.Tm 𝕊 → Signature.Tm 𝕊 → Bool)
  (mark : Signature.Ctx 𝕊 → BM.Mark → Signature.Tm 𝕊 → Bool)
  where

open Signature 𝕊
open import CaTTExp.Binder.TypingWith 𝕊 side mark
open import CaTTExp.Binder.Rename 𝕊 side mark using (MarkRen; wk-tm; lookup-top; lookup-pop)
open import CaTTExp.Binder.Subst 𝕊 side mark using (MarkSub; MarkVar; tm[])
open import CaTTExp.Binder.Scoping 𝕊 side mark using (sub-ctx)
open import CaTTExp.Binder.Presup 𝕊 side mark using (tm-ctx; ty-ctx)
open import CaTTExp.Binder.PureEmbed 𝕊 side mark
open Laws 𝕊 using (Closed; BinderLaws)

------------------------------------------------------------------------
-- Deep types and contexts.

DTy : Ctx → Ty → Set
DTy Γ ⋆           = Γ ⊢ctx
DTy Γ (arr A s u) = DTy Γ A × (Γ ⊢tm s ∶ A) × (Γ ⊢tm u ∶ A)

dty-ty : ∀ {Γ} A → DTy Γ A → Γ ⊢ty A
dty-ty ⋆           w           = ⋆-wf w
dty-ty (arr A s u) (_ , ds , du) = arr-wf ds du

dty-ctx : ∀ {Γ} A → DTy Γ A → Γ ⊢ctx
dty-ctx A d = ty-ctx (dty-ty A d)

-- A term with a deep type.
DTm : Ctx → Tm → Ty → Set
DTm Γ t A = (Γ ⊢tm t ∶ A) × DTy Γ A

DCtx : Ctx → Set
DCtx ε              = ⊤
DCtx (Γ ▸[ _ ] A) = DCtx Γ × DTy Γ A

dctx-ctx : ∀ Γ → DCtx Γ → Γ ⊢ctx
dctx-ctx ε              _       = ε-wf
dctx-ctx (Γ ▸[ _ ] A) (w , a) = ▸-wf (dctx-ctx Γ w) (dty-ty A a)

------------------------------------------------------------------------
-- Weakening and substitution.

module _ (closed : Closed) (laws : BinderLaws) (mren : MarkRen) (msub : MarkSub) (mvar : MarkVar) where

  dty-wk : ∀ {Γ ms B} A → DTy Γ A → (Γ ▸[ ms ] B) ⊢ctx → DTy (Γ ▸[ ms ] B) A
  dty-wk ⋆           _             c = c
  dty-wk (arr A s u) (a , ds , du) c = dty-wk A a c , wk-tm closed laws mren ds c , wk-tm closed laws mren du c

  dty[] : ∀ {Γ Δ σ} A → DTy Γ A → Δ ⊢sub σ ∶ Γ → DTy Δ (A [ σ ]ty)
  dty[] ⋆           _             s = sub-ctx closed laws s
  dty[] (arr A t u) (a , dt , du) s =
    dty[] A a s , tm[] closed laws mren msub mvar dt s , tm[] closed laws mren msub mvar du s

  -- Variables have the deep types of their entries.
  dlookup : ∀ Γ i {A} → DCtx Γ → lookup Γ i ≡ just A → DTy Γ A
  dlookup ε              i      _       ()
  dlookup (Γ ▸[ ms ] B) i {A} (w , b) e with i ==ℕ len Γ in q
  ... | true  = subst (DTy (Γ ▸[ ms ] B)) (just-inj e) (dty-wk B b c)
    where c = dctx-ctx (Γ ▸[ ms ] B) (w , b)
          just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
          just-inj refl = refl
  ... | false = dty-wk A (dlookup Γ i w e) (dctx-ctx (Γ ▸[ ms ] B) (w , b))

  dvar : ∀ {Γ i A} → DCtx Γ → lookup Γ i ≡ just A → DTm Γ (var i) A
  dvar {Γ} {i} w e = var-wf (dctx-ctx Γ w) e , dlookup Γ i w e

  ----------------------------------------------------------------------
  -- Coherences over embedded pure contexts.

  module _ (sp : SidePure) where

    -- Pure types are deep, by pure presupposition.
    pdty : ∀ {Q} B → Q P.⊢ty B → DTy (embCtx Q) (embTy B)
    pdty P.⋆           (P.⋆-wf w)     = ctx-emb sp w
    pdty (P.arr B s u) (P.arr-wf d e) = pdty B (Dv.tm-ty d) , tm-emb sp d , tm-emb sp e

    -- coh Q B σ, with its deep type B[σ].
    dcoh : ∀ {Γ Q A s u σ} → Q P.⊢ps → Q P.⊢ctx → Q P.⊢ty P.arr A s u → T (P.cattSide Q A s u) →
           Γ ⊢sub σ ∶ embCtx Q →
           DTm Γ (coh (embCtx Q) (embTy (P.arr A s u)) σ) (embTy (P.arr A s u) [ σ ]ty)
    dcoh {Γ} {Q} {A} {s} {u} {σ} p w a ok γ =
      coh-wf (ps-emb₀ p) (ctx-emb sp w) (ty-emb sp a) (sp Q A s u ok) γ ,
      dty[] (embTy (P.arr A s u)) (pdty (P.arr A s u) a) γ
