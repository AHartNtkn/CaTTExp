------------------------------------------------------------------------
-- The stability laws (CaTTExp.Binder.Laws.BinderLaws) of the Gray
-- object formers with the unary-multimap heads
-- (CaTTExp.Binder.Multimap), over any binder-free signature 𝕊₀.
--
-- The Gray formers' laws are CaTTExp.Binder.GrayFormLawsGen's. An mm
-- head has an empty telescope, and its arity and type are built from
-- bound variables and the Gray formers only (no free variable), so
-- substitution leaves them unchanged; its side condition reads only
-- the selector, the emptiness of the telescope and the index.
--
-- So substitution and weakening are admissible for 𝕊₀ + ⊗, \, / + mm
-- with every coh side condition and every stable mark judgment
-- (CaTTExp.Binder.Subst), the checker is complete
-- (CaTTExp.Binder.Completeness), and the extension is conservative
-- over 𝕊₀ (CaTTExp.Binder.Embed).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.GrayForm
open import CaTTExp.Binder.Multimap
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Gray.Biclosed.Syntax as GB

module CaTTExp.Binder.MultimapLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (multimapBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open GMInterface K
open import CaTTExp.Binder.GrayFormLawsGen K GMF gform
open import CaTTExp.Binder.SyntaxLemmas K B using (LC)

------------------------------------------------------------------------
-- Formulas, atoms and arities are closed.

fmB-[] : ∀ x σ → (fmB x) [ σ ]tm ≡ fmB x
fmB-[] (GB.obj i)  σ = refl
fmB-[] (GB.rep _)  σ = refl
fmB-[] (GB.shp _)  σ = refl
fmB-[] (x GB.⊗ y)  σ rewrite fmB-[] x σ | fmB-[] y σ = refl
fmB-[] (x GB.\\ y) σ rewrite fmB-[] x σ | fmB-[] y σ = refl
fmB-[] (x GB.// y) σ rewrite fmB-[] x σ | fmB-[] y σ = refl

sc-fmB : ∀ m x → scTm? m (fmB x) ≡ true
sc-fmB m (GB.obj i)  = refl
sc-fmB m (GB.rep _)  = refl
sc-fmB m (GB.shp _)  = refl
sc-fmB m (x GB.⊗ y)  rewrite sc-fmB m x | sc-fmB m y = refl
sc-fmB m (x GB.\\ y) rewrite sc-fmB m x | sc-fmB m y = refl
sc-fmB m (x GB.// y) rewrite sc-fmB m x | sc-fmB m y = refl

atomsTel-[] : ∀ k σ → atomsTel k [ σ ]tel ≡ atomsTel k
atomsTel-[] zero    σ = refl
atomsTel-[] (suc k) σ rewrite atomsTel-[] k σ = refl

cellsTel-[] : ∀ Θ ps σ → Θ [ σ ]tel ≡ Θ → cellsTel Θ ps [ σ ]tel ≡ cellsTel Θ ps
cellsTel-[] Θ []             σ e = e
cellsTel-[] Θ ((x , z) ∷ ps) σ e =
  cellsTel-[] (Θ ▸ arr ⋆ (fmB x) (fmB z)) ps σ
    (cong₂ (λ Θ′ A → Θ′ ▸ A) e (cong₂ (arr ⋆) (fmB-[] x σ) (fmB-[] z σ)))

argsM-[] : ∀ b y Δ σ → argsM b y Δ [ σ ]tel ≡ argsM b y Δ
argsM-[] b y Δ σ with mmTy b
... | just (ps , _) = cellsTel-[] (atomsTel (atoms b)) ps σ (atomsTel-[] (atoms b) σ)
... | nothing       = refl

argsM-Δ : ∀ b y Δ Δ′ → argsM b y Δ ≡ argsM b y Δ′
argsM-Δ b y Δ Δ′ with mmTy b
... | just _  = refl
... | nothing = refl

resM-[] : ∀ b y Δ σ → resM b y Δ [ σ ]ty ≡ resM b y Δ
resM-[] b y Δ σ with mmTy b
... | just (_ , (x , z)) rewrite fmB-[] x σ | fmB-[] z σ = refl
... | nothing      = refl

resM-Δ : ∀ b y Δ Δ′ → resM b y Δ ≡ resM b y Δ′
resM-Δ b y Δ Δ′ with mmTy b
... | just _  = refl
... | nothing = refl

resM-sc : ∀ b y Δ m → T (scTy? m (resM b y Δ))
resM-sc b y Δ m with mmTy b
... | just (_ , (x , z)) rewrite sc-fmB m x | sc-fmB m z = tt
... | nothing      = tt

sideM-stable : ∀ b y Δ σ → T (sideM b y Δ) → T (sideM b y (Δ [ σ ]tel))
sideM-stable b y Δ σ p rewrite isε-[] Δ σ = p

------------------------------------------------------------------------
-- The laws.

gmLaws : BinderLaws
gmLaws = record
  { side-stable = λ { (gform b) y Δ σ l p → side-stableG b y Δ σ l p
                    ; (mmh b)   y Δ σ _ p → sideM-stable b y Δ σ p }
  ; args-stable = λ { (gform b) y Δ σ l p → args-stableG b y Δ σ l p
                    ; (mmh b)   y Δ σ _ _ → trans (argsM-Δ b y (Δ [ σ ]tel) Δ) (sym (argsM-[] b y Δ σ)) }
  ; res-stable  = λ { (gform b) y Δ σ l p → res-stableG b y Δ σ l p
                    ; (mmh b)   y Δ σ _ _ → trans (resM-Δ b y (Δ [ σ ]tel) Δ) (sym (resM-[] b y Δ σ)) }
  ; res-sc      = λ { (gform b) y Δ m p q → res-scG b y Δ m p q
                    ; (mmh b)   y Δ m _ _ → resM-sc b y Δ m }
  }
