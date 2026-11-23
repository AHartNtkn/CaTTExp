------------------------------------------------------------------------
-- The stability laws (CaTTExp.Binder.Laws.BinderLaws) of the Gray
-- object formers with the cell heads mmc (CaTTExp.Binder.MultimapCells),
-- over any binder-free signature 𝕊₀.
--
-- An mmc head has an empty telescope; its arity and type are built from
-- bound variables, the Gray formers and mmc heads applied to bound
-- variables, with no free variable, so substitution leaves them
-- unchanged; its side condition reads only the selector, the emptiness
-- of the telescope and the index. So substitution and weakening are
-- admissible for 𝕊₀ + ⊗, \, / + mmc with every coh side condition and
-- every stable mark judgment, the checker is complete, and the
-- extension is conservative over 𝕊₀ (CaTTExp.Binder.Embed).
------------------------------------------------------------------------
open import CaTTExp.Prelude
import CaTTExp.Signature as Old
open import CaTTExp.Binder.Signature
open import CaTTExp.Binder.Embed using (Binders; extend)
open import CaTTExp.Binder.GrayForm
open import CaTTExp.Binder.Multimap using (MMI; mmi; atoms; mctx)
open import CaTTExp.Binder.MultimapCells
import CaTTExp.Binder.Laws as Laws
import CaTTExp.Gray.Biclosed.Syntax as GB
import CaTTExp.Gray.Biclosed.Typing as GT

module CaTTExp.Binder.MultimapCellsLaws (𝕊₀ : Old.Signature) where

𝕊 : Signature
𝕊 = extend 𝕊₀ (cellBinders (Old.Signature.K 𝕊₀))

open Signature 𝕊
open Laws 𝕊
open GCInterface K
open import CaTTExp.Binder.GrayFormLawsGen K GCF gform
open import CaTTExp.Binder.SyntaxLemmas K B using (LC)

------------------------------------------------------------------------
-- Closedness.

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

bvsOf-∘ : ∀ ρ js σ → bvsOf ρ js ∘ σ ≡ bvsOf (ρ ∘ σ) js
bvsOf-∘ ρ []       σ = refl
bvsOf-∘ ρ (j ∷ js) σ = bvsOf-∘ (ρ ,ₛ bvar 0 j) js σ

sc-bvsOf : ∀ m ρ js → scSub? m ρ ≡ true → scSub? m (bvsOf ρ js) ≡ true
sc-bvsOf m ρ []       e = e
sc-bvsOf m ρ (j ∷ js) e = sc-bvsOf m (ρ ,ₛ bvar 0 j) js (cong (_∧ true) e)

supArgs-∘ : ∀ k c σ → supArgs k c ∘ σ ≡ supArgs k c
supArgs-∘ k c σ =
  trans (bvsOf-∘ (bvsOf ⟨⟩ (catoms c)) (GT.map (k +_) (cvars c)) σ)
        (cong (λ ρ → bvsOf ρ (GT.map (k +_) (cvars c))) (bvsOf-∘ ⟨⟩ (catoms c) σ))

sc-supArgs : ∀ m k c → scSub? m (supArgs k c) ≡ true
sc-supArgs m k c = sc-bvsOf m (bvsOf ⟨⟩ (catoms c)) (GT.map (k +_) (cvars c)) (sc-bvsOf m ⟨⟩ (catoms c) refl)

trHead-[] : ∀ k Φ u σ → (trHead k Φ u) [ σ ]tm ≡ trHead k Φ u
trHead-[] k Φ u σ = cong (bnd _ 0 ε) (supArgs-∘ k (canon k Φ u) σ)

sc-trHead : ∀ m k Φ u → scTm? m (trHead k Φ u) ≡ true
sc-trHead m k Φ u = sc-supArgs m k (canon k Φ u)

trTm-[] : ∀ k Φ u σ → (trTm k Φ u) [ σ ]tm ≡ trTm k Φ u
trTm-[] k Φ (GB.var j)         σ = refl
trTm-[] k Φ u@(GB.mP _ _)      σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.eL _ _)      σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.eR _ _)      σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.pP _ _)      σ = trHead-[] k Φ u σ
trTm-[] k Φ u@GB.pt            σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.iP _)        σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.idt _)       σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.comp _ _)    σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.glue _ _ _)  σ = trHead-[] k Φ u σ
trTm-[] k Φ u@(GB.here _ _ _ _) σ = trHead-[] k Φ u σ

sc-trTm : ∀ m k Φ u → scTm? m (trTm k Φ u) ≡ true
sc-trTm m k Φ (GB.var j)         = refl
sc-trTm m k Φ u@(GB.mP _ _)      = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.eL _ _)      = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.eR _ _)      = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.pP _ _)      = sc-trHead m k Φ u
sc-trTm m k Φ u@GB.pt            = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.iP _)        = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.idt _)       = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.comp _ _)    = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.glue _ _ _)  = sc-trHead m k Φ u
sc-trTm m k Φ u@(GB.here _ _ _ _) = sc-trHead m k Φ u

trTy-[] : ∀ k Φ A σ → (trTy k Φ A) [ σ ]ty ≡ trTy k Φ A
trTy-[] k Φ (GB.op ([] GB.▸ _))              σ = refl
trTy-[] k Φ (GB.op ((x ∷ []) GB.▸ z))        σ rewrite fmB-[] x σ | fmB-[] z σ = refl
trTy-[] k Φ (GB.op ((_ ∷ _ ∷ _) GB.▸ _))     σ = refl
trTy-[] k Φ (GB.hom _ _ A s t) σ rewrite trTy-[] k Φ A σ | trTm-[] k Φ s σ | trTm-[] k Φ t σ = refl

sc-trTy : ∀ m k Φ A → scTy? m (trTy k Φ A) ≡ true
sc-trTy m k Φ (GB.op ([] GB.▸ _))          = refl
sc-trTy m k Φ (GB.op ((x ∷ []) GB.▸ z))    rewrite sc-fmB m x | sc-fmB m z = refl
sc-trTy m k Φ (GB.op ((_ ∷ _ ∷ _) GB.▸ _)) = refl
sc-trTy m k Φ (GB.hom _ _ A s t) rewrite sc-trTy m k Φ A | sc-trTm m k Φ s | sc-trTm m k Φ t = refl

atomsTel-[] : ∀ k σ → atomsTel k [ σ ]tel ≡ atomsTel k
atomsTel-[] zero    σ = refl
atomsTel-[] (suc k) σ rewrite atomsTel-[] k σ = refl

cellsTel-[] : ∀ k Φ Θ As σ → Θ [ σ ]tel ≡ Θ → cellsTel k Φ Θ As [ σ ]tel ≡ cellsTel k Φ Θ As
cellsTel-[] k Φ Θ []       σ e = e
cellsTel-[] k Φ Θ (A ∷ As) σ e =
  cellsTel-[] k Φ _ As σ (cong₂ (λ Θ′ B′ → Θ′ ▸[ marksOf A ] B′) e (trTy-[] k Φ A σ))

argsC-[] : ∀ b y Δ σ → argsC b y Δ [ σ ]tel ≡ argsC b y Δ
argsC-[] (mmi k Φ t) y Δ σ = cellsTel-[] k Φ (atomsTel k) Φ σ (atomsTel-[] k σ)

resC-[] : ∀ b y Δ σ → resC b y Δ [ σ ]ty ≡ resC b y Δ
resC-[] b y Δ σ with mmcTy b
... | just A  = trTy-[] (atoms b) (mctx b) A σ
... | nothing = refl

resC-Δ : ∀ b y Δ Δ′ → resC b y Δ ≡ resC b y Δ′
resC-Δ b y Δ Δ′ with mmcTy b
... | just _  = refl
... | nothing = refl

resC-sc : ∀ b y Δ m → T (scTy? m (resC b y Δ))
resC-sc b y Δ m with mmcTy b
... | just A  rewrite sc-trTy m (atoms b) (mctx b) A = tt
... | nothing = tt

sideC-stable : ∀ b y Δ σ → T (sideC b y Δ) → T (sideC b y (Δ [ σ ]tel))
sideC-stable b y Δ σ p rewrite isε-[] Δ σ = p

------------------------------------------------------------------------
-- The laws.

gcLaws : BinderLaws
gcLaws = record
  { side-stable = λ { (gform b) y Δ σ l p → side-stableG b y Δ σ l p
                    ; (mmc b)   y Δ σ _ p → sideC-stable b y Δ σ p }
  ; args-stable = λ { (gform b) y Δ σ l p → args-stableG b y Δ σ l p
                    ; (mmc (mmi k Φ t)) y Δ σ _ _ → sym (argsC-[] (mmi k Φ t) y Δ σ) }
  ; res-stable  = λ { (gform b) y Δ σ l p → res-stableG b y Δ σ l p
                    ; (mmc b)   y Δ σ _ _ → trans (resC-Δ b y (Δ [ σ ]tel) Δ) (sym (resC-[] b y Δ σ)) }
  ; res-sc      = λ { (gform b) y Δ m p q → res-scG b y Δ m p q
                    ; (mmc b)   y Δ m _ _ → resC-sc b y Δ m }
  }
