------------------------------------------------------------------------
-- The support invariant in the free model (ledger item A3a, general
-- case).
--
-- Over a pasting context Θ, at the generic environment η Θ of the free
-- model 𝒯 (CaTTExp.Strict.GenericEnv), every derivable t : A denotes a
-- well-typed tree whose labels are exactly Var(t : A), the variables of
-- t and of A (`supp`). This is invariant (15) of the outside answer
-- (notes/conjectures/answered/strict-omega-pasting-formal-2026-11-18.md).
-- The coh case uses that the labels of a composite are the labels of
-- its pieces (CaTTExp.Strict.FreeTV.cp-flat) and that a substituted type
-- only mentions variables of the substitution.
------------------------------------------------------------------------
open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Typing
import CaTTExp.Subst

module CaTTExp.Strict.Support
  (𝕊 : Signature) (closed : CaTTExp.Subst.Closed 𝕊 (CaTTExp.Typing.cattSide 𝕊))
  where

open Signature 𝕊
open import CaTTExp.Typing 𝕊
open import CaTTExp.Strict.Trees
open import CaTTExp.Strict.PsTree 𝕊 using (tr)
open import CaTTExp.Strict.LabelSets
open import CaTTExp.Strict.PsFacts 𝕊 using (ArrOrd; PsCtx; ps-facts; ord; shape; <→≢)
open import CaTTExp.Strict.GenericEnv 𝕊
open import CaTTExp.Strict.FreeTV 𝕊
open import CaTTExp.Strict.TrFlat 𝕊 using (flat-tr; upTo)
open import CaTTExp.Strict.Dim 𝕊 closed using (fvSub-at)
import CaTTExp.Strict.OmegaEval 𝕊 𝒯 M𝒯 as E
import CaTTExp.Subst 𝕊 cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)

------------------------------------------------------------------------
-- Free variables under substitution.

mutual
  fvTm-[] : ∀ t σ → ScTm (lenₛ σ) t → fvTm (t [ σ ]tm) ⊆ fvSub σ
  fvTm-[] (var i)     σ p = sub λ v m → fvSub-at σ i v p m
  fvTm-[] (coh Δ A τ) σ p = fvSub-∘ τ σ p
  fvTm-[] (cst k)     σ p = ⊆-[]

  fvSub-∘ : ∀ τ σ → ScSub (lenₛ σ) τ → fvSub (τ ∘ σ) ⊆ fvSub σ
  fvSub-∘ ⟨⟩       σ _       = ⊆-[]
  fvSub-∘ (τ ,ₛ t) σ (p , q) = ⊆-++ (fvSub-∘ τ σ p) (fvTm-[] t σ q)

fvTy-[] : ∀ A σ → ScTy (lenₛ σ) A → fvTy (A [ σ ]ty) ⊆ fvSub σ
fvTy-[] ⋆           σ _           = ⊆-[]
fvTy-[] (arr A t u) σ (p , q , r) = ⊆-++ (fvTy-[] A σ p) (⊆-++ (fvTm-[] t σ q) (fvTm-[] u σ r))

------------------------------------------------------------------------
-- Labels of an environment.

envFlat : E.Env → List Nat
envFlat E.[]ₑ      = []
envFlat (τ E.,ₑ X) = envFlat τ ++ flat X

AllE : (LT Nat → Set) → E.Env → Set
AllE Pr E.[]ₑ      = ⊤
AllE Pr (τ E.,ₑ X) = AllE Pr τ × Pr X

allE-lkd : ∀ {Pr : LT Nat → Set} τ d → AllE Pr τ → Pr d → ∀ w → Pr (E.lkd τ d w)
allE-lkd E.[]ₑ      d _       pd w = pd
allE-lkd (τ E.,ₑ X) d (a , p) pd w with w ==ℕ E.lenₑ τ
... | true  = p
... | false = allE-lkd τ d a pd w

private
  ==-r : ∀ n → (n ==ℕ n) ≡ true
  ==-r zero    = refl
  ==-r (suc n) = ==-r n

mutual
  cmap-map : ∀ {B : Set} (g : B → LT Nat) T → cmap flat (flat (mapLT g T)) ≡ cmap (λ w → flat (g w)) (flat T)
  cmap-map g (node x r) = cong (flat (g x) ++_) (cmapB-map g r)

  cmapB-map : ∀ {B : Set} (g : B → LT Nat) r → cmap flat (flatB (mapB g r)) ≡ cmap (λ w → flat (g w)) (flatB r)
  cmapB-map g nil          = refl
  cmapB-map g (cons T y r) =
    cong (flat (g y) ++_)
      (trans (cmap-++ flat (flat (mapLT g T)) (flatB (mapB g r)))
        (trans (cong₂ _++_ (cmap-map g T) (cmapB-map g r))
               (sym (cmap-++ (λ w → flat (g w)) (flat T) (flatB r)))))

private
  lt-ne : ∀ m n → T (m <ℕ n) → (m ==ℕ n) ≡ false
  lt-ne zero    (suc n) _ = refl
  lt-ne (suc m) (suc n) p = lt-ne m n p

  n<s : ∀ n → T (n <ℕ suc n)
  n<s zero    = tt
  n<s (suc n) = n<s n

  lt-s : ∀ m n → T (suc m <ℕ suc n) → T (m <ℕ suc n)
  lt-s zero    n       _ = tt
  lt-s (suc m) (suc n) p = lt-s m n p

cmap-upTo-wk : ∀ τ X d m → T (m <ℕ suc (E.lenₑ τ)) →
               cmap (λ w → flat (E.lkd (τ E.,ₑ X) d w)) (upTo m) ≡ cmap (λ w → flat (E.lkd τ d w)) (upTo m)
cmap-upTo-wk τ X d zero    _ = refl
cmap-upTo-wk τ X d (suc m) p
  rewrite cmap-++ (λ w → flat (E.lkd (τ E.,ₑ X) d w)) (upTo m) (m ∷ [])
        | cmap-++ (λ w → flat (E.lkd τ d w)) (upTo m) (m ∷ [])
        | lt-ne m (E.lenₑ τ) p
        | cmap-upTo-wk τ X d m (lt-s m (E.lenₑ τ) p) = refl

cmap-env : ∀ τ d → cmap (λ w → flat (E.lkd τ d w)) (upTo (E.lenₑ τ)) ≡ envFlat τ
cmap-env E.[]ₑ      d = refl
cmap-env (τ E.,ₑ X) d
  rewrite cmap-++ (λ w → flat (E.lkd (τ E.,ₑ X) d w)) (upTo (E.lenₑ τ)) (E.lenₑ τ ∷ [])
        | ==-r (E.lenₑ τ)
        | cmap-upTo-wk τ X d (E.lenₑ τ) (n<s (E.lenₑ τ))
        | cmap-env τ d
        | ++-[] (flat X) = refl

------------------------------------------------------------------------
-- The invariant.

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

module _ {Θ z} (dΘ : Θ ⊢ps z ∶ ⋆) where
  private
    o  = ord (ps-facts dΘ)
    sh = shape (ps-facts dΘ)

  -- fvTmTy t A ⊆-absorbs the type.
  mutual
    supp : ∀ {t A X} → Θ ⊢tm t ∶ A → E.Ev (η Θ) t X → TV Θ o ⋆ X × (flat X ≈ fvTmTy t A)
    supp (var-wf {i} {A} w eq) (E.ev-var p) with just-inj (trans (sym p) (lookE-η Θ i eq))
    ... | refl = tv-discT Θ o A (node i nil) (sh i A eq) i eq (eq , tt) , flat-disc i A (sh i A eq)
    supp (coh-wf {Δ} {B} {s} {u} {σ} (ps dΔ) wΔ bB side sσ) (E.ev-coh {ρ′ = τ} {X = X₀} es cpX) =
      let (allτ , fτ , gτ) = supp-sub sσ wΔ es
          lσ = snd (Sb.sub-sc closed sσ)
          lτ : E.lenₑ (τ E.,ₑ X₀) ≡ len Δ
          lτ = trans (E.lenₑ-EvS es) lσ
          g = E.lkd (τ E.,ₑ X₀) X₀
          eqL : cmap flat (flat (mapLT g (tr Δ))) ≡ envFlat (τ E.,ₑ X₀)
          eqL = trans (cmap-map g (tr Δ))
                  (trans (cong (cmap (λ w → flat (g w))) (trans (flat-tr dΔ) (cong upTo (sym lτ))))
                         (cmap-env (τ E.,ₑ X₀) X₀))
          (f₁ , g₁) = cp-flat cpX
          scA : ScTy (lenₛ σ) (arr B s u)
          scA = subst (λ n → ScTy n (arr B s u)) (sym lσ) (Sb.ty-sc closed bB)
      in cp-tv Θ o cpX (allL-map Θ o (TV Θ o ⋆) g (allE-lkd (τ E.,ₑ X₀) X₀ allτ (snd allτ)) (tr Δ)) ,
         ( ⊆-trans f₁ (⊆-trans (subst (λ L → L ⊆ envFlat (τ E.,ₑ X₀)) (sym eqL) ⊆-refl)
                               (⊆-trans fτ (⊆-l (fvSub σ) (fvTy (arr B s u [ σ ]ty)))))
         , ⊆-++ (⊆-trans gτ (⊆-trans (subst (λ L → envFlat (τ E.,ₑ X₀) ⊆ L) (sym eqL) ⊆-refl) g₁))
                (⊆-trans (fvTy-[] (arr B s u) σ scA)
                         (⊆-trans gτ (⊆-trans (subst (λ L → envFlat (τ E.,ₑ X₀) ⊆ L) (sym eqL) ⊆-refl) g₁))) )
    supp (cst-wf _ _) (E.ev-cst ())

    supp-sub : ∀ {σ Δ τ} → Θ ⊢sub σ ∶ Δ → Δ ⊢ctx → E.EvS (η Θ) σ τ →
               AllE (TV Θ o ⋆) τ × (envFlat τ ⊆ fvSub σ) × (fvSub σ ⊆ envFlat τ)
    supp-sub (⟨⟩-wf _) _ E.evs-nil = tt , ⊆-[] , ⊆-[]
    supp-sub (,-wf {σ} {Δ} {t} {A} sσ dt) (▸-wf wΔ bA) (E.evs-cons {ρ′ = τ} {c = X} es e) =
      let (a , f , g) = supp-sub sσ wΔ es
          (tX , fX , gX) = supp dt e
          lσ = snd (Sb.sub-sc closed sσ)
          scA : ScTy (lenₛ σ) A
          scA = subst (λ n → ScTy n A) (sym lσ) (Sb.ty-sc closed bA)
      in (a , tX) ,
         ⊆-++ (inl⊆ (fvTm t) f)
              (⊆-trans fX (⊆-++ (inr⊆ (fvSub σ) ⊆-refl) (inl⊆ (fvTm t) (fvTy-[] A σ scA)))) ,
         ⊆-++ (inl⊆ (flat X) g) (inr⊆ (envFlat τ) (⊆-trans (⊆-l (fvTm t) (fvTy (A [ σ ]ty))) gX))
