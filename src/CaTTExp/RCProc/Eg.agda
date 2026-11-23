------------------------------------------------------------------------
-- The whiskered-generator cell e_g (ledger S20 (i), stage 3c;
-- notes/relative-coherence.md §2 Step 3).
--
-- For a whiskered generator g = (λ, x, ρ), with a ⇝λ v, x : s ⇒ t,
-- s t : v → w and w ⇝ρ b, the cell
--
--   e_g = κ(B_src, c⁻[θ_g]) ∗₁ H_g[θ_g] ∗₁ κ(c⁺[θ_g], B_tgt)
--       : B Γ a (λ ++ P⁻ ++ ρ) ⇒ B Γ a (λ ++ P⁺ ++ ρ)    (path s ≡ P⁻, path t ≡ P⁺)
--
-- where H_g is the column coherence (RCProc.Whisker), θ_g its
-- substitution (RCProc.Walk), and the κ's are the 1-dimensional
-- chain fillers (GraphFillerTotal.total), which apply because both
-- sides have the same path (RCProc.EgPath). `eg` is the term, computed
-- from the data alone; `eg-wf` types it, and `eg-κ₁-wf`, `eg-H-wf`,
-- `eg-κ₂-wf` type its three factors.
------------------------------------------------------------------------
module CaTTExp.RCProc.Eg where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (tm-ty)
open import CaTTExp.DerivedBoundary using (rwT)
open import CaTTExp.GraphFillerTotal using (path; pathCh; ∣_∣; Walk; walk; walk-++; wsub; fill₁; total)
open import CaTTExp.GraphFillerTotal.Chains using (vtx)
open import CaTTExp.PsRaiseCongr using (c⁻; c⁺; A^)
open import CaTTExp.RCProc.Glue using (Ans; transA)
open import CaTTExp.RCProc.Path1 using (B; B-wf)
open import CaTTExp.RCProc.Column using (leaves; flagAt; colEnd)
open import CaTTExp.RCProc.Edges using (pathCh-wgo)
open import CaTTExp.RCProc.Walk using (θg; θg-wf; θg-0; θg-end; θg-λ; θg-s; θg-t; θg-ρ)
open import CaTTExp.RCProc.EgPath using (path-c⁻; path-c⁺)
import CaTTExp.RCProc.Whisker as W

-- The path of the composite of a walk is the walk.
path-B : ∀ Γ a p → path (B Γ a p) ≡ p
path-B Γ a p = pathCh-wgo Γ (⟨⟩ ,ₛ var a) a p

-- Vertical composite of two 2-cells over A, as a term (Glue.transA).
vcomp : Ty → Tm → Tm → Tm → Tm → Tm → Tm
vcomp A t s u c h = rwT (dim A) 0 c (arr A t s) u h

------------------------------------------------------------------------
-- The term.

module EgTm (Γ : Ctx) (a : Nat) (λ′ : List Nat) (w : Nat) (s t : Tm) (x : Nat) (ρ : List Nat) (b : Nat)
            (Ps Pt : List Nat) where
  m n : Nat
  m = ∣ λ′ ∣
  n = ∣ ρ ∣

  θ : Sub
  θ = θg Γ a λ′ w s t x ρ

  A : Ty
  A = arr ⋆ (var a) (var b)

  private
    N = suc (m + n)
    cm cp : Tm
    cm = c⁻ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)) [ θ ]tm
    cp = c⁺ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx N)) [ θ ]tm

  c⁻θ c⁺θ : Tm
  c⁻θ = cm
  c⁺θ = cp

  Bs Bt : Tm
  Bs = B Γ a (λ′ ++ (Ps ++ ρ))
  Bt = B Γ a (λ′ ++ (Pt ++ ρ))

  κ₁ κ₂ Hθ : Tm
  κ₁ = fill₁ Γ Bs c⁻θ A
  κ₂ = fill₁ Γ c⁺θ Bt A
  Hθ = W.Col.H m n θ

  eg : Tm
  eg = vcomp A Bs c⁻θ Bt κ₁ (vcomp A c⁻θ c⁺θ Bt Hθ κ₂)

open EgTm using (eg) public

------------------------------------------------------------------------
-- Its typing.

module _ {Γ a λ′ v w s t x ρ b}
         (da : Γ ⊢tm var a ∶ ⋆) (wλ : Walk Γ a λ′ v)
         (dx : Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t) (wρ : Walk Γ w ρ b)
         {Ps Pt} (ps : path s ≡ Ps) (pt : path t ≡ Pt) where
  open EgTm Γ a λ′ w s t x ρ b Ps Pt hiding (eg)
  open W.Col m n using (H-wf; A^-eq)

  private
    sθ = θg-wf da wλ dx wρ

    tyH : A^ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n)))) [ θ ]ty ≡ A
    tyH = trans (cong (_[ θ ]ty) A^-eq)
                (cong₂ (arr ⋆) (θg-0 da wλ dx wρ) (θg-end da wλ dx wρ))

    dH : Γ ⊢tm Hθ ∶ arr A c⁻θ c⁺θ
    dH = subst (λ X → Γ ⊢tm Hθ ∶ arr X c⁻θ c⁺θ) tyH (H-wf sθ)

    sides : Σ (Γ ⊢tm c⁻θ ∶ A) λ _ → Γ ⊢tm c⁺θ ∶ A
    sides with tm-ty dH
    ... | arr-wf d⁻ d⁺ = d⁻ , d⁺

    tys : Σ (Γ ⊢tm s ∶ arr ⋆ (var v) (var w)) λ _ → Γ ⊢tm t ∶ arr ⋆ (var v) (var w)
    tys with tm-ty dx
    ... | arr-wf ds dt = ds , dt

    dBs : Γ ⊢tm Bs ∶ A
    dBs = B-wf da (walk-++ wλ (walk-++ (subst (λ q → Walk Γ v q w) ps (walk s (fst tys) refl)) wρ))

    dBt : Γ ⊢tm Bt ∶ A
    dBt = B-wf da (walk-++ wλ (walk-++ (subst (λ q → Walk Γ v q w) pt (walk t (snd tys) refl)) wρ))

    pe₁ : path Bs ≡ path c⁻θ
    pe₁ = trans (path-B Γ a _)
            (sym (trans (path-c⁻ m n ⋆ (var 0) (var (vtx (suc (m + n)))) θ)
                        (cong₂ _++_ (θg-λ da wλ dx wρ)
                                    (cong₂ _++_ (trans (cong path (θg-s da wλ dx wρ)) ps) (θg-ρ da wλ dx wρ)))))

    pe₂ : path c⁺θ ≡ path Bt
    pe₂ = trans (trans (path-c⁺ m n ⋆ (var 0) (var (vtx (suc (m + n)))) θ)
                       (cong₂ _++_ (θg-λ da wλ dx wρ)
                                   (cong₂ _++_ (trans (cong path (θg-t da wλ dx wρ)) pt) (θg-ρ da wλ dx wρ))))
                (sym (path-B Γ a _))

    k₁ : Ans Γ A Bs c⁻θ
    k₁ = κ₁ , total dBs (fst sides) pe₁

    k₂ : Ans Γ A c⁺θ Bt
    k₂ = κ₂ , total (snd sides) dBt pe₂

  eg-wf : Γ ⊢tm eg Γ a λ′ w s t x ρ b Ps Pt ∶ arr A Bs Bt
  eg-wf = snd (transA k₁ (transA (Hθ , dH) k₂))

  -- Its three factors, typed.
  eg-κ₁-wf : Γ ⊢tm κ₁ ∶ arr A Bs c⁻θ
  eg-κ₁-wf = snd k₁

  eg-H-wf : Γ ⊢tm Hθ ∶ arr A c⁻θ c⁺θ
  eg-H-wf = dH

  eg-κ₂-wf : Γ ⊢tm κ₂ ∶ arr A c⁺θ Bt
  eg-κ₂-wf = snd k₂
