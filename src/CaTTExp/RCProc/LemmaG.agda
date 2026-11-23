------------------------------------------------------------------------
-- Lemma G, kind (ii), step (4): the comparison coherence of
-- RCProc.LemmaGCoh, substituted along θ_g (ledger S20 (i), 3d;
-- notes/relative-coherence.md §2, Lemma G).
--
-- Data, in any context Γ: a prefix chain τ′ : chainC m′ from a to v,
-- x : s ⇒ t with s t : v → w, a suffix chain τs : chainC n′ from w to
-- b. Put θ′ = colSub τ′ w s t x τs (the column substitution of the
-- 2-term W = H_{m′,n′}[θ′]), λ′ = pathCh τ′, ρ′ = pathCh τs, m = ∣λ′∣,
-- n = ∣ρ′∣, θ = θ_g = θg Γ a λ′ w s t x ρ′ and A = a → b. Then
--
--   Q⇒ θ : W ⇛ κ̃⁻[θ] ∗₁ H_{m,n}[θ] ∗₁ κ̃⁺[θ]          (`lemmaG⇒`)
--   Q⇐ θ : κ̃⁻[θ] ∗₁ H_{m,n}[θ] ∗₁ κ̃⁺[θ] ⇛ W          (`lemmaG⇐`)
--
-- where H_{m,n}[θ] is EgTm's Hθ (the column coherence of e_g), its
-- boundaries are EgTm's c∓θ, and κ̃∓[θ] are chain fillers over Δ
-- substituted along θ: κ̃⁻[θ] : c⁻_{m′,n′}[θ′] ⇒ c⁻θ and
-- κ̃⁺[θ] : c⁺θ ⇒ c⁺_{m′,n′}[θ′].
------------------------------------------------------------------------
module CaTTExp.RCProc.LemmaG where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (idS; id-tm; sphSub)
open import CaTTExp.DerivedBoundary using (rwT; idS∘)
open import CaTTExp.PsRaise using (inclM; inclP; inclM-wf; inclP-wf)
open import CaTTExp.PsRaiseCongr using (c⁻; c⁺)
open import CaTTExp.GraphFillerTotal using (pathCh; ∣_∣; walkCh; Walk)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; vtx)
open import CaTTExp.RCProc.Column using (colCtx; flagAt; leaves)
open import CaTTExp.RCProc.ColSub using (colSub)
open import CaTTExp.RCProc.Walk using (θg; θg-wf; θg-0; θg-end)
open import CaTTExp.RCProc.Eg using (vcomp)
open import CaTTExp.RCProc.LemmaGSub using (factor)
open import CaTTExp.RCProc.LemmaGCoh using (module Cmp)
import CaTTExp.RCProc.Whisker as W

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  idS-incl : ∀ (ρ : Sub) n → lenₛ ρ ≡ n → idS n ∘ ρ ≡ ρ
  idS-incl ρ .(lenₛ ρ) refl = idS∘ ρ ρ (λ _ _ → refl)

  sph-sub : ∀ C θ → sphSub C ∘ θ ≡ sphSub (C [ θ ]ty)
  sph-sub ⋆           θ = refl
  sph-sub (arr C s t) θ = cong (λ X → X ,ₛ s [ θ ]tm ,ₛ t [ θ ]tm) (sph-sub C θ)

  rwT-sub : ∀ k j c C z h θ →
            rwT k j c C z h [ θ ]tm ≡ rwT k j (c [ θ ]tm) (C [ θ ]ty) (z [ θ ]tm) (h [ θ ]tm)
  rwT-sub k j c C z h θ =
    cong (λ X → coh _ _ (X ,ₛ c [ θ ]tm ,ₛ z [ θ ]tm ,ₛ h [ θ ]tm)) (sph-sub C θ)

-- The column boundaries c∓ are scoped in the column context.
module _ (m n : Nat) where
  private
    bs = flagAt m
    ts = leaves (m + n)
    N  = suc (m + n)
    nP = len (ctxOf (node (node [] ∷ ts)))
    lR : len (W.Col.R m n) ≡ len (colCtx m n)
    lR = cong len (W.Col.R≡ m n)

  c⁻-sc : S.ScTm (len (colCtx m n)) (c⁻ bs (node []) ts ⋆ (var 0) (var (vtx N)))
  c⁻-sc = subst (λ k → S.ScSub k (idS nP ∘ inclM bs (node []) ts)) lR
            (subst (S.ScSub (len (W.Col.R m n))) (sym (idS-incl (inclM bs (node []) ts) nP (snd sc))) (fst sc))
    where sc = S.sub-sc closed (inclM-wf bs (node []) ts)

  c⁺-sc : S.ScTm (len (colCtx m n)) (c⁺ bs (node []) ts ⋆ (var 0) (var (vtx N)))
  c⁺-sc = subst (λ k → S.ScSub k (idS nP ∘ inclP bs (node []) ts)) lR
            (subst (S.ScSub (len (W.Col.R m n))) (sym (idS-incl (inclP bs (node []) ts) nP (snd sc))) (fst sc))
    where sc = S.sub-sc closed (inclP-wf bs (node []) ts)

------------------------------------------------------------------------
-- Lemma G (ii).

module _ {Γ a v w s t x b m′ n′ τ′ τs}
         (da : Γ ⊢tm var a ∶ ⋆)
         (sτ′ : Γ ⊢sub τ′ ∶ chainC m′) (l0 : lookupₛ τ′ 0 ≡ var a) (lv : lookupₛ τ′ (vtx m′) ≡ var v)
         (dx : Γ ⊢tm var x ∶ arr (arr ⋆ (var v) (var w)) s t)
         (sτs : Γ ⊢sub τs ∶ chainC n′) (lw : lookupₛ τs 0 ≡ var w) (lb : lookupₛ τs (vtx n′) ≡ var b) where
  open Cmp sτ′ sτs public using (m; n; Δ; κ̃⁻; κ̃⁺; Q⇒; Q⇐)
  open Cmp sτ′ sτs using (ι; σς; A_Δ; c⁻′; c⁺′; c⁻₀; c⁺₀; X; H₀; Y; Bnd; Q⇒-wf; Q⇐-wf; dκ⁻; dκ⁺)

  private
    c⁻ᵐ c⁺ᵐ c⁻ᵍ c⁺ᵍ : Tm
    c⁻ᵐ = c⁻ (flagAt m′) (node []) (leaves (m′ + n′)) ⋆ (var 0) (var (vtx (suc (m′ + n′))))
    c⁺ᵐ = c⁺ (flagAt m′) (node []) (leaves (m′ + n′)) ⋆ (var 0) (var (vtx (suc (m′ + n′))))
    c⁻ᵍ = c⁻ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n))))
    c⁺ᵍ = c⁺ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n))))

  θ θ′ : Sub
  θ  = θg Γ a (pathCh τ′) w s t x (pathCh τs)
  θ′ = colSub τ′ w s t x τs

  A : Ty
  A = arr ⋆ (var a) (var b)

  c⁻θ′ c⁺θ′ c⁻θ c⁺θ Wθ′ Hθ Yθ : Tm
  c⁻θ′ = c⁻ᵐ [ θ′ ]tm
  c⁺θ′ = c⁺ᵐ [ θ′ ]tm
  c⁻θ  = c⁻ᵍ [ θ ]tm
  c⁺θ  = c⁺ᵍ [ θ ]tm
  Wθ′  = W.Col.H m′ n′ θ′
  Hθ   = W.Col.H m n θ
  Yθ   = vcomp A c⁻θ′ c⁻θ c⁺θ′ (κ̃⁻ [ θ ]tm) (vcomp A c⁻θ c⁺θ c⁺θ′ Hθ (κ̃⁺ [ θ ]tm))

  private
    wλ : Walk Γ a (pathCh τ′) v
    wλ = walkCh m′ τ′ sτ′ l0 lv
    wρ : Walk Γ w (pathCh τs) b
    wρ = walkCh n′ τs sτs lw lb

  θ-wf : Γ ⊢sub θ ∶ Δ
  θ-wf = θg-wf da wλ dx wρ

  private
    lθ : lenₛ θ ≡ len Δ
    lθ = snd (S.sub-sc closed θ-wf)

    lς : lenₛ σς ≡ len (colCtx m′ n′)
    lς = snd (S.sub-sc closed (ς-wf sτ′ sτs))
      where open import CaTTExp.RCProc.LemmaGSub using (ς-wf)

    fac : σς ∘ θ ≡ θ′
    fac = factor sτ′ l0 sτs lw

    eA : A_Δ [ θ ]ty ≡ A
    eA = cong₂ (arr ⋆) (θg-0 da wλ dx wρ) (θg-end da wλ dx wρ)

    e⁻′ : c⁻′ [ θ ]tm ≡ c⁻θ′
    e⁻′ = trans (S.assoc-tm c⁻ᵐ σς θ (subst (λ k → S.ScTm k c⁻ᵐ) (sym lς) (c⁻-sc m′ n′)))
                (cong (c⁻ᵐ [_]tm) fac)
    e⁺′ : c⁺′ [ θ ]tm ≡ c⁺θ′
    e⁺′ = trans (S.assoc-tm c⁺ᵐ σς θ (subst (λ k → S.ScTm k c⁺ᵐ) (sym lς) (c⁺-sc m′ n′)))
                (cong (c⁺ᵐ [_]tm) fac)

    e⁻₀ : c⁻₀ [ θ ]tm ≡ c⁻θ
    e⁻₀ = cong (_[ θ ]tm) (id-tm (len Δ) c⁻ᵍ (c⁻-sc m n))
    e⁺₀ : c⁺₀ [ θ ]tm ≡ c⁺θ
    e⁺₀ = cong (_[ θ ]tm) (id-tm (len Δ) c⁺ᵍ (c⁺-sc m n))

    eX : X [ θ ]tm ≡ Wθ′
    eX = cong (W.Col.H m′ n′) fac

    eH : H₀ [ θ ]tm ≡ Hθ
    eH = cong (W.Col.H m n) (idS-incl θ (len Δ) lθ)

    Y₂ : Tm
    Y₂ = vcomp A_Δ c⁻₀ c⁺₀ c⁺′ H₀ κ̃⁺

    eY₂ : Y₂ [ θ ]tm ≡ vcomp A c⁻θ c⁺θ c⁺θ′ Hθ (κ̃⁺ [ θ ]tm)
    eY₂ = trans (rwT-sub 1 0 H₀ (arr A_Δ c⁻₀ c⁺₀) c⁺′ κ̃⁺ θ)
                (cong₃ (λ c C z → rwT 1 0 c C z (κ̃⁺ [ θ ]tm)) eH (cong₃ arr eA e⁻₀ e⁺₀) e⁺′)

    eY : Y [ θ ]tm ≡ Yθ
    eY = trans (rwT-sub 1 0 κ̃⁻ (arr A_Δ c⁻′ c⁻₀) c⁺′ Y₂ θ)
               (cong₃ (λ C z h → rwT 1 0 (κ̃⁻ [ θ ]tm) C z h) (cong₃ arr eA e⁻′ e⁻₀) e⁺′ eY₂)

    eBnd : Bnd [ θ ]ty ≡ arr A c⁻θ′ c⁺θ′
    eBnd = cong₃ arr eA e⁻′ e⁺′

  -- The comparison, in both directions.
  lemmaG⇒ : Γ ⊢tm Q⇒ θ ∶ arr (arr A c⁻θ′ c⁺θ′) Wθ′ Yθ
  lemmaG⇒ = subst (Γ ⊢tm Q⇒ θ ∶_) (cong₃ arr eBnd eX eY) (Q⇒-wf θ-wf)

  lemmaG⇐ : Γ ⊢tm Q⇐ θ ∶ arr (arr A c⁻θ′ c⁺θ′) Yθ Wθ′
  lemmaG⇐ = subst (Γ ⊢tm Q⇐ θ ∶_) (cong₃ arr eBnd eY eX) (Q⇐-wf θ-wf)

  -- The two outer factors of Yθ.
  κ̃⁻-wf : Γ ⊢tm κ̃⁻ [ θ ]tm ∶ arr A c⁻θ′ c⁻θ
  κ̃⁻-wf = subst (Γ ⊢tm κ̃⁻ [ θ ]tm ∶_) (cong₃ arr eA e⁻′ e⁻₀) (S.tm[] closed dκ⁻ θ-wf)

  κ̃⁺-wf : Γ ⊢tm κ̃⁺ [ θ ]tm ∶ arr A c⁺θ c⁺θ′
  κ̃⁺-wf = subst (Γ ⊢tm κ̃⁺ [ θ ]tm ∶_) (cong₃ arr eA e⁺₀ e⁺′) (S.tm[] closed dκ⁺ θ-wf)
