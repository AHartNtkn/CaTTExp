------------------------------------------------------------------------
-- One whiskered generator, pulled back (ledger S20 (i), stage 3e,
-- Lemma E part (2); notes/relative-coherence.md §2).
--
-- Data: a context Δ with a whiskered generator (l, Z, r) of it, where
-- Z : f ⇒ f′ is a 2-variable whose boundaries are 1-variables, and a
-- substitution θ : Γ → Δ sending Z to a 2-variable α : s ⇒ t of Γ.
-- Put τ′ = wsub Δ a₀ l ∘ θ and τs = wsub Δ L r ∘ θ (the whiskers,
-- pulled back), and let
--
--   e = e_(l,Z,r)[θ]            : X⁻ ⇒ X⁺      (the Δ-cell, pulled back)
--   g = e_(pathCh τ′,α,pathCh τs) : B⁻ ⇒ B⁺      (the Γ-cell)
--
-- with X∓ the pulled-back boundaries of e and B∓ those of g. Both have
-- the same paths, so the chain fillers K⁻ : X⁻ ⇒ B⁻ and K⁺ : X⁺ ⇒ B⁺
-- exist, and the square commutes up to two-way 3-cells (`sq`):
--
--   K⁻ ∗ g  ⇄  e ∗ K⁺.
--
-- Proof. Pulling back the column coherence of e gives the 2-term W of
-- Lemma G (`fac`: θ_g ∘ θ is the column substitution colSub τ′ …
-- τs). Lemma G replaces W by κ̃⁻ ∗ H ∗ κ̃⁺, with H the column
-- coherence of g; what is left are composites of chain fillers with
-- equal boundaries, which cancel (Glue3.cancel), and reassociation.
------------------------------------------------------------------------
module CaTTExp.RCProc.ExchangeSq where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.PureMetatheory using (closed)
import CaTTExp.Subst ∅ cattSide as S
open import CaTTExp.Derived using (sphSub; tm-ty; tm-ctx)
open import CaTTExp.DerivedBoundary using (rwT)
open import CaTTExp.GraphFillerTotal using (path; pathCh; ∣_∣; Walk; wgo; wsub; wgo-ty; wgo-keep; walkCh; walk-end; fill₁; total)
open import CaTTExp.GraphFillerTotal.Chains using (chainC; chainC-wf; vtx; len-chain; +-zero; T→<; <→T; vtx-<; ≤-refl)
open import CaTTExp.PsRaiseCongr using (c⁻; c⁺)
open import CaTTExp.RCProc.Column using (flagAt; leaves; colCtx; e₀-vtx)
open import CaTTExp.RCProc.ColSub using (appCh; colSub; appCh-∘)
open import CaTTExp.RCProc.Walk using (θg; θg-wf; wgoF-end)
open import CaTTExp.RCProc.Path1 using (B)
open import CaTTExp.RCProc.Eg using (vcomp; eg; module EgTm; eg-κ₁-wf; eg-H-wf; eg-κ₂-wf; path-B)
import CaTTExp.RCProc.LemmaG as G
import CaTTExp.RCProc.LemmaGCoh as LC
module C = LC.Cmp
open import CaTTExp.RCProc.ExchangeSub using (wgo-app; pmap; pmap-++; pathCh-wgo∘)
open import CaTTExp.RCProc.Glue3 using (LowT; low-coh; low-vcomp; graph-chain)
open import CaTTExp.RCProc.Glue3Eqv
import CaTTExp.RCProc.Whisker as W

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

  sph-sub : ∀ C θ → sphSub C ∘ θ ≡ sphSub (C [ θ ]ty)
  sph-sub ⋆           θ = refl
  sph-sub (arr C s t) θ = cong (λ X → X ,ₛ s [ θ ]tm ,ₛ t [ θ ]tm) (sph-sub C θ)

  rwT-sub : ∀ k j c C z h θ →
            rwT k j c C z h [ θ ]tm ≡ rwT k j (c [ θ ]tm) (C [ θ ]ty) (z [ θ ]tm) (h [ θ ]tm)
  rwT-sub k j c C z h θ =
    cong (λ X → coh _ _ (X ,ₛ c [ θ ]tm ,ₛ z [ θ ]tm ,ₛ h [ θ ]tm)) (sph-sub C θ)

  len-sub : ∀ {Γ σ Δ} → Γ ⊢sub σ ∶ Δ → lenₛ σ ≡ len Δ
  len-sub s = snd (S.sub-sc closed s)

  -- Looking up a pulled-back chain substitution.
  lk∘ : ∀ {Δ τ k} θ i → Δ ⊢sub τ ∶ chainC k → T (i <ℕ vtx (suc k)) → lookupₛ (τ ∘ θ) i ≡ lookupₛ τ i [ θ ]tm
  lk∘ {τ = τ} {k} θ i sτ p = S.lookupₛ-∘ τ θ i (subst (λ N → T (i <ℕ N)) (sym (trans (len-sub sτ) (len-chain k))) p)

  -- The walk substitution of a walk, as a chain, and its two ends.
  module WS {Δ x p y} (dx : Δ ⊢tm var x ∶ ⋆) (wk : Walk Δ x p y) where
    sw : Δ ⊢sub wsub Δ x p ∶ chainC ∣ p ∣
    sw = subst (λ k → Δ ⊢sub wsub Δ x p ∶ chainC k) (+-zero ∣ p ∣) (wgo-ty (,-wf (⟨⟩-wf (tm-ctx dx)) dx) refl wk)

    l-0 : lookupₛ (wsub Δ x p) 0 ≡ var x
    l-0 = wgo-keep (⟨⟩ ,ₛ var x) x p 0 (T→< 0 1 tt)

    l-end : lookupₛ (wsub Δ x p) (vtx ∣ p ∣) ≡ var y
    l-end = subst (λ N → lookupₛ (wsub Δ x p) N ≡ var y) (e₀-vtx ∣ p ∣)
              (trans (wgoF-end Δ (ε ▸ ⋆) (⟨⟩ ,ₛ var x) 0 x p refl refl) (cong var (walk-end wk)))

------------------------------------------------------------------------

module Sq {Γ Δ θE a b a₀ b₀ v₀ v L w f f′ Z α s t l r Ps Pt}
          (d0 : Δ ⊢tm var a₀ ∶ ⋆) (wl : Walk Δ a₀ l v₀)
          (dZ : Δ ⊢tm var Z ∶ arr (arr ⋆ (var v₀) (var L)) (var f) (var f′)) (wr : Walk Δ L r b₀)
          (sθ : Γ ⊢sub θE ∶ Δ)
          (la : lookupₛ θE a₀ ≡ var a) (lb : lookupₛ θE b₀ ≡ var b) (lv : lookupₛ θE v₀ ≡ var v)
          (lL : lookupₛ θE L ≡ var w) (lf : lookupₛ θE f ≡ s) (lf′ : lookupₛ θE f′ ≡ t)
          (lZ : lookupₛ θE Z ≡ var α)
          (ps : path s ≡ Ps) (pt : path t ≡ Pt) where

  private
    dL : Δ ⊢tm var L ∶ ⋆
    dL with tm-ty dZ
    ... | arr-wf df _ with tm-ty df
    ...   | arr-wf _ d = d

    module Wl = WS d0 wl
    module Wr = WS dL wr

  -- The whiskers, pulled back.
  τ′ τs : Sub
  τ′ = wsub Δ a₀ l ∘ θE
  τs = wsub Δ L r ∘ θE

  m n : Nat
  m = ∣ l ∣
  n = ∣ r ∣

  sτ′ : Γ ⊢sub τ′ ∶ chainC m
  sτ′ = S.sub∘ closed (chainC-wf m) Wl.sw sθ

  sτs : Γ ⊢sub τs ∶ chainC n
  sτs = S.sub∘ closed (chainC-wf n) Wr.sw sθ

  l0 : lookupₛ τ′ 0 ≡ var a
  l0 = trans (lk∘ θE 0 Wl.sw tt) (trans (cong (_[ θE ]tm) Wl.l-0) la)

  lvτ : lookupₛ τ′ (vtx m) ≡ var v
  lvτ = trans (lk∘ θE (vtx m) Wl.sw (<→T {vtx m} {vtx (suc m)} (vtx-< {m} {m} ≤-refl))) (trans (cong (_[ θE ]tm) Wl.l-end) lv)

  lwτ : lookupₛ τs 0 ≡ var w
  lwτ = trans (lk∘ θE 0 Wr.sw tt) (trans (cong (_[ θE ]tm) Wr.l-0) lL)

  lbτ : lookupₛ τs (vtx n) ≡ var b
  lbτ = trans (lk∘ θE (vtx n) Wr.sw (<→T {vtx n} {vtx (suc n)} (vtx-< {n} {n} ≤-refl))) (trans (cong (_[ θE ]tm) Wr.l-end) lb)

  da : Γ ⊢tm var a ∶ ⋆
  da = subst (λ X → Γ ⊢tm X ∶ ⋆) la (S.tm[] closed d0 sθ)

  dx : Γ ⊢tm var α ∶ arr (arr ⋆ (var v) (var w)) s t
  dx = subst (λ X → Γ ⊢tm X ∶ arr (arr ⋆ (var v) (var w)) s t) lZ
         (subst (λ T′ → Γ ⊢tm lookupₛ θE Z ∶ T′)
                (cong₃ arr (cong₂ (arr ⋆) lv lL) lf lf′) (S.tm[] closed dZ sθ))

  ----------------------------------------------------------------------
  -- The Γ-cell and the Δ-cell.

  lΓ rΓ : List Nat
  lΓ = pathCh τ′
  rΓ = pathCh τs

  module EΓ = EgTm Γ a lΓ w s t α rΓ b Ps Pt
  module EΔ = EgTm Δ a₀ l L (var f) (var f′) Z r b₀ (f ∷ []) (f′ ∷ [])

  A : Ty
  A = arr ⋆ (var a) (var b)

  g e : Tm
  g = eg Γ a lΓ w s t α rΓ b Ps Pt
  e = eg Δ a₀ l L (var f) (var f′) Z r b₀ (f ∷ []) (f′ ∷ []) [ θE ]tm

  -- The pieces of Lemma G.
  θΓ θ′ : Sub
  θΓ = θg Γ a lΓ w s t α rΓ
  θ′ = colSub τ′ w s t α τs

  private
    wλΓ : Walk Γ a lΓ v
    wλΓ = walkCh m τ′ sτ′ l0 lvτ
    wρΓ : Walk Γ w rΓ b
    wρΓ = walkCh n τs sτs lwτ lbτ

    θΔ : Sub
    θΔ = θg Δ a₀ l L (var f) (var f′) Z r

    σ₅ : Sub
    σ₅ = wsub Δ a₀ l ,ₛ var L ,ₛ var f ,ₛ var f′ ,ₛ var Z

  fac : θΔ ∘ θE ≡ θ′
  fac = trans (cong (_∘ θE) (wgo-app Δ σ₅ L r))
          (trans (appCh-∘ σ₅ (wsub Δ L r) θE)
                 (cong (λ X → appCh X τs)
                       (cong₂ (λ X Y → X ,ₛ Y) (cong₃ (λ X Y U → τ′ ,ₛ X ,ₛ Y ,ₛ U) lL lf lf′) lZ)))

  private
    c⁻ᵐ c⁺ᵐ : Tm
    c⁻ᵐ = c⁻ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n))))
    c⁺ᵐ = c⁺ (flagAt m) (node []) (leaves (m + n)) ⋆ (var 0) (var (vtx (suc (m + n))))

    lθΔ : lenₛ θΔ ≡ len (colCtx m n)
    lθΔ = len-sub (θg-wf d0 wl dZ wr)

  c⁻′ c⁺′ W′ : Tm
  c⁻′ = c⁻ᵐ [ θ′ ]tm
  c⁺′ = c⁺ᵐ [ θ′ ]tm
  W′  = W.Col.H m n θ′

  private
    eA : EΔ.A [ θE ]ty ≡ A
    eA = cong₂ (arr ⋆) la lb

    e⁻ : EΔ.c⁻θ [ θE ]tm ≡ c⁻′
    e⁻ = trans (S.assoc-tm c⁻ᵐ θΔ θE (subst (λ k → S.ScTm k c⁻ᵐ) (sym lθΔ) (G.c⁻-sc m n)))
               (cong (c⁻ᵐ [_]tm) fac)

    e⁺ : EΔ.c⁺θ [ θE ]tm ≡ c⁺′
    e⁺ = trans (S.assoc-tm c⁺ᵐ θΔ θE (subst (λ k → S.ScTm k c⁺ᵐ) (sym lθΔ) (G.c⁺-sc m n)))
               (cong (c⁺ᵐ [_]tm) fac)

    eH : EΔ.Hθ [ θE ]tm ≡ W′
    eH = cong (W.Col.H m n) fac

  X⁻ X⁺ e₁ e₂ : Tm
  X⁻ = EΔ.Bs [ θE ]tm
  X⁺ = EΔ.Bt [ θE ]tm
  e₁ = EΔ.κ₁ [ θE ]tm
  e₂ = EΔ.κ₂ [ θE ]tm

  -- e, unfolded.
  e-eq : e ≡ vcomp A X⁻ c⁻′ X⁺ e₁ (vcomp A c⁻′ c⁺′ X⁺ W′ e₂)
  e-eq =
    trans (rwT-sub 1 0 EΔ.κ₁ (arr EΔ.A EΔ.Bs EΔ.c⁻θ) EΔ.Bt Y₂ θE)
          (cong₂ (λ C U → rwT 1 0 e₁ C X⁺ U) (cong₃ arr eA refl e⁻)
                 (trans (rwT-sub 1 0 EΔ.Hθ (arr EΔ.A EΔ.c⁻θ EΔ.c⁺θ) EΔ.Bt EΔ.κ₂ θE)
                        (cong₂ (λ c C → rwT 1 0 c C X⁺ e₂) eH (cong₃ arr eA e⁻ e⁺))))
    where Y₂ = vcomp EΔ.A EΔ.c⁻θ EΔ.c⁺θ EΔ.Bt EΔ.Hθ EΔ.κ₂
  ----------------------------------------------------------------------
  -- Typings.

  private
    sub-ty : ∀ {u T′ T″} → Δ ⊢tm u ∶ T′ → T′ [ θE ]ty ≡ T″ → Γ ⊢tm u [ θE ]tm ∶ T″
    sub-ty du q = subst (λ X → Γ ⊢tm _ ∶ X) q (S.tm[] closed du sθ)

    de₁ : Γ ⊢tm e₁ ∶ arr A X⁻ c⁻′
    de₁ = sub-ty (eg-κ₁-wf d0 wl dZ wr refl refl) (cong₃ arr eA refl e⁻)

    dW : Γ ⊢tm W′ ∶ arr A c⁻′ c⁺′
    dW = subst (λ X → Γ ⊢tm X ∶ arr A c⁻′ c⁺′) eH
           (sub-ty (eg-H-wf d0 wl dZ wr refl refl) (cong₃ arr eA e⁻ e⁺))

    de₂ : Γ ⊢tm e₂ ∶ arr A c⁺′ X⁺
    de₂ = sub-ty (eg-κ₂-wf d0 wl dZ wr refl refl) (cong₃ arr eA e⁺ refl)

    dk₁ : Γ ⊢tm EΓ.κ₁ ∶ arr A EΓ.Bs EΓ.c⁻θ
    dk₁ = eg-κ₁-wf da wλΓ dx wρΓ ps pt
    dH : Γ ⊢tm EΓ.Hθ ∶ arr A EΓ.c⁻θ EΓ.c⁺θ
    dH = eg-H-wf da wλΓ dx wρΓ ps pt
    dk₂ : Γ ⊢tm EΓ.κ₂ ∶ arr A EΓ.c⁺θ EΓ.Bt
    dk₂ = eg-κ₂-wf da wλΓ dx wρΓ ps pt

    sides : ∀ {T′ u u′ h} → Γ ⊢tm h ∶ arr T′ u u′ → (Γ ⊢tm u ∶ T′) × (Γ ⊢tm u′ ∶ T′)
    sides dh with tm-ty dh
    ... | arr-wf du du′ = du , du′

  ----------------------------------------------------------------------
  -- The fillers K∓.

  K⁻ K⁺ : Tm
  K⁻ = fill₁ Γ X⁻ EΓ.Bs A
  K⁺ = fill₁ Γ X⁺ EΓ.Bt A

  private
    eλ : lΓ ≡ pmap θE l
    eλ = pathCh-wgo∘ Δ (⟨⟩ ,ₛ var a₀) a₀ l θE

    eρ : rΓ ≡ pmap θE r
    eρ = pathCh-wgo∘ Δ (⟨⟩ ,ₛ var L) L r θE

    pX : ∀ u → path (B Δ a₀ (l ++ ((u ∷ []) ++ r)) [ θE ]tm) ≡ lΓ ++ (path (lookupₛ θE u) ++ rΓ)
    pX u = trans (pathCh-wgo∘ Δ (⟨⟩ ,ₛ var a₀) a₀ (l ++ ((u ∷ []) ++ r)) θE)
             (trans (pmap-++ θE l (u ∷ r))
                    (cong₂ (λ X Y → X ++ (path (lookupₛ θE u) ++ Y)) (sym eλ) (sym eρ)))

    pK⁻ : path X⁻ ≡ path EΓ.Bs
    pK⁻ = trans (pX f) (trans (cong (λ X → lΓ ++ (X ++ rΓ)) (trans (cong path lf) ps)) (sym (path-B Γ a _)))

    pK⁺ : path X⁺ ≡ path EΓ.Bt
    pK⁺ = trans (pX f′) (trans (cong (λ X → lΓ ++ (X ++ rΓ)) (trans (cong path lf′) pt)) (sym (path-B Γ a _)))

    dX⁻ = fst (sides de₁)
    dX⁺ = snd (sides de₂)
    dBs = fst (sides dk₁)
    dBt = snd (sides dk₂)

    dK⁻ : Γ ⊢tm K⁻ ∶ arr A X⁻ EΓ.Bs
    dK⁻ = total dX⁻ dBs pK⁻

    dK⁺ : Γ ⊢tm K⁺ ∶ arr A X⁺ EΓ.Bt
    dK⁺ = total dX⁺ dBt pK⁺

  ----------------------------------------------------------------------
  -- Lemma G at this generator.

  m₁ m₂ Y : Tm
  m₁ = G.κ̃⁻ da sτ′ l0 lvτ dx sτs lwτ lbτ [ θΓ ]tm
  m₂ = G.κ̃⁺ da sτ′ l0 lvτ dx sτs lwτ lbτ [ θΓ ]tm
  Y  = vcomp A c⁻′ EΓ.c⁻θ c⁺′ m₁ (vcomp A EΓ.c⁻θ EΓ.c⁺θ c⁺′ EΓ.Hθ m₂)

  private
    dm₁ : Γ ⊢tm m₁ ∶ arr A c⁻′ EΓ.c⁻θ
    dm₁ = G.κ̃⁻-wf da sτ′ l0 lvτ dx sτs lwτ lbτ
    dm₂ : Γ ⊢tm m₂ ∶ arr A EΓ.c⁺θ c⁺′
    dm₂ = G.κ̃⁺-wf da sτ′ l0 lvτ dx sτs lwτ lbτ

  lemG : Eqv Γ (arr A c⁻′ c⁺′) W′ Y
  lemG = (G.Q⇒ da sτ′ l0 lvτ dx sτs lwτ lbτ θΓ , G.lemmaG⇒ da sτ′ l0 lvτ dx sτs lwτ lbτ) ,
         (G.Q⇐ da sτ′ l0 lvτ dx sτs lwτ lbτ θΓ , G.lemmaG⇐ da sτ′ l0 lvτ dx sτs lwτ lbτ)

  ----------------------------------------------------------------------
  -- The square.

  private
    Bs = EΓ.Bs
    Bt = EΓ.Bt
    c⁻g = EΓ.c⁻θ
    c⁺g = EΓ.c⁺θ
    k₁ = EΓ.κ₁
    k₂ = EΓ.κ₂
    H  = EΓ.Hθ

    vc : Tm → Tm → Tm → Tm → Tm → Tm
    vc = vcomp A

    lK⁻ = low-coh dK⁻ (graph-chain ∣ path X⁻ ∣)
    lK⁺ = low-coh dK⁺ (graph-chain ∣ path X⁺ ∣)
    lk₁ = low-coh dk₁ (graph-chain ∣ path Bs ∣)
    lk₂ = low-coh dk₂ (graph-chain ∣ path c⁺g ∣)
    le₁ = low-coh de₁ (graph-chain ∣ path EΔ.Bs ∣)
    le₂ = low-coh de₂ (graph-chain ∣ path EΔ.c⁺θ ∣)
    lm₁ = low-coh dm₁ (graph-chain ∣ path (C.c⁻′ sτ′ sτs) ∣)
    lm₂ = low-coh dm₂ (graph-chain ∣ path (C.c⁺₀ sτ′ sτs) ∣)

    Hk₂ = vc c⁻g c⁺g Bt H k₂
    dHk₂ = vc-wf dH dk₂
    e₂K = vc c⁺′ X⁺ Bt e₂ K⁺
    de₂K = vc-wf de₂ dK⁺
    We₂ = vc c⁻′ c⁺′ X⁺ W′ e₂
    dWe₂ = vc-wf dW de₂
    Hm₂ = vc c⁻g c⁺g c⁺′ H m₂
    dHm₂ = vc-wf dH dm₂

    MID : Tm
    MID = vc X⁻ c⁻′ Bt e₁ (vc c⁻′ c⁻g Bt m₁ Hk₂)

    left : Eqv Γ (arr A X⁻ Bt) (vc X⁻ Bs Bt K⁻ g) MID
    left =
      symE (assocE dK⁻ dk₁ dHk₂) ⊙
      congLE dHk₂ (cancelE (vc-wf dK⁻ dk₁) (vc-wf de₁ dm₁) (low-vcomp dK⁻ dk₁ lK⁻ lk₁) (low-vcomp de₁ dm₁ le₁ lm₁)) ⊙
      assocE de₁ dm₁ dHk₂

    right : Eqv Γ (arr A X⁻ Bt) (vc X⁻ X⁺ Bt (vc X⁻ c⁻′ X⁺ e₁ We₂) K⁺) MID
    right =
      assocE de₁ dWe₂ dK⁺ ⊙
      congRE de₁ (assocE dW de₂ dK⁺) ⊙
      congRE de₁ (congLE de₂K lemG) ⊙
      congRE de₁ (assocE dm₁ dHm₂ de₂K) ⊙
      congRE de₁ (congRE dm₁ (assocE dH dm₂ de₂K)) ⊙
      congRE de₁ (congRE dm₁ (congRE dH
        (cancelE (vc-wf dm₂ de₂K) dk₂ (low-vcomp dm₂ de₂K lm₂ (low-vcomp de₂ dK⁺ le₂ lK⁺)) lk₂)))

  sq : Eqv Γ (arr A X⁻ EΓ.Bt) (vcomp A X⁻ EΓ.Bs EΓ.Bt K⁻ g) (vcomp A X⁻ X⁺ EΓ.Bt e K⁺)
  sq = substE refl (cong (λ E′ → vc X⁻ X⁺ Bt E′ K⁺) (sym e-eq)) (left ⊙ symE right)
