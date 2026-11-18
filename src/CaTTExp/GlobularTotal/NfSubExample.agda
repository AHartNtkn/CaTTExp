------------------------------------------------------------------------
-- A concrete inhabitant of NfSub.Hyp, so nf-sub's hypothesis is not
-- vacuous: the composite g ∘ f in the context x →f y →g z, substituted
-- by the identity.
------------------------------------------------------------------------
module CaTTExp.GlobularTotal.NfSubExample where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GlobularFiller using (LT; lt; bd; bdL; nf)
open import CaTTExp.GlobularTotal.TreeAlg using (WF)
open import CaTTExp.GlobularTotal.FlatBd
open import CaTTExp.GlobularTotal.NfSub

-- x : ⋆, y : ⋆, f : x → y, z : ⋆, g : y → z
Δ : Ctx
Δ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (var 0) (var 1) ▸ ⋆ ▸ arr ⋆ (var 1) (var 3)

τ : Sub
τ = idₛ Δ

-- g ∘ f
gf : Tm
gf = coh Δ (arr ⋆ (var 0) (var 3)) τ

private
  lf : Nat → LT
  lf y = lt (y ∷ []) []

  arrow : Nat → Nat → Nat → LT
  arrow a b f = lt (a ∷ b ∷ []) (lf f ∷ [])

  bd-leaf : ∀ β i y → bd β i (lf y) ≡ lf y
  bd-leaf false zero    y = refl
  bd-leaf true  zero    y = refl
  bd-leaf false (suc i) y = refl
  bd-leaf true  (suc i) y = refl

  dim-pt : ∀ y β i → bd β (0 + i) (lf y) ≡ lf y
  dim-pt y β i = bd-leaf β i y

  dim-arr : ∀ a b f β i → bd β (1 + i) (arrow a b f) ≡ arrow a b f
  dim-arr a b f false i = cong (λ c → lt (a ∷ b ∷ []) (c ∷ [])) (bd-leaf false i f)
  dim-arr a b f true  i = cong (λ c → lt (a ∷ b ∷ []) (c ∷ [])) (bd-leaf true  i f)

  wf-pt : ∀ y → WF (lf y)
  wf-pt y = refl , tt

  wf-arr : ∀ a b f → WF (arrow a b f)
  wf-arr a b f = refl , wf-pt f , tt

  -- The images of the variables (σ = τ = identity, fuel 1).
  J : Nat → Maybe LT
  J = Ĵ Δ τ 1

  Top : LT → Set
  Top _ = ⊤

  good-pt : ∀ y → J y ≡ just (lf y) → Good J 0 Top (lf y)
  good-pt y e = ((lf y , e , wf-pt y , dim-pt y , tt) , tt) , tt

  good-arr : ∀ a b f → J a ≡ just (lf a) → J b ≡ just (lf b) →
             J f ≡ just (arrow a b f) → Good J 0 Top (arrow a b f)
  good-arr a b f ea eb ef =
    ( (lf a , ea , wf-pt a , dim-pt a , tt)
    , (lf b , eb , wf-pt b , dim-pt b , tt) , tt )
    , ( ((arrow a b f , ef , wf-arr a b f , dim-arr a b f , ea , eb) , tt) , tt ) , tt

  -- Every image is compatible.
  hi : ∀ y b → J y ≡ just b → Good J 0 Top b
  hi 0 _ refl = good-pt 0 refl
  hi 1 _ refl = good-pt 1 refl
  hi 2 _ refl = good-arr 0 1 2 refl refl refl
  hi 3 _ refl = good-pt 3 refl
  hi 4 _ refl = good-arr 1 3 4 refl refl refl
  hi (suc (suc (suc (suc (suc y))))) b ()

  hsub : ∀ y → T (y <ℕ lenₛ τ) → Hyp Δ τ 1 1 Δ (lookupₛ τ y)
  hsub 0 _ = _ , refl
  hsub 1 _ = _ , refl
  hsub 2 _ = _ , refl
  hsub 3 _ = _ , refl
  hsub 4 _ = _ , refl
  hsub (suc (suc (suc (suc (suc y))))) ()

hyp : Hyp Δ τ 1 2 Δ gf
hyp tr refl =
  _ ,
  ( ( (lf 0 , refl , wf-pt 0 , dim-pt 0 , tt)
    , (lf 1 , refl , wf-pt 1 , dim-pt 1 , tt)
    , (lf 3 , refl , wf-pt 3 , dim-pt 3 , tt) , tt )
  , ( ((arrow 0 1 2 , refl , wf-arr 0 1 2 , dim-arr 0 1 2 , refl , refl) , tt) , tt )
  , ( ((arrow 1 3 4 , refl , wf-arr 1 3 4 , dim-arr 1 3 4 , refl , refl) , tt) , tt )
  , tt ) ,
  hi , hsub

-- nf-sub at this instance: nf of gf[τ] is gf's nf flattened along J.
nf-gf : Σ LT λ a → nf 2 Δ gf ≡ just a
nf-gf = _ , refl

nf-sub-gf : nf (2 + 1) Δ (gf [ τ ]tm) ≡ flatG J 0 (fst nf-gf)
nf-sub-gf = nf-sub Δ τ 1 2 Δ gf (fst nf-gf) hyp (snd nf-gf)
