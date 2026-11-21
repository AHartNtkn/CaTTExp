------------------------------------------------------------------------
-- The four corollas of the 𝔖̂ instance are representing (S5).
--
--   m_{U,W} : (U, W ▸ U ⊗ W)   the coend injection; its universal
--            property is proved by induction on the generated ∼.
--   p_{Δ,Θ} : (⟦Δ⟧, ⟦Θ⟧ ▸ ⟦Δ ⊠ Θ⟧),  ι_Θ : (⟦Θ⟧ ▸ ⟦Θ⟧♭),  pt : ( ▸ ⟦D⁰⟧)
--            representables; their universal properties are Yoneda.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.Corollas (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC; globe; named)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB
open import CaTTExp.Gray.Biclosed.Steiner.PshOps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.GlobeMaps nmFB using (G; iso0; iso0⁻; iso0-l; iso0-r)
open import CaTTExp.Gray.Biclosed.Steiner.Sem nmFB
open import CaTTExp.Gray.Biclosed.Steiner.Rep nmFB

castM-inj : ∀ {K L L′} (e : L ≡ L′) {m n : Map K L} → castM refl e m ≈M castM refl e n → m ≈M n
castM-inj refl e = e

castM-cancel : ∀ {K L L′} (e : L ≡ L′) (m : Map K L) → castM refl (sym e) (castM refl e m) ≈M m
castM-cancel refl m = ≈M-refl

castM-cancel′ : ∀ {K L L′} (e : L ≡ L′) (m : Map K L′) → castM refl e (castM refl (sym e) m) ≈M m
castM-cancel′ refl m = ≈M-refl

module Corollas (ob : Nat → Psh) where
  open Sem ob
  open Rep ob

  record DecR (K : Code) : Set where
    constructor dr
    field
      rLs : List Code
      rvs : List Uni
      rg  : Map K (concat rLs)
  open DecR

  defDec : ∀ K → DecR K
  defDec K = dr (K ∷ []) [] (castM refl (sym (++-[] K)) (idMap K))

  --------------------------------------------------------------------
  -- m_{U,W}

  module CorM (U₁ W₁ : Fm) where
    private
      O  = U₁ ⊗ W₁
      Is = U₁ ∷ W₁ ∷ []
      DA = ⟦ U₁ ⟧
      DB = ⟦ W₁ ⟧
      Dp = ⟦ U₁ ⊗ W₁ ⟧

    mraw : List Code → List Uni → UF O
    mraw (L ∷ M ∷ _) (a ∷ b ∷ _) = de (L ++ (M ++ [])) L M (co U₁ a) (co W₁ b) (idMap (L ++ (M ++ [])))
    mraw []          _           = defD DA DB
    mraw (L ∷ [])    _           = defD DA DB
    mraw (L ∷ M ∷ _) []          = defD DA DB
    mraw (L ∷ M ∷ _) (a ∷ [])    = defD DA DB

    private
      cAt : ∀ (A : Fm) {K x} → At ⟦ A ⟧ K x → At ⟦ A ⟧ K (co A (A , x))
      cAt A {K} {x} a = subst (At ⟦ A ⟧ K) (sym (co-id A x)) a

    mok : Ok (Is ▸ O) mraw
    mok = ok at cg nt
      where
        at : ∀ Ks us → AtL Is Ks us → At Dp (concat Ks) (mraw Ks us)
        at Ks us a with AtL-cons a
        ... | cns L _ x _ refl refl ax as with AtL-cons as
        ...   | cns M _ y _ refl refl ay as′ with AtL-nil as′
        ...     | refl , refl = refl , cAt U₁ ax , cAt W₁ ay
        cg : ∀ Ks us vs → AtL Is Ks us → AtL Is Ks vs → us ∼L vs → _∼_ Dp (mraw Ks us) (mraw Ks vs)
        cg Ks us vs a b e with AtL-cons a | AtL-cons b
        ... | cns L _ x _ refl refl _ as | cns _ _ x′ _ refl refl _ bs with AtL-cons as | AtL-cons bs
        ...   | cns M _ y _ refl refl _ _ | cns _ _ y′ _ refl refl _ _ =
          dcong (co-cong U₁ (fst e)) (co-cong W₁ (fst (snd e))) ≈M-refl
        nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL Is Ks us → _∼_ Dp (mraw Ks′ (resL hs us)) (res Dp (⊗s hs) (mraw Ks us))
        nt hs us a with AtL-cons a
        ... | cns L _ x _ refl refl ax as with AtL-cons as
        ...   | cns M _ y _ refl refl ay as′ with AtL-nil as′
        nt {L′ ∷ M′ ∷ []} (h₁ ∷ h₂ ∷ []) _ _ | cns L _ x _ refl refl ax as | cns M _ y _ refl refl ay as′ | refl , refl =
          Dp ⟨ dcong (∼-≡ DA (co-id U₁ (res DA h₁ x))) (∼-≡ DB (co-id W₁ (res DB h₂ y))) ≈M-refl ⟩
          Dp ⟨ dgen h₁ h₂ (idMap (L′ ++ (M′ ++ []))) ax ay ⟩
          Dp ⟨ dcong (∼-≡ DA (sym (co-id U₁ x))) (∼-≡ DB (sym (co-id W₁ y)))
                     (≈M-trans _ (∘M-idr (h₁ ⊗ₘ (h₂ ⊗ₘ idMap []))) (≈M-sym (∘M-idl (h₁ ⊗ₘ (h₂ ⊗ₘ idMap []))))) ⟩
               ∼-≡ Dp (sym (dres-at DA DB (h₁ ⊗ₘ (h₂ ⊗ₘ idMap [])) L M (co U₁ (U₁ , x)) (co W₁ (W₁ , y))
                                    (idMap (L ++ (M ++ []))) refl))

    mdgo : ∀ {K K₁} L M (a : UF U₁) (b : UF W₁) (f : Map K₁ (L ++ (M ++ []))) → Maybe (K₁ ≡ K) → DecR K
    mdgo L M a b f (just refl) = dr (L ∷ M ∷ []) ((U₁ , a) ∷ (W₁ , b) ∷ []) f
    mdgo {K} L M a b f nothing = defDec K

    md : ∀ K → UF O → DecR K
    md K (de K₁ L M a b f) = mdgo L M a b f (decCode K₁ K)

    md-at : ∀ {K} L M a b (f : Map K (L ++ (M ++ []))) → md K (de K L M a b f) ≡ dr (L ∷ M ∷ []) ((U₁ , a) ∷ (W₁ , b) ∷ []) f
    md-at {K} L M a b f = cong (mdgo L M a b f) (decCode-refl K)

    -- the value of a framed family on an element of the coend
    module _ {Z} (F : Framed Is Z) where
      private
        Zp = Z
        KP = fKP F
        KQ = fKQ F

      VF : UF O → U Z
      VF (de K L M a b f) = res Z (Fr KP KQ (L ∷ M ∷ []) f) (fF F (L ∷ M ∷ []) ((U₁ , a) ∷ (W₁ , b) ∷ []))

      VF-cong : ∀ {K t t′} → _∼_ Dp t t′ → At Dp K t → _∼_ Z (VF t) (VF t′)
      VF-cong (dcong {K} {L} {M} {a} {a′} {b} {b′} {f} {f′} ea eb ef) (k , aa , ab) =
        res-cong Z (Fr-cong KP KQ (L ∷ M ∷ []) ef)
          (fcg F _ _ _ ((refl , aa) , (refl , ab) , tt) ((refl , At-∼ DA ea aa) , (refl , At-∼ DB eb ab) , tt)
               (∼u ea , ∼u eb , tt))
      VF-cong (dgen {K} {L} {M} {L′} {M′} {a} {b} u v f aa ab) (k , _ , _) =
        Z ⟨ res-cong Z ≈M-refl (fnat F (u ∷ v ∷ []) ((U₁ , a) ∷ (W₁ , b) ∷ []) ((refl , aa) , (refl , ab) , tt)) ⟩
        Z ⟨ ∼-sym Z (res-∘ Z (Fr KP KQ (L ∷ M ∷ []) f) (⊗s (idMaps KP ++ᵐ ((u ∷ v ∷ []) ++ᵐ idMaps KQ)))
                          (fAt F _ _ ((refl , aa) , (refl , ab) , tt))) ⟩
            res-cong Z (Fr-post (idMaps KP) (u ∷ v ∷ []) (idMaps KQ) f) (∼-refl Z)
      VF-cong (dsym p)     at = ∼-sym Z (VF-cong p (At-∼ Dp (dsym p) at))
      VF-cong (dtrans p q) at = ∼-trans Z (VF-cong p at) (VF-cong q (At-∼ Dp p at))

      -- a framed value at a decomposition is VF of the decomposed element
      bridge : ∀ {K L M} (g : Map K (L ++ (M ++ []))) x y → At ⟦ U₁ ⟧ L x → At ⟦ W₁ ⟧ M y →
               _∼_ Z (res Z (Fr KP KQ (L ∷ M ∷ []) g) (fF F (L ∷ M ∷ []) ((U₁ , x) ∷ (W₁ , y) ∷ [])))
                     (VF (res Dp g (mraw (L ∷ M ∷ []) ((U₁ , x) ∷ (W₁ , y) ∷ []))))
      bridge {K} {L} {M} g x y ax ay =
        Z ⟨ res-cong Z (Fr-cong KP KQ (L ∷ M ∷ []) (≈M-sym (∘M-idl g)))
              (fcg F _ _ _ ((refl , ax) , (refl , ay) , tt) ((refl , cAt U₁ ax) , (refl , cAt W₁ ay) , tt) (∼u (∼-≡ DA (sym (co-id U₁ x))) , ∼u (∼-≡ DB (sym (co-id W₁ y))) , tt)) ⟩
            ∼-≡ Z (cong VF (sym (dres-at DA DB g L M (co U₁ (U₁ , x)) (co W₁ (W₁ , y)) (idMap (L ++ (M ++ []))) refl)))

    cm : CorD Is O
    cm = record
      { cr = mraw ; cok = mok
      ; dLs = λ K t → rLs (md K t) ; dvs = λ K t → rvs (md K t) ; dg = λ K t → rg (md K t)
      ; dAt = λ { K (de .K L M a b f) (refl , aa , ab) →
          subst (λ d → AtL Is (rLs d) (rvs d)) (sym (md-at L M a b f)) ((refl , aa) , (refl , ab) , tt) }
      ; deq = λ { K (de .K L M a b f) (refl , aa , ab) →
          subst (λ d → _∼_ Dp (de K L M a b f) (res Dp (rg d) (mraw (rLs d) (rvs d)))) (sym (md-at L M a b f))
            (Dp ⟨ dcong (∼-≡ DA (sym (co-id U₁ a))) (∼-≡ DB (sym (co-id W₁ b))) (≈M-sym (∘M-idl f)) ⟩
                  ∼-≡ Dp (sym (dres-at DA DB f L M (co U₁ (U₁ , a)) (co W₁ (W₁ , b)) (idMap (L ++ (M ++ []))) refl))) }
      ; dUP = up
      }
      where
        up : ∀ {Z} (F : Framed Is Z) {K Ls₁ vs₁ Ls₂ vs₂} (g₁ : Map K (concat Ls₁)) (g₂ : Map K (concat Ls₂)) →
             AtL Is Ls₁ vs₁ → AtL Is Ls₂ vs₂ →
             _∼_ Dp (res Dp g₁ (mraw Ls₁ vs₁)) (res Dp g₂ (mraw Ls₂ vs₂)) →
             _∼_ Z (res Z (Fr (fKP F) (fKQ F) Ls₁ g₁) (fF F Ls₁ vs₁)) (res Z (Fr (fKP F) (fKQ F) Ls₂ g₂) (fF F Ls₂ vs₂))
        up {Z} F g₁ g₂ A₁ A₂ hyp with AtL-cons A₁ | AtL-cons A₂
        ... | cns L₁ _ x₁ _ refl refl ax₁ as₁ | cns L₂ _ x₂ _ refl refl ax₂ as₂ with AtL-cons as₁ | AtL-cons as₂
        ...   | cns M₁ _ y₁ _ refl refl ay₁ n₁ | cns M₂ _ y₂ _ refl refl ay₂ n₂ with AtL-nil n₁ | AtL-nil n₂
        ...     | refl , refl | refl , refl =
          Z ⟨ bridge F g₁ x₁ y₁ ax₁ ay₁ ⟩
          Z ⟨ VF-cong F hyp (At-res Dp g₁ (vAt mok _ _ A₁)) ⟩
              ∼-sym Z (bridge F g₂ x₂ y₂ ax₂ ay₂)
