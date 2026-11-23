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
      O : Fm
      O  = U₁ ⊗ W₁
      Is : List Fm
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
        at Ks us a with AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ks} {us = us} a
        ... | cns L Ks₁ x us₁ refl refl ax as with AtL-cons {A = W₁} {As = []} {Ks = Ks₁} {us = us₁} as
        ...   | cns M Ks₂ y us₂ refl refl ay as′ with AtL-nil {Ks = Ks₂} {us = us₂} as′
        ...     | refl , refl = refl , cAt U₁ ax , cAt W₁ ay
        cg : ∀ Ks us vs → AtL Is Ks us → AtL Is Ks vs → us ∼L vs → _∼_ Dp (mraw Ks us) (mraw Ks vs)
        cg Ks us vs a b e with AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ks} {us = us} a | AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ks} {us = vs} b
        ... | cns L Ks₁ x us₁ refl refl _ as | cns _ _ x′ vs₁ refl refl _ bs with AtL-cons {A = W₁} {As = []} {Ks = Ks₁} {us = us₁} as | AtL-cons {A = W₁} {As = []} {Ks = Ks₁} {us = vs₁} bs
        ...   | cns M _ y _ refl refl _ _ | cns _ _ y′ _ refl refl _ _ =
          dcong (co-cong U₁ (fst e)) (co-cong W₁ (fst (snd e))) ≈M-refl
        nt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL Is Ks us → _∼_ Dp (mraw Ks′ (resL hs us)) (res Dp (⊗s hs) (mraw Ks us))
        nt {Ks = Ks} hs us a with AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ks} {us = us} a
        ... | cns L Ks₁ x us₁ refl refl ax as with AtL-cons {A = W₁} {As = []} {Ks = Ks₁} {us = us₁} as
        ...   | cns M Ks₂ y us₂ refl refl ay as′ with AtL-nil {Ks = Ks₂} {us = us₂} as′
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
        up {Z} F {K} {Ls₁} {vs₁} {Ls₂} {vs₂} g₁ g₂ A₁ A₂ hyp with AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ls₁} {us = vs₁} A₁ | AtL-cons {A = U₁} {As = W₁ ∷ []} {Ks = Ls₂} {us = vs₂} A₂
        ... | cns L₁ Ks₁ x₁ us₁ refl refl ax₁ as₁ | cns L₂ Ks₂ x₂ us₂ refl refl ax₂ as₂ with AtL-cons {A = W₁} {As = []} {Ks = Ks₁} {us = us₁} as₁ | AtL-cons {A = W₁} {As = []} {Ks = Ks₂} {us = us₂} as₂
        ...   | cns M₁ Ks₃ y₁ us₃ refl refl ay₁ n₁ | cns M₂ Ks₄ y₂ us₄ refl refl ay₂ n₂ with AtL-nil {Ks = Ks₃} {us = us₃} n₁ | AtL-nil {Ks = Ks₄} {us = us₄} n₂
        ...     | refl , refl | refl , refl =
          Z ⟨ bridge F g₁ x₁ y₁ ax₁ ay₁ ⟩
          Z ⟨ VF-cong F hyp (At-res Dp g₁ (vAt mok _ _ A₁)) ⟩
              ∼-sym Z (bridge F g₂ x₂ y₂ ax₂ ay₂)

  --------------------------------------------------------------------
  -- Corollas between representables: p_{Δ,Θ}, ι_Θ and pt.
  --
  -- The inputs are representables ⟦Θᵢ⟧ = y(λΘᵢ) and the output is a
  -- representable y B with an isomorphism φ : ⊗ᵢ λΘᵢ ≅ B.  The corolla
  -- sends (h₁ : L₁ → λΘ₁, …) to φ ∘ (h₁ ⊗ …); its universal property is
  -- Yoneda.

  λs : List Shape → List Code
  λs []       = []
  λs (Θ ∷ Θs) = λS Θ ∷ λs Θs

  reps : List Shape → List Fm
  reps []       = []
  reps (Θ ∷ Θs) = rep Θ ∷ reps Θs

  -- the arguments named by a list of maps
  yvs : ∀ Θs {Ls} → Maps Ls (λs Θs) → List Uni
  yvs []       []       = []
  yvs (Θ ∷ Θs) {L ∷ _} (h ∷ hs) = (rep Θ , (L , h)) ∷ yvs Θs hs

  yvs-At : ∀ Θs {Ls} (hs : Maps Ls (λs Θs)) → AtL (reps Θs) Ls (yvs Θs hs)
  yvs-At []       []       = tt
  yvs-At (Θ ∷ Θs) (h ∷ hs) = (refl , refl) , yvs-At Θs hs

  -- every argument list at the inputs is named by a list of maps
  yview : ∀ Θs Ls vs → AtL (reps Θs) Ls vs → Σ (Maps Ls (λs Θs)) (λ hs → vs ≡ yvs Θs hs)
  yview []       []       []       _ = [] , refl
  yview []       []       (_ ∷ _)  ()
  yview []       (_ ∷ _)  _        ()
  yview (Θ ∷ Θs) []       _        ()
  yview (Θ ∷ Θs) (L ∷ Ls) []       ()
  yview (Θ ∷ Θs) (L ∷ Ls) ((.(rep Θ) , (.L , h)) ∷ vs) ((refl , refl) , a) with yview Θs Ls vs a
  ... | hs , refl = (h ∷ hs) , refl

  yvs-inv : ∀ Θs {Ls} (hs hs′ : Maps Ls (λs Θs)) → yvs Θs hs ∼L yvs Θs hs′ → hs ≈ᵐ hs′
  yvs-inv []       []       []         _          = tt
  yvs-inv (Θ ∷ Θs) (h ∷ hs) (h′ ∷ hs′) (∼u e , es) = yinv (λS Θ) e , yvs-inv Θs hs hs′ es

  yvs-congˢ : ∀ Θs {Ls} (hs hs′ : Maps Ls (λs Θs)) → hs′ ≈ᵐ hs → yvs Θs hs ∼L yvs Θs hs′
  yvs-congˢ []       []       []         _        = tt
  yvs-congˢ (Θ ∷ Θs) (h ∷ hs) (h′ ∷ hs′) (e , es) = ∼u (yeq (λS Θ) (≈M-sym e)) , yvs-congˢ Θs hs hs′ es

  resL-yvs : ∀ Θs {Ls Ks′} (hs : Maps Ls (λs Θs)) (hs₀ : Maps Ks′ Ls) → resL hs₀ (yvs Θs hs) ≡ yvs Θs (hs ∘ᵐ hs₀)
  resL-yvs []       []       []         = refl
  resL-yvs (Θ ∷ Θs) (h ∷ hs) (g ∷ hs₀) = cong₂ _∷_ (cong (rep Θ ,_) (yres (λS Θ) g h)) (resL-yvs Θs hs hs₀)

  -- reading a list of maps off an argument list
  gyo : ∀ {K′ L A} → Map K′ A → Maybe (K′ ≡ L) → Maybe (Map L A)
  gyo f (just refl) = just f
  gyo f nothing     = nothing

  gyY : ∀ {A} L → Σ Code (λ K → Map K A) → Maybe (Map L A)
  gyY L (K′ , f) = gyo f (decCode K′ L)

  getY : ∀ Θ L → Uni → Maybe (Map L (λS Θ))
  getY Θ L v = gyY L (co (rep Θ) v)

  getY-at : ∀ Θ {L} (h : Map L (λS Θ)) → getY Θ L (rep Θ , (L , h)) ≡ just h
  getY-at Θ {L} h = trans (cong (gyY L) (co-id (rep Θ) (L , h))) (cong (gyo h) (decCode-refl L))

  mcons : ∀ {L A Ls As} → Maybe (Map L A) → Maybe (Maps Ls As) → Maybe (Maps (L ∷ Ls) (A ∷ As))
  mcons (just h) (just hs) = just (h ∷ hs)
  mcons (just h) nothing   = nothing
  mcons nothing  _         = nothing

  getM : ∀ Θs Ls → List Uni → Maybe (Maps Ls (λs Θs))
  getM []       []       []       = just []
  getM []       []       (_ ∷ _)  = nothing
  getM []       (_ ∷ _)  _        = nothing
  getM (Θ ∷ Θs) []       _        = nothing
  getM (Θ ∷ Θs) (L ∷ Ls) []       = nothing
  getM (Θ ∷ Θs) (L ∷ Ls) (v ∷ vs) = mcons (getY Θ L v) (getM Θs Ls vs)

  getM-yvs : ∀ Θs {Ls} (hs : Maps Ls (λs Θs)) → getM Θs Ls (yvs Θs hs) ≡ just hs
  getM-yvs []       []       = refl
  getM-yvs (Θ ∷ Θs) (h ∷ hs) = cong₂ mcons (getY-at Θ h) (getM-yvs Θs hs)

  -- an isomorphism given by an equation of codes
  φE : ∀ {X Y : Code} → X ≡ Y → Map X Y
  φE {X} e = castM refl e (idMap X)

  ψE : ∀ {X Y : Code} → X ≡ Y → Map Y X
  ψE {X} e = castM e refl (idMap X)

  φψE : ∀ {X Y : Code} (e : X ≡ Y) → (φE e ∘M ψE e) ≈M idMap Y
  φψE refl = ∘M-idl _

  ψφE : ∀ {X Y : Code} (e : X ≡ Y) → (ψE e ∘M φE e) ≈M idMap X
  ψφE refl = ∘M-idl _

  module CorY (Θs : List Shape) (B : Code) (φ : Map (concat (λs Θs)) B) (ψ : Map B (concat (λs Θs)))
              (φψ : (φ ∘M ψ) ≈M idMap B) (ψφ : (ψ ∘M φ) ≈M idMap (concat (λs Θs))) where
    private
      As = λs Θs
      Is = reps Θs
      yB = yP B

    fin : ∀ {Ls} → Maybe (Maps Ls As) → U yB
    fin {Ls} (just hs) = concat Ls , (φ ∘M ⊗s hs)
    fin      nothing   = B , idMap B

    cr : List Code → List Uni → U yB
    cr Ls vs = fin (getM Θs Ls vs)

    cr-at : ∀ {Ls} (hs : Maps Ls As) → cr Ls (yvs Θs hs) ≡ (concat Ls , (φ ∘M ⊗s hs))
    cr-at hs = cong fin (getM-yvs Θs hs)

    yAt : ∀ Ls vs → AtL Is Ls vs → At yB (concat Ls) (cr Ls vs)
    yAt Ls vs a with yview Θs Ls vs a
    ... | hs , refl = cong fst (cr-at hs)

    ycg : ∀ Ls us vs → AtL Is Ls us → AtL Is Ls vs → us ∼L vs → _∼_ yB (cr Ls us) (cr Ls vs)
    ycg Ls us vs a b e with yview Θs Ls us a | yview Θs Ls vs b
    ... | hs , refl | hs′ , refl =
      yB ⟨ ∼-≡ yB (cr-at hs) ⟩
      yB ⟨ yeq B (∘M-cong ≈M-refl (⊗s-cong (yvs-inv Θs hs hs′ e))) ⟩
           ∼-≡ yB (sym (cr-at hs′))

    ynt : ∀ {Ks′ Ks} (hs₀ : Maps Ks′ Ks) us → AtL Is Ks us →
          _∼_ yB (cr Ks′ (resL hs₀ us)) (res yB (⊗s hs₀) (cr Ks us))
    ynt {Ks′} {Ks} hs₀ us a with yview Θs Ks us a
    ... | hs , refl =
      yB ⟨ ∼-≡ yB (cong (cr Ks′) (resL-yvs Θs hs hs₀)) ⟩
      yB ⟨ ∼-≡ yB (cr-at (hs ∘ᵐ hs₀)) ⟩
      yB ⟨ yeq B (≈M-trans (φ ∘M (⊗s hs ∘M ⊗s hs₀)) (∘M-cong ≈M-refl (⊗s-∘ hs hs₀))
                           (≈M-sym (∘M-assoc φ (⊗s hs) (⊗s hs₀)))) ⟩
           ∼-≡ yB (sym (trans (cong (res yB (⊗s hs₀)) (cr-at hs)) (yres B (⊗s hs₀) (φ ∘M ⊗s hs))))

    -- decomposition
    ddo : ∀ {K K′} → Map K′ B → Maybe (K′ ≡ K) → DecR K
    ddo f (just refl) = dr As (yvs Θs (idMaps As)) (ψ ∘M f)
    ddo {K} f nothing = defDec K

    dd : ∀ K → U yB → DecR K
    dd K (K′ , f) = ddo f (decCode K′ K)

    dd-at : ∀ {K} (f : Map K B) → dd K (K , f) ≡ dr As (yvs Θs (idMaps As)) (ψ ∘M f)
    dd-at {K} f = cong (ddo f) (decCode-refl K)

    ydAt : ∀ K t → At yB K t → AtL Is (rLs (dd K t)) (rvs (dd K t))
    ydAt K (.K , f) refl =
      subst (λ d → AtL Is (rLs d) (rvs d)) (sym (dd-at f)) (yvs-At Θs (idMaps As))

    -- f = φ ∘ ⊗ ids ∘ ψ ∘ f
    deq-law : ∀ {K} (f : Map K B) → f ≈M ((φ ∘M ⊗s (idMaps As)) ∘M (ψ ∘M f))
    deq-law f =
      ≈M-sym
      (≈M-trans ((φ ∘M idMap (concat As)) ∘M (ψ ∘M f)) (∘M-cong (∘M-cong ≈M-refl (⊗s-ids As)) ≈M-refl)
      (≈M-trans (φ ∘M (ψ ∘M f)) (∘M-cong (∘M-idr φ) ≈M-refl)
      (≈M-trans ((φ ∘M ψ) ∘M f) (≈M-sym (∘M-assoc φ ψ f))
      (≈M-trans (idMap B ∘M f) (∘M-cong φψ ≈M-refl) (∘M-idl f)))))

    ydeq : ∀ K t → At yB K t → _∼_ yB t (res yB (rg (dd K t)) (cr (rLs (dd K t)) (rvs (dd K t))))
    ydeq K (.K , f) refl =
      subst (λ d → _∼_ yB (K , f) (res yB (rg d) (cr (rLs d) (rvs d)))) (sym (dd-at f))
        (yB ⟨ yeq B (deq-law f) ⟩
              ∼-≡ yB (sym (trans (cong (res yB (ψ ∘M f)) (cr-at (idMaps As)))
                                 (yres B (ψ ∘M f) (φ ∘M ⊗s (idMaps As))))))

    -- Yoneda: a framed value at named arguments is a restriction of its value at the identities
    module _ {Z} (F : Framed Is Z) where
      private
        KP = fKP F
        KQ = fKQ F
        w₀ = yvs Θs (idMaps As)
        a₀ = yvs-At Θs (idMaps As)

      yo : ∀ {K Ls} (g : Map K (concat Ls)) (hs : Maps Ls As) →
           _∼_ Z (res Z (Fr KP KQ Ls g) (fF F Ls (yvs Θs hs)))
                 (res Z (Fr KP KQ As (⊗s hs ∘M g)) (fF F As w₀))
      yo {K} {Ls} g hs =
        Z ⟨ res-cong Z ≈M-refl
              (Z ⟨ fcg F Ls (yvs Θs hs) (resL hs w₀) (yvs-At Θs hs) (AtL-res Is hs w₀ a₀)
                       (subst (λ z → yvs Θs hs ∼L z) (sym (resL-yvs Θs (idMaps As) hs))
                              (yvs-congˢ Θs hs (idMaps As ∘ᵐ hs) (ids-∘ᵐ hs))) ⟩
                   fnat F hs w₀ a₀) ⟩
        Z ⟨ ∼-sym Z (res-∘ Z (Fr KP KQ Ls g) (⊗s (idMaps KP ++ᵐ (hs ++ᵐ idMaps KQ))) (fAt F As w₀ a₀)) ⟩
            res-cong Z (Fr-post (idMaps KP) hs (idMaps KQ) g) (∼-refl Z)

    canc : ∀ {K} (m : Map K (concat As)) → m ≈M (ψ ∘M (φ ∘M m))
    canc m =
      ≈M-sym
      (≈M-trans ((ψ ∘M φ) ∘M m) (≈M-sym (∘M-assoc ψ φ m))
      (≈M-trans (idMap (concat As) ∘M m) (∘M-cong ψφ ≈M-refl) (∘M-idl m)))

    ydUP : ∀ {Z} (F : Framed Is Z) {K Ls₁ vs₁ Ls₂ vs₂} (g₁ : Map K (concat Ls₁)) (g₂ : Map K (concat Ls₂)) →
           AtL Is Ls₁ vs₁ → AtL Is Ls₂ vs₂ →
           _∼_ yB (res yB g₁ (cr Ls₁ vs₁)) (res yB g₂ (cr Ls₂ vs₂)) →
           _∼_ Z (res Z (Fr (fKP F) (fKQ F) Ls₁ g₁) (fF F Ls₁ vs₁)) (res Z (Fr (fKP F) (fKQ F) Ls₂ g₂) (fF F Ls₂ vs₂))
    ydUP {Z} F {K} {Ls₁} {vs₁} {Ls₂} {vs₂} g₁ g₂ A₁ A₂ hyp with yview Θs Ls₁ vs₁ A₁ | yview Θs Ls₂ vs₂ A₂
    ... | hs₁ , refl | hs₂ , refl =
      Z ⟨ yo F g₁ hs₁ ⟩
      Z ⟨ res-cong Z (Fr-cong (fKP F) (fKQ F) As key) (∼-refl Z) ⟩
          ∼-sym Z (yo F g₂ hs₂)
      where
        E : ∀ {Ls} (g : Map K (concat Ls)) (hs : Maps Ls As) →
            res yB g (cr Ls (yvs Θs hs)) ≡ (K , ((φ ∘M ⊗s hs) ∘M g))
        E g hs = trans (cong (res yB g) (cr-at hs)) (yres B g (φ ∘M ⊗s hs))
        h′ : ((φ ∘M ⊗s hs₁) ∘M g₁) ≈M ((φ ∘M ⊗s hs₂) ∘M g₂)
        h′ = yinv B (subst (λ z → _∼_ yB z (K , ((φ ∘M ⊗s hs₂) ∘M g₂))) (E g₁ hs₁)
                    (subst (λ z → _∼_ yB (res yB g₁ (cr Ls₁ (yvs Θs hs₁))) z) (E g₂ hs₂) hyp))
        key : (⊗s hs₁ ∘M g₁) ≈M (⊗s hs₂ ∘M g₂)
        key =
          ≈M-trans (ψ ∘M (φ ∘M (⊗s hs₁ ∘M g₁))) (canc _)
          (≈M-trans (ψ ∘M (φ ∘M (⊗s hs₂ ∘M g₂)))
            (∘M-cong ≈M-refl
              (≈M-trans ((φ ∘M ⊗s hs₁) ∘M g₁) (≈M-sym (∘M-assoc φ (⊗s hs₁) g₁))
              (≈M-trans ((φ ∘M ⊗s hs₂) ∘M g₂) h′ (∘M-assoc φ (⊗s hs₂) g₂))))
            (≈M-sym (canc _)))

  --------------------------------------------------------------------
  -- The three instances.

  private
    eP : ∀ Δ Θ → concat (λs (Δ ∷ Θ ∷ [])) ≡ λS Δ ++ λS Θ
    eP Δ Θ = cong (λS Δ ++_) (++-[] (λS Θ))

    eI : ∀ Θ → concat (λs (Θ ∷ [])) ≡ λS Θ
    eI Θ = ++-[] (λS Θ)

  cpD : ∀ Δ Θ → CorD (rep Δ ∷ rep Θ ∷ []) (rep (Δ ⊠ Θ))
  cpD Δ Θ = record
    { cr = cr ; cok = ok yAt ycg ynt
    ; dLs = λ K t → rLs (dd K t) ; dvs = λ K t → rvs (dd K t) ; dg = λ K t → rg (dd K t)
    ; dAt = ydAt ; deq = ydeq ; dUP = ydUP }
    where open CorY (Δ ∷ Θ ∷ []) (λS Δ ++ λS Θ) (φE (eP Δ Θ)) (ψE (eP Δ Θ)) (φψE (eP Δ Θ)) (ψφE (eP Δ Θ))

  cιD : ∀ Θ → CorD (rep Θ ∷ []) (shp Θ)
  cιD Θ = record
    { cr = cr ; cok = ok yAt ycg ynt
    ; dLs = λ K t → rLs (dd K t) ; dvs = λ K t → rvs (dd K t) ; dg = λ K t → rg (dd K t)
    ; dAt = ydAt ; deq = ydeq ; dUP = ydUP }
    where open CorY (Θ ∷ []) (λS Θ) (φE (eI Θ)) (ψE (eI Θ)) (φψE (eI Θ)) (ψφE (eI Θ))

  cptD : CorD [] (rep (disk 0))
  cptD = record
    { cr = cr ; cok = ok yAt ycg ynt
    ; dLs = λ K t → rLs (dd K t) ; dvs = λ K t → rvs (dd K t) ; dg = λ K t → rg (dd K t)
    ; dAt = ydAt ; deq = ydeq ; dUP = ydUP }
    where open CorY [] (G 0) iso0 iso0⁻ iso0-l iso0-r
