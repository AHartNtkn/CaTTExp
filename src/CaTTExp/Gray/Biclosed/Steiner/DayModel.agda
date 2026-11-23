------------------------------------------------------------------------
-- The Day convolution model 𝔖̂ (S5): the globes δ, σ and the
-- assembled `Model`.
--
-- 𝔖̂ interprets a formula as a presheaf on the Steiner codes (Psh),
-- ⊗ as Day convolution and the closures as its two homs, rep Θ and
-- shp Θ as the representable y(λΘ), and object variables by a given
-- family of presheaves `ob`.  The globes are representables y(λDⁿ),
-- with δ^± and σ given by postcomposition with the face and
-- degeneracy maps of Steiner complexes (GlobeMaps).
--
-- What this does and does not establish (see notes): operations of
-- (X₁, …, Xₙ ▸ Z) are natural families on the Day multicategory of
-- presheaves.  Tensors of shapes are matched with the Steiner tensor
-- λΔ ⊗ λΘ only as inputs (p_{Δ,Θ} is representing); the strict model 𝔖
-- with ⟦U ⊗ W⟧ the Gray tensor of strict ω-categories is not built here.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.DayModel (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Model using (Model; Cor; corIns; corOut; dsrc) renaming (D to Dg)
import CaTTExp.Gray.Biclosed.Model as Mod
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; AC; globe; named)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB
open import CaTTExp.Gray.Biclosed.Steiner.PshOps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.GlobeMaps nmFB using (G; iso0; iso0⁻; iso0-l; iso0-r; δmap; σmap; d0; σδ; σδ0)
open import CaTTExp.Gray.Biclosed.Steiner.Sem nmFB
open import CaTTExp.Gray.Biclosed.Steiner.Rep nmFB
open import CaTTExp.Gray.Biclosed.Steiner.Corollas nmFB

castM-cc : ∀ {K K′ L L′} (e₁ : K ≡ K′) (e₂ : L ≡ L′) (m : Map K L) → castM e₁ refl (castM refl e₂ m) ≡ castM e₁ e₂ m
castM-cc refl refl m = refl

module DayModel (ob : Nat → Psh) where
  open Sem ob
  open Rep ob
  open Corollas ob

  --------------------------------------------------------------------
  -- Unary operations between representables: postcomposition.

  module Post (Θa : Shape) {B : Code} (φ : Map (λS Θa) B) where
    private
      A  = λS Θa
      yA = yP A
      yB = yP B
      Fa = rep Θa

    praw : List Code → List Uni → U yB
    praw Ks []      = B , idMap B
    praw Ks (u ∷ _) = ypost A φ (co Fa u)

    pAt : ∀ Ks us → AtL (Fa ∷ []) Ks us → At yB (concat Ks) (praw Ks us)
    pAt Ks us a with AtL-one a
    ... | one K (_ , (_ , h)) refl refl (refl , refl) =
      trans (cong (λ z → fst (ypost A φ z)) (co-id Fa (K , h))) (sym (++-[] K))

    pcg : ∀ Ks us vs → AtL (Fa ∷ []) Ks us → AtL (Fa ∷ []) Ks vs → us ∼L vs → _∼_ yB (praw Ks us) (praw Ks vs)
    pcg Ks us vs a b e with AtL-one a | AtL-one b
    ... | one K u refl refl _ | one _ v _ refl _ = ypost-cong A B φ (co-cong Fa (fst e))

    pnt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL (Fa ∷ []) Ks us →
          _∼_ yB (praw Ks′ (resL hs us)) (res yB (⊗s hs) (praw Ks us))
    pnt hs us a with AtL-one a
    pnt {K′ ∷ []} (h₀ ∷ []) _ a | one K (_ , (_ , h)) refl refl (refl , refl) =
      yB ⟨ ∼-≡ yB (cong (ypost A φ) (trans (co-id Fa (res yA h₀ (K , h))) (yres A h₀ h))) ⟩
      yB ⟨ yeqc B (++-[] K′) law ⟩
           ∼-≡ yB (sym (trans (cong (λ z → res yB (h₀ ⊗ₘ idMap []) (ypost A φ z)) (co-id Fa (K , h)))
                              (yres-at B (h₀ ⊗ₘ idMap []) (φ ∘M h) (++-[] K))))
      where
        law : (φ ∘M (h ∘M h₀)) ≈M castM (++-[] K′) refl ((φ ∘M h) ∘M castM refl (++-[] K) (h₀ ⊗ₘ idMap []))
        law = ≈M-sym
          (≈M-trans ((φ ∘M h) ∘M castM (++-[] K′) refl (castM refl (++-[] K) (h₀ ⊗ₘ idMap [])))
                    (castM-∘ (++-[] K′) refl refl (φ ∘M h) (castM refl (++-[] K) (h₀ ⊗ₘ idMap [])))
          (≈M-trans ((φ ∘M h) ∘M h₀)
                    (∘M-cong ≈M-refl (subst (λ z → z ≈M h₀) (sym (castM-cc (++-[] K′) (++-[] K) (h₀ ⊗ₘ idMap [])))
                                            (⊗-unitʳ h₀)))
                    (∘M-assoc φ h h₀)))

  --------------------------------------------------------------------
  -- Nullary operations into a representable: a point.

  module Pt {B : Code} (x : Map [] B) where
    private
      yB = yP B

    qraw : List Code → List Uni → U yB
    qraw _ _ = [] , x

    qAt : ∀ Ks us → AtL [] Ks us → At yB (concat Ks) (qraw Ks us)
    qAt Ks us a with AtL-nil a
    ... | refl , refl = refl

    qcg : ∀ Ks us vs → AtL [] Ks us → AtL [] Ks vs → us ∼L vs → _∼_ yB (qraw Ks us) (qraw Ks vs)
    qcg _ _ _ _ _ _ = ∼-refl yB

    qnt : ∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL [] Ks us →
          _∼_ yB (qraw Ks′ (resL hs us)) (res yB (⊗s hs) (qraw Ks us))
    qnt hs us a with AtL-nil a
    qnt [] _ _ | refl , refl = ∼-sym yB (yB ⟨ ∼-≡ yB (yres B (idMap []) x) ⟩ yeq B (∘M-idr x))

  --------------------------------------------------------------------
  -- The globes.

  postV : ∀ Θa Θb → Map (λS Θa) (λS Θb) → Val
  postV Θa Θb φ = mk ((rep Θa ∷ []) ▸ rep Θb) praw (ok pAt pcg pnt)
    where open Post Θa φ

  δv : Bool → Nat → Val
  δv α zero    = mk ([] ▸ Dg 1) qraw (ok qAt qcg qnt)
    where open Pt (d0 α)
  δv α (suc n) = postV (disk (suc n)) (disk (suc (suc n))) (δmap α (suc n))

  σv : Nat → Val
  σv n = postV (disk (suc n)) (disk n) (σmap n)

  T-δ : ∀ α n → δv α n ∶ (dsrc n ▸ Dg (suc n))
  T-δ α zero    = refl
  T-δ α (suc n) = refl

  T-σ : ∀ n → σv n ∶ ((Dg (suc n) ∷ []) ▸ Dg n)
  T-σ n = refl

  --------------------------------------------------------------------
  -- The corollas.

  corD : (c : Cor) → CorD (corIns c) (corOut c)
  corD (Mod.cm U W) = CorM.cm U W
  corD (Mod.cp Δ Θ) = cpD Δ Θ
  corD Mod.cpt      = cptD
  corD (Mod.cι Θ)   = cιD Θ

  corv : Cor → Val
  corv c = UC.corV (corD c)

  unCv′ : Cor → Nat → Val → Val
  unCv′ c = UC.unCv (corD c)

  --------------------------------------------------------------------
  -- σ ∘ δ^± = 1, and = pt at n = 0.

  -- a retraction of representables composes to the identity
  retr : ∀ Θ₁ Θ₂ (f : Map (λS Θ₁) (λS Θ₂)) (g : Map (λS Θ₂) (λS Θ₁)) → (g ∘M f) ≈M idMap (λS Θ₁) →
         pc (postV Θ₂ Θ₁ g) 0 (postV Θ₁ Θ₂ f) ≈ idv (rep Θ₁)
  retr Θ₁ Θ₂ f g gf =
    ≈-trans (≈-≡ (pc-just (Val.vok (postV Θ₂ Θ₁ g)) (Val.vok (postV Θ₁ Θ₂ f)) 0 (slot [] [] refl refl))) (≈c H)
    where
      F₁ = rep Θ₁
      F₂ = rep Θ₂
      A₁ = λS Θ₁
      A₂ = λS Θ₂
      H : ∀ Ks us → AtL (F₁ ∷ []) Ks us →
          _∼_ ⟦ F₁ ⟧ (PC.rc (Val.vok (postV Θ₂ Θ₁ g)) (Val.vok (postV Θ₁ Θ₂ f)) 0 (slot [] [] refl refl) Ks us)
                     (idraw F₁ Ks us)
      H Ks us a with AtL-one a
      ... | one K (_ , (_ , h)) refl refl (refl , refl) =
        ⟦ F₁ ⟧ ⟨ ∼-≡ ⟦ F₁ ⟧ (cong (λ z → ypost A₂ g (co F₂ (F₂ , ypost A₁ f z))) (co-id F₁ (K , h))) ⟩
        ⟦ F₁ ⟧ ⟨ ∼-≡ ⟦ F₁ ⟧ (cong (ypost A₂ g) (co-id F₂ (K , (f ∘M h)))) ⟩
        ⟦ F₁ ⟧ ⟨ yeq A₁ (≈M-trans ((g ∘M f) ∘M h) (≈M-sym (∘M-assoc g f h))
                         (≈M-trans (idMap A₁ ∘M h) (∘M-cong gf ≈M-refl) (∘M-idl h))) ⟩
                 ∼-≡ ⟦ F₁ ⟧ (sym (co-id F₁ (K , h)))

  σδ-suc : ∀ α n → pc (σv (suc n)) 0 (δv α (suc n)) ≈ idv (Dg (suc n))
  σδ-suc α n = retr (disk (suc n)) (disk (suc (suc n))) (δmap α (suc n)) (σmap (suc n)) (σδ α (suc n))

  σδ-0 : ∀ α → pc (σv 0) 0 (δv α 0) ≈ corv Mod.cpt
  σδ-0 α =
    ≈-trans (≈-≡ (pc-just (Val.vok (σv 0)) (Val.vok (δv α 0)) 0 (slot [] [] refl refl))) (≈c H)
    where
      H : ∀ Ks us → AtL [] Ks us →
          _∼_ ⟦ Dg 0 ⟧ (PC.rc (Val.vok (σv 0)) (Val.vok (δv α 0)) 0 (slot [] [] refl refl) Ks us)
                      (Val.raw (corv Mod.cpt) Ks us)
      H Ks us a with AtL-nil a
      ... | refl , refl =
        ⟦ Dg 0 ⟧ ⟨ ∼-≡ ⟦ Dg 0 ⟧ (cong (ypost (G 1) (σmap 0)) (co-id (Dg 1) ([] , d0 α))) ⟩
                  yeq (G 0) (≈M-trans iso0 (σδ0 α) (≈M-sym (∘M-idr iso0)))

  --------------------------------------------------------------------
  -- The model.

  dayModel : Model
  dayModel = record
    { V = Val ; _≈_ = _≈_ ; ≈-refl = ≈-refl ; ≈-sym = ≈-sym ; ≈-trans = ≈-trans
    ; _∶_ = _∶_ ; ∶-≈ = ∶-≈
    ; pc = pc ; idv = idv ; cor = corv ; evL = evL ; evR = evR ; δ = δv ; σ = σv
    ; unC = unCv′ ; curL = curL ; curR = curR
    ; T-pc = T-pc ; T-id = T-id ; T-cor = λ c → refl ; T-evL = T-evL ; T-evR = T-evR ; T-δ = T-δ ; T-σ = T-σ
    ; pc-cong = pc-cong ; seq = seq ; par = par ; unit-l = unit-l ; unit-r = unit-r
    ; T-unC = λ {y} {P} {c} → UC.T-unC (corD c)
    ; unC-l = λ {x} {P} {c} → UC.unC-l (corD c)
    ; unC-r = λ {y} {P} {c} → UC.unC-r (corD c)
    ; unC-cong = λ c → UC.unC-cong (corD c)
    ; T-curL = T-curL ; curL-l = curL-l ; curL-r = curL-r ; curL-cong = curL-cong
    ; T-curR = T-curR ; curR-l = curR-l ; curR-r = curR-r ; curR-cong = curR-cong
    ; σδ-suc = σδ-suc ; σδ-0 = σδ-0
    }
