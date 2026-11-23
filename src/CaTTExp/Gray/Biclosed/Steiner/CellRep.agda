------------------------------------------------------------------------
-- Cells of representables in 𝔖̂ are maps of 𝒮 (D7g-link, part 3), and
-- the walking-square criterion stated through the syntax (part 4).
--
-- A unary operation x : (⟦Dⁿ⟧ ▸ y B) of 𝔖̂ *represents* φ : λDⁿ → B
-- when x sends the element h : L → λDⁿ to φ ∘ h (`Rep`).  Every such
-- operation represents a map (`rep-ext`, Yoneda), and the faces
-- pc x 0 δ^± represent φ ∘ δ^± (`rep-face`).
--
-- `ws-no-term`: in 𝔖̂, for any valuation ε satisfying Γ, if the 1-cells
-- s, t of (▸ rep(D¹ ⊠ D¹)) represent paths with n₀ = (t, top) in s and
-- not in t, then no term over Γ has type s ⇒ t.  This is the D7g
-- instance criterion for the walking square; choosing a concrete Γ, σ
-- and ε (parts 1–2 of D7g-link) is not done here.  No postulates.
------------------------------------------------------------------------
open import CaTTExp.Prelude using (Nat)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (FB)

module CaTTExp.Gray.Biclosed.Steiner.CellRep (nmFB : Nat → FB) where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Biclosed.Syntax
open import CaTTExp.Gray.Biclosed.Typing using (dim; baseM; infer)
open import CaTTExp.Gray.Biclosed.ListOps using (lookup)
open import CaTTExp.Gray.Biclosed.Soundness using (no-term)
import CaTTExp.Gray.Biclosed.Sem as BSem
import CaTTExp.Gray.Biclosed.RowSem as BRow
open import CaTTExp.Gray.Biclosed.Model using (Model) renaming (D to Dg)
open import CaTTExp.Gray.Biclosed.Steiner.Codes using (Code; globe)
open import CaTTExp.Gray.Biclosed.Steiner.Psh nmFB
open import CaTTExp.Gray.Biclosed.Steiner.PshOps nmFB
open import CaTTExp.Gray.Biclosed.Steiner.GlobeMaps nmFB using (G; δmap)
open import CaTTExp.Gray.Biclosed.Steiner.Sem nmFB
open import CaTTExp.Gray.Biclosed.Steiner.DayModel nmFB
open import CaTTExp.Gray.Biclosed.Steiner.WalkingSquare nmFB
  using (no-reverse-face; n₀)
open import CaTTExp.Gray.Biclosed.Steiner.Globe using (GCell; top)

-- a cast through a unit-law cast
cast-unit : ∀ {A A′ C C′ B} (e₁ : A′ ≡ A) (e₂ : C′ ≡ C) (f : Map C′ B) (X : Map A′ C′) (h : Map A C) →
            castM e₁ e₂ X ≈M h → castM e₁ refl (f ∘M X) ≈M (castM e₂ refl f ∘M h)
cast-unit refl refl f X h p = ∘M-cong ≈M-refl p

module CellRep (ob : Nat → Psh) where
  open Sem ob
  open DayModel ob

  --------------------------------------------------------------------
  -- Representing a map

  module _ (n : Nat) (B : Code) where
    private
      Fn = rep (disk n)
      yB = yP B

    -- a record, so that Rep r φ is compared through r and φ and never
    -- unfolded (unfolding makes the conversion checks below very slow)
    record Rep (r : List Code → List Uni → U yB) (φ : Map (G n) B) : Set where
      constructor mkRep
      field run : ∀ L (h : Map L (G n)) → _∼_ yB (r (L ∷ []) ((Fn , (L , h)) ∷ [])) (L , (φ ∘M h))
    open Rep public

    -- the list stage only needs to be propositionally the element's
    RepG : ∀ {r φ} → Rep r φ → ∀ L′ L (e : L ≡ L′) (h : Map L (G n)) →
           _∼_ yB (r (L′ ∷ []) ((Fn , (L , h)) ∷ [])) (L , (φ ∘M h))
    RepG R L′ .L′ refl h = run R L′ h

    private
      core : ∀ {L K′} (h : Map L (G n)) (f : Map K′ B) (e : K′ ≡ G n ++ []) →
             _∼_ yB (res yB (h ⊗ₘ idMap []) (K′ , f)) (L , (castM (trans e (++-[] (G n))) refl f ∘M h))
      core {L} h f refl =
        yB ⟨ ∼-≡ yB (yres B (h ⊗ₘ idMap []) f) ⟩
             ∼-sym yB (yeqc B (++-[] L)
               (≈M-sym (cast-unit (++-[] L) (++-[] (G n)) f (h ⊗ₘ idMap []) h (⊗-unitʳ h))))

    -- Yoneda: every operation (⟦Dⁿ⟧ ▸ y B) represents a map
    rep-ext : ∀ (r : List Code → List Uni → U yB) →
              (∀ Ks us → AtL (Fn ∷ []) Ks us → At yB (concat Ks) (r Ks us)) →
              (∀ Ks us vs → AtL (Fn ∷ []) Ks us → AtL (Fn ∷ []) Ks vs → us ∼L vs → _∼_ yB (r Ks us) (r Ks vs)) →
              (∀ {Ks′ Ks} (hs : Maps Ks′ Ks) us → AtL (Fn ∷ []) Ks us →
                 _∼_ yB (r Ks′ (resL hs us)) (res yB (⊗s hs) (r Ks us))) →
              Σ (Map (G n) B) (Rep r)
    rep-ext r vA vC vN = go (r (G n ∷ []) u₀) refl (vA _ _ a₀)
      where
        u₀ : List Uni
        u₀ = (Fn , (G n , idMap (G n))) ∷ []
        a₀ : AtL (Fn ∷ []) (G n ∷ []) u₀
        a₀ = (refl , refl) , tt
        go : ∀ r₀ → r (G n ∷ []) u₀ ≡ r₀ → fst r₀ ≡ G n ++ [] → Σ (Map (G n) B) (Rep r)
        go (K′ , f) q e = castM (trans e (++-[] (G n))) refl f , mkRep R
          where
            R : ∀ L (h : Map L (G n)) → _∼_ yB (r (L ∷ []) ((Fn , (L , h)) ∷ [])) (L , (castM (trans e (++-[] (G n))) refl f ∘M h))
            R L h =
              yB ⟨ vC (L ∷ []) _ _ ((refl , refl) , tt) ((refl , refl) , tt) (∼u (yeq (G n) (≈M-sym (∘M-idl h))) , tt) ⟩
              yB ⟨ ∼-≡ yB (cong (λ z → r (L ∷ []) ((Fn , z) ∷ [])) (sym (yres (G n) h (idMap (G n))))) ⟩
              yB ⟨ vN (h ∷ []) u₀ a₀ ⟩
              yB ⟨ ∼-≡ yB (cong (res yB (h ⊗ₘ idMap [])) q) ⟩
                   core h f e

  --------------------------------------------------------------------
  -- Faces

  rep-face : ∀ α k Θ (r : List Code → List Uni → UF (rep Θ)) (o : Ok ((Dg (suc (suc k)) ∷ []) ▸ rep Θ) r) φ →
             Rep (suc (suc k)) (λS Θ) r φ →
             Rep (suc k) (λS Θ) (PC.rc o (Val.vok (δv α (suc k))) 0 (slot [] [] refl refl)) (φ ∘M δmap α (suc k))
  rep-face α k Θ r o φ R = mkRep λ L h →
    yB ⟨ ∼-≡ yB (cong (λ z → r ((L ++ []) ∷ []) ((F₂ , ypost A₁ (δmap α (suc k)) z) ∷ [])) (co-id F₁ (L , h))) ⟩
    yB ⟨ RepG (suc (suc k)) (λS Θ) {r = r} {φ = φ} R (L ++ []) L (sym (++-[] L)) (δmap α (suc k) ∘M h) ⟩
         yeq (λS Θ) (≈M-sym (∘M-assoc φ (δmap α (suc k)) h))
    where
      yB = yP (λS Θ)
      F₁ = rep (disk (suc k))
      F₂ = rep (disk (suc (suc k)))
      A₁ = λS (disk (suc k))

  -- two operations related by ≈ that represent maps represent the same map
  rep-≈ : ∀ n Θ {r r′ : List Code → List Uni → UF (rep Θ)} {o o′} {φ φ′} →
          mk ((Dg n ∷ []) ▸ rep Θ) r o ≈ mk ((Dg n ∷ []) ▸ rep Θ) r′ o′ →
          Rep n (λS Θ) r φ → Rep n (λS Θ) r′ φ′ → φ ≈M φ′
  rep-≈ n Θ (≈c e) R R′ =
    ≈M-trans (φ₀ ∘M idMap (G n)) (≈M-sym (∘M-idr _))
    (≈M-trans (φ₁ ∘M idMap (G n))
      (yinv (λS Θ) (yB ⟨ ∼-sym yB (run R (G n) (idMap (G n))) ⟩
                    yB ⟨ e (G n ∷ []) _ ((refl , refl) , tt) ⟩
                         run R′ (G n) (idMap (G n))))
      (∘M-idr _))
    where
      yB = yP (λS Θ)
      φ₀ = _
      φ₁ = _

  --------------------------------------------------------------------
  -- The walking-square criterion through the syntax

  private
    WS = disk 1 ⊠ disk 1
    R  = rep WS

  -- a value that is a unary operation (⟦Dⁿ⟧ ▸ rep Θ) representing φ
  data RepV (n : Nat) (Θ : Shape) (φ : Map (G n) (λS Θ)) : Val → Set where
    repV : ∀ {r o} → Rep n (λS Θ) r φ → RepV n Θ φ (mk ((Dg n ∷ []) ▸ rep Θ) r o)

  -- the face of a representing 2-cell.  Stated for an abstract side α
  -- and dimension suc k: with literal dimensions Agda unfolds δv while
  -- comparing types, and the check does not finish.
  face-rep : ∀ α k {r o} φ → Rep (suc (suc k)) (λS WS) r φ → ∀ {vs φs} →
             pc (mk ((Dg (suc (suc k)) ∷ []) ▸ R) r o) 0 (δv α (suc k)) ≈ vs → RepV (suc k) WS φs vs →
             (φ ∘M δmap α (suc k)) ≈M φs
  face-rep α k {r} {o} φ Rφ fs (repV Ss) =
    rep-≈ (suc k) WS (≈-trans (≈-≡ (sym (pc-just o (Val.vok (δv α (suc k))) 0 (slot [] [] refl refl)))) fs)
      (rep-face α k WS r o φ Rφ) Ss

  module _ where
    open BSem dayModel using (SC; val; module Interp; HomMem; cell)
    open BRow dayModel using (CellAt; cellAt)

    -- a 2-cell of (▸ rep WS) whose faces represent maps is represented by
    -- a map with those faces.  Stated for an abstract dimension suc k:
    -- with literal dimensions Agda unfolds δv while comparing types, and
    -- the check does not finish.
    cell-rep : ∀ k {φs φt} v vs vt → CellAt (suc (suc k)) 0 ([] ▸ R) v →
               pc v 0 (δv false (suc k)) ≈ vs → pc v 0 (δv true (suc k)) ≈ vt →
               RepV (suc k) WS φs vs → RepV (suc k) WS φt vt →
               Σ (Map (G (suc (suc k))) (λS WS)) λ φ →
                 ((φ ∘M δmap false (suc k)) ≈M φs) × ((φ ∘M δmap true (suc k)) ≈M φt)
    cell-rep k (mk _ r o) _ _ (cellAt [] [] refl refl refl) fs ft Ss St
      with rep-ext (suc (suc k)) (λS WS) r (vAt o) (vcong o) (vnat o)
    ... | φ , Rφ = φ , face-rep false k φ Rφ fs Ss , face-rep true k φ Rφ ft St

    -- If, under a valuation ε of Γ in 𝔖̂, the 1-cells s and t of
    -- (▸ rep(D¹ ⊠ D¹)) represent paths φs, φt with n₀ = (t, top) in φs
    -- and not in φt, then no term over Γ has type s ⇒ t.
    ws-no-term : ∀ (ε : Nat → SC) Γ → (∀ i {A} → lookup Γ i ≡ just A → Interp.Mem ε A (ε i)) →
                 ∀ (a b s t : Tm) φs φt →
                 RepV 1 WS φs (val (Interp.⟦_⟧ ε s)) → RepV 1 WS φt (val (Interp.⟦_⟧ ε t)) →
                 ∀ k → mat φs (top , tt) n₀ ≡ suc k → mat φt (top , tt) n₀ ≡ 0 →
                 ∀ x → infer Γ x ≡ just (hom dir 0 (hom dir 0 (op ([] ▸ R)) a b) s t) → ⊥
    ws-no-term ε Γ hyp a b s t φs φt Rs Rt k es et =
      no-term dayModel ε Γ hyp (hom dir 0 (hom dir 0 (op ([] ▸ R)) a b) s t) empty
      where
        empty : ∀ c → Interp.Mem ε (hom dir 0 (hom dir 0 (op ([] ▸ R)) a b) s t) c → ⊥
        empty c m with cell-rep zero (val c) _ _ (cell m) (HomMem.fS m) (HomMem.fT m) Rs Rt
        ... | φ , eS , eT =
          no-reverse-face φ k (trans (≈mat eS (top , tt) n₀) es) (trans (≈mat eT (top , tt) n₀) et)
