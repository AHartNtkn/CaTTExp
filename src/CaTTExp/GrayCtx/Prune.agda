------------------------------------------------------------------------
-- A first datum for D6 (pruning for Gray shapes): the cylinder of an
-- identity is coherently the identity.
--
-- Prune D² = (x, y, f, g, α : f ⇒ g) at α ↦ id f. This is a
-- substitution D¹ ⊢ π : D². Applying the cylinder construction to both
-- sides, the substitution
--
--     D¹ ⊗ D¹  ⊢  π ⊗ D¹  :  D² ⊗ D¹
--
-- is π on each copy, the identity on the cylinder generators of x, y,
-- sends f⊗e and g⊗e to f⊗e, and must send α⊗e to a 3-cell
--
--     f⊗e ; (id f₀ ▹ y⊗e)  ⇛  (x⊗e ◃ id f₁) ; f⊗e .
--
-- Plain CaTT provides one (unitors and "whiskered identity is an
-- identity" coherences over pasting schemes); in CaTT_su both sides
-- reduce to f⊗e and the cell to id(f⊗e). `prunedCyl` builds it, and
-- CaTTExp.GrayCtx.Checks certifies the substitution in both orientations.
------------------------------------------------------------------------
module CaTTExp.GrayCtx.Prune where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import CaTTExp.GrayCtx.VComp using (fromList)

-- Levels in D¹ ⊗ D¹ (N = 3): x₀ y₀ f₀ x₁ y₁ f₁ xₑ yₑ fₑ = 0 … 8.
-- Levels in D² ⊗ D¹ (N = 5): x₀ y₀ f₀ g₀ α₀ x₁ y₁ f₁ g₁ α₁ xₑ yₑ fₑ gₑ αₑ.

-- id(f;h) ⇒ (id f) ▹ h  and  id(h;f) ⇒ h ◃ (id f), over Comp₂ = (x —f→ y —h→ z).
idWhisk : Bool → Ctx → Tm → Tm → Maybe Tm
idWhisk onRight Γ f h = cohT Γ (node (leaf ∷ leaf ∷ [])) (λ P →
    (if onRight
     then (idc P (var 2) >>= λ i → rw F P i (var 4) >>= λ w →
           vcomp P (var 2 ∷ var 4 ∷ []) >>= λ c → idc P c >>= λ j → just (j , w))
     else (idc P (var 4) >>= λ i → lw F P (var 2) i >>= λ w →
           vcomp P (var 2 ∷ var 4 ∷ []) >>= λ c → idc P c >>= λ j → just (j , w))))
  (if onRight then (f ∷ h ∷ []) else (h ∷ f ∷ []))

-- Reverse a full coherence (swap its source and target).
swapCoh : Tm → Maybe Tm
swapCoh (coh P (arr A s t) σ) = just (coh P (arr A t s) σ)
swapCoh _                     = nothing

module _ (sd : Side) (Γ : Ctx) where
  -- Γ is meant to be D¹ ⊗ D¹ (sd), the source of π ⊗ D¹.
  x₀ y₀ f₀ x₁ y₁ f₁ xₑ yₑ fₑ : Tm
  x₀ = var 0 ; y₀ = var 1 ; f₀ = var 2
  x₁ = var 3 ; y₁ = var 4 ; f₁ = var 5
  xₑ = var 6 ; yₑ = var 7 ; fₑ = var 8

  -- right:  αₑ : fₑ ; (α₀ ▹ yₑ) ⇛ (xₑ ◃ α₁) ; gₑ
  -- left:   αₑ : (α₀ ▹ yₑ) ; gₑ ⇛ fₑ ; (xₑ ◃ α₁)
  cell : Maybe Tm
  cell =
    idc Γ f₀ >>= λ i₀ → idc Γ f₁ >>= λ i₁ →
    rw F Γ i₀ yₑ >>= λ W₀ → lw F Γ xₑ i₁ >>= λ W₁ →
    vcomp Γ (f₀ ∷ yₑ ∷ []) >>= λ f₀yₑ → idc Γ f₀yₑ >>= λ j₀ →
    vcomp Γ (xₑ ∷ f₁ ∷ []) >>= λ xₑf₁ → idc Γ xₑf₁ >>= λ j₁ →
    go sd W₀ W₁ j₀ j₁
    where
    go : Side → Tm → Tm → Tm → Tm → Maybe Tm
    go right W₀ W₁ j₀ j₁ =
      -- [fₑ, W₀] ⇛ [fₑ, j₀] ⇛ [fₑ] ⇛ [j₁, fₑ] ⇛ [W₁, fₑ]
      idWhisk true Γ f₀ yₑ >>= λ c₁ → swapCoh c₁ >>= λ Φ₁ →
      stepAt Γ (fₑ ∷ []) (W₀ ∷ []) [] Φ₁ (j₀ ∷ []) >>= λ s₁ →
      unitor false true Γ fₑ >>= λ Φ₂ →
      stepAt Γ [] (fₑ ∷ j₀ ∷ []) [] Φ₂ (fₑ ∷ []) >>= λ s₂ →
      unitor true false Γ fₑ >>= λ Φ₃ →
      stepAt Γ [] (fₑ ∷ []) [] Φ₃ (j₁ ∷ fₑ ∷ []) >>= λ s₃ →
      idWhisk false Γ f₁ xₑ >>= λ Φ₄ →
      stepAt Γ [] (j₁ ∷ []) (fₑ ∷ []) Φ₄ (W₁ ∷ []) >>= λ s₄ →
      vcomp Γ (snd s₁ ∷ snd s₂ ∷ snd s₃ ∷ snd s₄ ∷ [])
    go left W₀ W₁ j₀ j₁ =
      -- [W₀, fₑ] ⇛ [j₀, fₑ] ⇛ [fₑ] ⇛ [fₑ, j₁] ⇛ [fₑ, W₁]
      idWhisk true Γ f₀ yₑ >>= λ c₁ → swapCoh c₁ >>= λ Φ₁ →
      stepAt Γ [] (W₀ ∷ []) (fₑ ∷ []) Φ₁ (j₀ ∷ []) >>= λ s₁ →
      unitor true true Γ fₑ >>= λ Φ₂ →
      stepAt Γ [] (j₀ ∷ fₑ ∷ []) [] Φ₂ (fₑ ∷ []) >>= λ s₂ →
      unitor false false Γ fₑ >>= λ Φ₃ →
      stepAt Γ [] (fₑ ∷ []) [] Φ₃ (fₑ ∷ j₁ ∷ []) >>= λ s₃ →
      idWhisk false Γ f₁ xₑ >>= λ Φ₄ →
      stepAt Γ (fₑ ∷ []) (j₁ ∷ []) [] Φ₄ (W₁ ∷ []) >>= λ s₄ →
      vcomp Γ (snd s₁ ∷ snd s₂ ∷ snd s₃ ∷ snd s₄ ∷ [])

  -- π ⊗ D¹, listed in the order of D² ⊗ D¹.
  prunedSub : Maybe Sub
  prunedSub =
    idc Γ f₀ >>= λ i₀ → idc Γ f₁ >>= λ i₁ → cell >>= λ c →
    just (fromList (x₀ ∷ y₀ ∷ f₀ ∷ f₀ ∷ i₀ ∷
                    x₁ ∷ y₁ ∷ f₁ ∷ f₁ ∷ i₁ ∷
                    xₑ ∷ yₑ ∷ fₑ ∷ fₑ ∷ c ∷ []))

prunedCyl : Side → Maybe (Ctx × Sub)
prunedCyl sd = cyl sd 1 (ctxOf (chain 1)) >>= λ Γ → prunedSub sd Γ >>= λ σ → just (Γ , σ)
