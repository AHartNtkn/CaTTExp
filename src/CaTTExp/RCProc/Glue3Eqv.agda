------------------------------------------------------------------------
-- Two-way 3-cells, identities and the unit law (ledger S20 (i),
-- stage 3e; notes/relative-coherence.md §2 Step 3).
--
-- `Eqv Γ A t u` is a pair of 3-cells t ⇛ u and u ⇛ t. The glue of
-- RCProc.Glue3 lifts to it (`congLE`, `congRE`, `assocE`, `cancelE`),
-- and so does vertical composition (`_⊙_`, by Glue.transA).
--
-- Also two more fixed coherences, pulled back as in Glue3:
--
--   id₂ x y f : f ⇒ f            (over the 1-chain chainC 1)
--   unitE     : id₂ f ∗ h ⇄ h    (over a 2-disc)
--   reflE     : h ⇄ h            (the identity 3-cell, over a 2-disc)
--
-- `paste`: two squares K⁻ ∗ g ⇄ e ∗ K⁺ sharing a side give one for the
-- composites; and `stripE`: a low 2-cell K : U ⇒ V on the left can be
-- removed,
--   K ∗ x ⇄ K ∗ y  ⟹  x ⇄ y,
-- since J ∗ K ⇄ id₂ U for the chain filler J : V ⇒ U (Glue3.cancel).
------------------------------------------------------------------------
module CaTTExp.RCProc.Glue3Eqv where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.Derived using (idS; tm-ty; tm-ctx)
open import CaTTExp.GraphFillerTotal.Chains using (chainC)
open import CaTTExp.RCProc.Eg using (vcomp)
open import CaTTExp.RCProc.Glue using (Ans; transA)
open import CaTTExp.RCProc.Glue3

private
  A′ : Ty
  A′ = arr ⋆ (var 0) (var 1)

------------------------------------------------------------------------
-- The identity 2-cell on a 1-cell.

idT : Ty
idT = arr A′ (var 2) (var 2)

id₂ : Tm → Tm → Tm → Tm
id₂ x y f = coh (chainC 1) idT (⟨⟩ ,ₛ x ,ₛ y ,ₛ f)

private
  dId = snd (from-just (infer (chainC 1) (coh (chainC 1) idT (idS 3))))

  bd2 : ∀ {Γ x y t s c} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s →
        (Γ ⊢tm x ∶ ⋆) × (Γ ⊢tm y ∶ ⋆) × (Γ ⊢tm t ∶ arr ⋆ x y) × (Γ ⊢tm s ∶ arr ⋆ x y)
  bd2 dc with tm-ty dc
  ... | arr-wf dt ds with tm-ty dt
  ...   | arr-wf dx dy = dx , dy , dt , ds

  bd1 : ∀ {Γ x y f} → Γ ⊢tm f ∶ arr ⋆ x y → (Γ ⊢tm x ∶ ⋆) × (Γ ⊢tm y ∶ ⋆)
  bd1 df with tm-ty df
  ... | arr-wf dx dy = dx , dy

id₂-wf : ∀ {Γ x y f} → Γ ⊢tm f ∶ arr ⋆ x y → Γ ⊢tm id₂ x y f ∶ arr (arr ⋆ x y) f f
id₂-wf df = retarget dId (,-wf (,-wf (,-wf (⟨⟩-wf (tm-ctx df)) (fst b)) (snd b)) df)
  where b = bd1 df

low-id₂ : ∀ {Γ x y f} → Γ ⊢tm f ∶ arr ⋆ x y → LowT Γ (id₂ x y f)
low-id₂ df = low-coh (id₂-wf df) (graph-chain 1)

------------------------------------------------------------------------
-- Two-way 3-cells.

Eqv : Ctx → Ty → Tm → Tm → Set
Eqv Γ A t u = Ans Γ A t u × Ans Γ A u t

symE : ∀ {Γ A t u} → Eqv Γ A t u → Eqv Γ A u t
symE (p , q) = q , p

infixr 5 _⊙_
_⊙_ : ∀ {Γ A t s u} → Eqv Γ A t s → Eqv Γ A s u → Eqv Γ A t u
(p , q) ⊙ (p′ , q′) = transA p p′ , transA q′ q

-- Rewriting along equations.
substE : ∀ {Γ A t t′ u u′} → t ≡ t′ → u ≡ u′ → Eqv Γ A t u → Eqv Γ A t′ u′
substE refl refl e = e

substE3 : ∀ {Γ A A′ t t′ u u′} → A ≡ A′ → t ≡ t′ → u ≡ u′ → Eqv Γ A t u → Eqv Γ A′ t′ u′
substE3 refl refl refl e = e

congLE : ∀ {Γ x y t s u c c′ h} → Γ ⊢tm h ∶ arr (arr ⋆ x y) s u →
         Eqv Γ (arr (arr ⋆ x y) t s) c c′ →
         Eqv Γ (arr (arr ⋆ x y) t u) (vcomp (arr ⋆ x y) t s u c h) (vcomp (arr ⋆ x y) t s u c′ h)
congLE dh (p , q) = congL dh p , congL dh q

congRE : ∀ {Γ x y t s u c h h′} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s →
         Eqv Γ (arr (arr ⋆ x y) s u) h h′ →
         Eqv Γ (arr (arr ⋆ x y) t u) (vcomp (arr ⋆ x y) t s u c h) (vcomp (arr ⋆ x y) t s u c h′)
congRE dc (p , q) = congR dc p , congR dc q

assocE : ∀ {Γ x y t s u v c h k} (dc : Γ ⊢tm c ∶ arr (arr ⋆ x y) t s) (dh : Γ ⊢tm h ∶ arr (arr ⋆ x y) s u)
         (dk : Γ ⊢tm k ∶ arr (arr ⋆ x y) u v) →
         Eqv Γ (arr (arr ⋆ x y) t v) (vcomp (arr ⋆ x y) t u v (vcomp (arr ⋆ x y) t s u c h) k)
                                      (vcomp (arr ⋆ x y) t s v c (vcomp (arr ⋆ x y) s u v h k))
assocE dc dh dk = assoc dc dh dk , assoc′ dc dh dk

cancelE : ∀ {Γ x y p q u v} (du : Γ ⊢tm u ∶ arr (arr ⋆ x y) p q) (dv : Γ ⊢tm v ∶ arr (arr ⋆ x y) p q) →
          LowT Γ u → LowT Γ v → Eqv Γ (arr (arr ⋆ x y) p q) u v
cancelE du dv lu lv = cancel du dv lu lv , cancel dv du lv lu

-- The typing of a vertical composite.
vc-wf : ∀ {Γ x y t s u c h} → Γ ⊢tm c ∶ arr (arr ⋆ x y) t s → Γ ⊢tm h ∶ arr (arr ⋆ x y) s u →
        Γ ⊢tm vcomp (arr ⋆ x y) t s u c h ∶ arr (arr ⋆ x y) t u
vc-wf {c = c} {h} dc dh = snd (transA (c , dc) (h , dh))

------------------------------------------------------------------------
-- Pasting two squares K⁻ ∗ g ⇄ e ∗ K⁺ side by side.

module _ {Γ x y X₀ X₁ X₂ B₀ B₁ B₂ K₀ K₁ K₂ g₁ g₂ e₁ e₂}
         (dK₀ : Γ ⊢tm K₀ ∶ arr (arr ⋆ x y) X₀ B₀) (dg₁ : Γ ⊢tm g₁ ∶ arr (arr ⋆ x y) B₀ B₁)
         (dg₂ : Γ ⊢tm g₂ ∶ arr (arr ⋆ x y) B₁ B₂) (de₁ : Γ ⊢tm e₁ ∶ arr (arr ⋆ x y) X₀ X₁)
         (de₂ : Γ ⊢tm e₂ ∶ arr (arr ⋆ x y) X₁ X₂) (dK₁ : Γ ⊢tm K₁ ∶ arr (arr ⋆ x y) X₁ B₁)
         (dK₂ : Γ ⊢tm K₂ ∶ arr (arr ⋆ x y) X₂ B₂) where
  private
    A = arr ⋆ x y

  paste : Eqv Γ (arr A X₀ B₁) (vcomp A X₀ B₀ B₁ K₀ g₁) (vcomp A X₀ X₁ B₁ e₁ K₁) →
          Eqv Γ (arr A X₁ B₂) (vcomp A X₁ B₁ B₂ K₁ g₂) (vcomp A X₁ X₂ B₂ e₂ K₂) →
          Eqv Γ (arr A X₀ B₂) (vcomp A X₀ B₀ B₂ K₀ (vcomp A B₀ B₁ B₂ g₁ g₂))
                              (vcomp A X₀ X₂ B₂ (vcomp A X₀ X₁ X₂ e₁ e₂) K₂)
  paste s₁ s₂ =
    symE (assocE dK₀ dg₁ dg₂) ⊙ congLE dg₂ s₁ ⊙ assocE de₁ dK₁ dg₂ ⊙ congRE de₁ s₂ ⊙
    symE (assocE de₁ de₂ dK₂)

------------------------------------------------------------------------
-- The unit law.

-- a, b, f, g, h : f ⇒ g.
Θu : Ctx
Θu = ε ▸ ⋆ ▸ ⋆ ▸ A′ ▸ A′ ▸ arr A′ (var 2) (var 3)

private
  Lu : Tm
  Lu = vcomp A′ (var 2) (var 2) (var 3) (id₂ (var 0) (var 1) (var 2)) (var 4)

Tu Tu′ : Ty
Tu  = arr (arr A′ (var 2) (var 3)) Lu (var 4)
Tu′ = arr (arr A′ (var 2) (var 3)) (var 4) Lu

private
  dTu  = snd (from-just (infer Θu (coh Θu Tu (idS 5))))
  dTu′ = snd (from-just (infer Θu (coh Θu Tu′ (idS 5))))

unitE : ∀ {Γ x y f g h} → Γ ⊢tm h ∶ arr (arr ⋆ x y) f g →
        Eqv Γ (arr (arr ⋆ x y) f g) (vcomp (arr ⋆ x y) f f g (id₂ x y f) h) h
unitE {Γ} {x} {y} {f} {g} {h} dh = (coh Θu Tu σ , retarget dTu sσ) , (coh Θu Tu′ σ , retarget dTu′ sσ)
  where
  σ = ⟨⟩ ,ₛ x ,ₛ y ,ₛ f ,ₛ g ,ₛ h
  b = bd2 dh
  sσ : Γ ⊢sub σ ∶ Θu
  sσ = ,-wf (,-wf (,-wf (,-wf (,-wf (⟨⟩-wf (tm-ctx dh)) (fst b)) (fst (snd b))) (fst (snd (snd b)))) (snd (snd (snd b)))) dh

------------------------------------------------------------------------
-- The identity 3-cell on a 2-cell.

private
  Tr : Ty
  Tr = arr (arr A′ (var 2) (var 3)) (var 4) (var 4)

  dTr = snd (from-just (infer Θu (coh Θu Tr (idS 5))))

reflE : ∀ {Γ x y f g h} → Γ ⊢tm h ∶ arr (arr ⋆ x y) f g → Eqv Γ (arr (arr ⋆ x y) f g) h h
reflE {Γ} {x} {y} {f} {g} {h} dh = (coh Θu Tr σ , retarget dTr sσ) , (coh Θu Tr σ , retarget dTr sσ)
  where
  σ = ⟨⟩ ,ₛ x ,ₛ y ,ₛ f ,ₛ g ,ₛ h
  b = bd2 dh
  sσ : Γ ⊢sub σ ∶ Θu
  sσ = ,-wf (,-wf (,-wf (,-wf (,-wf (⟨⟩-wf (tm-ctx dh)) (fst b)) (fst (snd b))) (fst (snd (snd b)))) (snd (snd (snd b)))) dh

------------------------------------------------------------------------
-- Stripping a low cell on the left.

module _ {Γ x y U V W K J} (dK : Γ ⊢tm K ∶ arr (arr ⋆ x y) U V) (dJ : Γ ⊢tm J ∶ arr (arr ⋆ x y) V U)
         (lK : LowT Γ K) (lJ : LowT Γ J) where
  private
    A = arr ⋆ x y
    dV = snd (snd (snd (bd2 dK)))
    di = id₂-wf dV

    -- r ⇄ J ∗ (K ∗ r)
    peel : ∀ {r} → Γ ⊢tm r ∶ arr A V W → Eqv Γ (arr A V W) r (vcomp A V U W J (vcomp A U V W K r))
    peel dr =
      symE (unitE dr) ⊙
      congLE dr (cancelE di (vc-wf dJ dK) (low-id₂ dV) (low-vcomp dJ dK lJ lK)) ⊙
      assocE dJ dK dr

  stripE : ∀ {p q} → Γ ⊢tm p ∶ arr A V W → Γ ⊢tm q ∶ arr A V W →
           Eqv Γ (arr A U W) (vcomp A U V W K p) (vcomp A U V W K q) → Eqv Γ (arr A V W) p q
  stripE dp dq e = peel dp ⊙ congRE dJ e ⊙ symE (peel dq)
