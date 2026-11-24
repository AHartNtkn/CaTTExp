------------------------------------------------------------------------
-- The coherence case of two-tier L needs full *Gray* support
-- (S30, notes/lax-sc-completeness.md §3).
--
-- Over HComp = ΣD¹ ∨ ΣD¹ take the two layerings
--
--   βα  = (f◁β) ; (α▷g′)
--   βα₂ = (1_{f;g} ; (f◁β)) ; (α▷g′)
--
-- They are parallel, have the same image in 𝔉(HComp) (the 1-cell
-- ∂⁻τ of the lax square), and together use every variable of HComp.
-- So the type βα → βα₂ has exactly one inhabitant in the free model
-- (the identity; a strict ω-category of a loop-free Steiner complex has
-- no non-identity endo-cells), and that inhabitant uses every variable.
--
-- Facts checked here:
--  (1) both terms are derivable, at the same type;
--  (2) their supports agree (sameDown both ways), but are not the full
--      Gray support of HComp: the top generator α⊗β is missing;
--  (3) graySide rejects coh_{HComp, βα → βα₂}, in both directions,
--      so no single coherence over HComp has this type, and no
--      pasting sub-context of HComp contains all the variables used;
--  (4) a *composite* of coherences of that type is derivable: the
--      whiskering of the unitor λ : L ⇛ 1;L by R.
--
-- So the literal single-head reading of completeness ("a uniquely
-- inhabited type that uses every variable is accepted") fails for
-- two-tier L, while the reading "every cell of the free model is the
-- image of a derivable term" survives here. It also shows that the
-- proof of Proposition 4.3 of notes/surface-conservativity.md (EL in
-- pasting contexts by one coherence-case coh over Var(u)) does not
-- apply to two-tier L as stated: that coh is exactly (3).
------------------------------------------------------------------------
module CaTTExp.Gray.CohCaseGap where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Examples
  using (D₁; HComp; VComp; comp; vcomp; lw; rw; x; y; f; f'; α; z; g; g'; β;
         fg; fg'; f'g; f'g'; βα; Txz)

v : Nat → Tm
v = var

-- identity 2-cell on a 1-cell (coherence case over D¹)
id₂ : Tm → Tm → Tm → Tm
id₂ a b h = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) ⟪ a ∷ b ∷ h ∷ [] ⟫

L R : Tm
L = lw x y f z g g' β
R = rw x y f f' α z g'

1L : Tm
1L = vcomp x z fg fg (id₂ x z fg) fg' L

βα₂ : Tm
βα₂ = vcomp x z fg fg' 1L f'g' R

-- (1) both derivable at the same type
_ : βα ≡ vcomp x z fg fg' L f'g' R
_ = refl

βα-ty : fst (from-just (infer HComp βα)) ≡ arr Txz fg f'g'
βα-ty = refl

βα₂-ty : fst (from-just (infer HComp βα₂)) ≡ arr Txz fg f'g'
βα₂-ty = refl

-- (2) equal supports, not full
_ : sameDown HComp (supp βα (arr Txz fg f'g')) (supp βα₂ (arr Txz fg f'g')) ≡ true
_ = refl

_ : sameDown HComp (supp βα (arr Txz fg f'g')) (fullT (homs HComp)) ≡ false
_ = refl

-- (3) the single coherence over HComp is rejected, both directions
gap : graySide HComp (arr Txz fg f'g') βα βα₂ ≡ false
gap = refl

gap⁻ : graySide HComp (arr Txz fg f'g') βα₂ βα ≡ false
gap⁻ = refl

no-single : ∀ {Γ σ B} → ¬ (Γ ⊢tm coh HComp (arr (arr Txz fg f'g') βα βα₂) σ ∶ B)
no-single (coh-wf _ _ _ ok _) = subst T gap ok

-- (4) the composite: λ : L ⇛ 1;L (coherence case over D², one hom),
-- then whiskered by R (operation case over the whiskering context).

-- D²:  x0 z1 a2 b3 L4 : a ⇒ b, read as a 2-cell of one hom
D₂ : Ctx
D₂ = ctxOf (node (node (leaf ∷ []) ∷ []))

λ-ty : Tm → Tm → Tm → Tm → Tm → Ty
λ-ty X Z A B M = arr (arr (arr ⋆ X Z) A B) M (vcomp X Z A A (id₂ X Z A) B M)

unitor : Tm
unitor = coh D₂ (λ-ty (v 0) (v 1) (v 2) (v 3) (v 4))
             ⟪ x ∷ z ∷ fg ∷ fg' ∷ L ∷ [] ⟫

-- whiskering context: x0 z1 a2 b3 M4 M'5 μ6 : M ⇛ M' c7 N8 : b ⇒ c
Wh : Ctx
Wh = ctxOf (node (node (node (leaf ∷ []) ∷ leaf ∷ []) ∷ []))

whTy : Ty
whTy = arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7))
           (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (v 8))
           (vcomp (v 0) (v 1) (v 2) (v 3) (v 5) (v 7) (v 8))

e : Tm
e = coh Wh whTy ⟪ x ∷ z ∷ fg ∷ fg' ∷ L ∷ 1L ∷ unitor ∷ f'g' ∷ R ∷ [] ⟫

e-ty : fst (from-just (infer HComp e)) ≡ arr (arr Txz fg f'g') βα βα₂
e-ty = refl

e-wf : HComp ⊢tm e ∶ arr (arr Txz fg f'g') βα βα₂
e-wf = snd (from-just (infer HComp e))
