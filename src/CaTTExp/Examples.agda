------------------------------------------------------------------------
-- Example derivations in pure CaTT, produced by the certified checker
-- at typechecking time. Each `from-just` only typechecks if the
-- checker succeeds, and its result is a genuine derivation.
------------------------------------------------------------------------
module CaTTExp.Examples where

open import CaTTExp.Prelude
open import CaTTExp.Pure

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- Pasting contexts as trees.

-- x
D₀ : Ctx
D₀ = ctxOf leaf

-- x —f→ y
D₁ : Ctx
D₁ = ctxOf (node (leaf ∷ []))

-- x —f→ y —g→ z      (levels: x=0 y=1 f=2 z=3 g=4)
Comp₂ : Ctx
Comp₂ = ctxOf (node (leaf ∷ leaf ∷ []))

-- x —f→ y —g→ z —h→ w (levels: x=0 y=1 f=2 z=3 g=4 w=5 h=6)
Comp₃ : Ctx
Comp₃ = ctxOf (node (leaf ∷ leaf ∷ leaf ∷ []))

-- The trees really produce the contexts one writes by hand.
_ : Comp₂ ≡ (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ ⋆ ▸ arr ⋆ (v 1) (v 3))
_ = refl

------------------------------------------------------------------------
-- Identity: a coherence over D₀ (uses every variable on both sides).

idTy : Ty
idTy = arr ⋆ (v 0) (v 0)

id : Tm → Tm
id x = coh D₀ idTy ⟪ x ∷ [] ⟫

------------------------------------------------------------------------
-- Binary composition: an operation over Comp₂ (source uses ∂⁻ = {x},
-- target uses ∂⁺ = {z}).

compTy : Ty
compTy = arr ⋆ (v 0) (v 3)

comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh Comp₂ compTy ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

-- In Comp₂ itself, comp(f, g) : x → z.
comp-wf : Comp₂ ⊢tm comp (v 0) (v 1) (v 2) (v 3) (v 4) ∶ arr ⋆ (v 0) (v 3)
comp-wf = snd (from-just (infer Comp₂ (comp (v 0) (v 1) (v 2) (v 3) (v 4))))

-- The boundary computations agree with Finster–Mimram.
_ : ∂⁻ Comp₂ ≡ (0 ∷ [])
_ = refl
_ : ∂⁺ Comp₂ ≡ (3 ∷ [])
_ = refl

------------------------------------------------------------------------
-- Associator over Comp₃: (f;g);h ⇒ f;(g;h), a full coherence.

fg-h : Tm
fg-h = comp (v 0) (v 3) (comp (v 0) (v 1) (v 2) (v 3) (v 4)) (v 5) (v 6)

f-gh : Tm
f-gh = comp (v 0) (v 1) (v 2) (v 5) (comp (v 1) (v 3) (v 4) (v 5) (v 6))

assocTy : Ty
assocTy = arr (arr ⋆ (v 0) (v 5)) fg-h f-gh

assoc : Tm
assoc = coh Comp₃ assocTy (idₛ Comp₃)

assoc-wf : Comp₃ ⊢tm assoc ∶ assocTy
assoc-wf = snd (from-just (infer Comp₃ assoc))

------------------------------------------------------------------------
-- Left unitor over D₁: id(x);f ⇒ f.

lunitor : Tm
lunitor = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (comp (v 0) (v 0) (id (v 0)) (v 1) (v 2)) (v 2))
              (idₛ D₁)

lunitor-wf = snd (from-just (infer D₁ lunitor))

------------------------------------------------------------------------
-- 2-dimensional: vertical composition of α : f ⇒ g and β : g ⇒ h,
-- and horizontal composition (whiskering-free exchange shape).

-- x, y, f, g, α:f⇒g, h, β:g⇒h  (levels 0..6)
VComp : Ctx
VComp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))

_ : VComp ≡ (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)
               ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
               ▸ arr ⋆ (v 0) (v 1)
               ▸ arr (arr ⋆ (v 0) (v 1)) (v 3) (v 5))
_ = refl

vcomp : Tm
vcomp = coh VComp (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) (idₛ VComp)

vcomp-wf = snd (from-just (infer VComp vcomp))

-- Horizontal composition: α : f ⇒ f' between x and y, β : g ⇒ g'
-- between y and z. Levels: x0 y1 f2 f'3 α4 z5 g6 g'7 β8.
HComp : Ctx
HComp = ctxOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []))

hcomp : Tm
hcomp = coh HComp
  (arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                           (comp (v 0) (v 1) (v 3) (v 5) (v 7)))
  (idₛ HComp)

hcomp-wf = snd (from-just (infer HComp hcomp))

------------------------------------------------------------------------
-- Negative examples: the checker rejects these.

-- Not a pasting context: two parallel arrows with nothing between them.
Sphere₁ : Ctx
Sphere₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)

_ : is-just (infer Sphere₁ (coh Sphere₁ (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)) (idₛ Sphere₁)))
    ≡ false
_ = refl

-- Fails both side conditions: a "composite" x → y over Comp₂ forgets z, g.
_ : is-just (infer Comp₂ (coh Comp₂ (arr ⋆ (v 0) (v 1)) (idₛ Comp₂))) ≡ false
_ = refl

-- Directedness: no inverse of f, since g;f has the wrong boundary.
_ : is-just (infer D₁ (coh D₁ (arr ⋆ (v 1) (v 0)) (idₛ D₁))) ≡ false
_ = refl
