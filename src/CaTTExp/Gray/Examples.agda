------------------------------------------------------------------------
-- Worked examples of two-tier L (notes/pseudo-vs-gray.md §3.4, §0
-- Examples 1–2). Every positive example is a derivation produced by
-- the certified checker at type-checking time; every negative example
-- is either a proof that the coh's side condition is false (so no
-- derivation of that coh exists at all) or a checker rejection.
------------------------------------------------------------------------
module CaTTExp.Gray.Examples where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
import CaTTExp.Pure as C           -- plain CaTT, for comparison

v : Nat → Tm
v = var

------------------------------------------------------------------------
-- Pasting contexts.

-- x0 —f2→ y1
D₁ : Ctx
D₁ = ctxOf (node (leaf ∷ []))

-- x0 —f2→ y1 —g4→ z3
Comp₂ : Ctx
Comp₂ = ctxOf (node (leaf ∷ leaf ∷ []))

-- vertical pair in one hom: x0 y1 f2 g3 α4:f⇒g h5 β6:g⇒h
VComp : Ctx
VComp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))

-- left whiskering shape ΣD⁰ ∨ ΣD¹: x0 y1 f2 z3 g4 g'5 β6:g⇒g'
LW : Ctx
LW = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ []))

-- right whiskering shape ΣD¹ ∨ ΣD⁰: x0 y1 f2 f'3 α4:f⇒f' z5 g6
RW : Ctx
RW = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ []))

-- ΣD¹ ∨ ΣD¹: x0 y1 f2 f'3 α4:f⇒f' z5 g6 g'7 β8:g⇒g'
HComp : Ctx
HComp = ctxOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []))

_ : HComp ≡ (ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)
               ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
               ▸ ⋆ ▸ arr ⋆ (v 1) (v 5) ▸ arr ⋆ (v 1) (v 5)
               ▸ arr (arr ⋆ (v 1) (v 5)) (v 6) (v 7))
_ = refl

------------------------------------------------------------------------
-- The Gray unfolding of HComp is the lax square D¹ ⊗ D¹.

_ : map hd (homs HComp) ≡ (1 ∷ 1 ∷ [])
_ = refl

-- top cell α⊗β
_ : topT (homs HComp) ≡ ((4 ∷ 8 ∷ []) ∷ [])
_ = refl

-- ∂⁻(α⊗β) at dimension 1: f⊗β + α⊗g'   (β first, then α)
_ : chainT false 1 (homs HComp) ≡ ((2 ∷ 8 ∷ []) ∷ (4 ∷ 7 ∷ []) ∷ [])
_ = refl

-- ∂⁺(α⊗β) at dimension 1: α⊗g + f'⊗β   (α first, then β)
_ : chainT true 1 (homs HComp) ≡ ((3 ∷ 8 ∷ []) ∷ (4 ∷ 6 ∷ []) ∷ [])
_ = refl

-- The closed support of T is all nine basis elements of D¹ ⊗ D¹, while
-- its table support misses f⊗g' and f'⊗g (boundaries of atoms only).
private
  len' : TSet → Nat
  len' []       = 0
  len' (_ ∷ xs) = suc (len' xs)

_ : len' (down HComp (fullT (homs HComp))) ≡ 9
_ = refl
_ : memT (2 ∷ 7 ∷ []) (fullT (homs HComp)) ≡ false
_ = refl

------------------------------------------------------------------------
-- Basic operations (all single cohs).

-- composite of 1-cells
comp : Tm → Tm → Tm → Tm → Tm → Tm
comp x y f z g = coh Comp₂ (arr ⋆ (v 0) (v 3)) ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ [] ⟫

-- identity
idc : Tm → Tm
idc x = coh (ctxOf leaf) (arr ⋆ (v 0) (v 0)) ⟪ x ∷ [] ⟫

-- vertical composite of 2-cells α : f ⇒ g, β : g ⇒ h (all x → y)
vcomp : (x y f g α h β : Tm) → Tm
vcomp x y f g α h β =
  coh VComp (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) ⟪ x ∷ y ∷ f ∷ g ∷ α ∷ h ∷ β ∷ [] ⟫

-- f ◁ β : f;g ⇒ f;g'
lw : (x y f z g g' β : Tm) → Tm
lw x y f z g g' β =
  coh LW (arr (arr ⋆ (v 0) (v 3)) (comp (v 0) (v 1) (v 2) (v 3) (v 4))
                                  (comp (v 0) (v 1) (v 2) (v 3) (v 5)))
      ⟪ x ∷ y ∷ f ∷ z ∷ g ∷ g' ∷ β ∷ [] ⟫

-- α ▷ g : f;g ⇒ f';g
rw : (x y f f' α z g : Tm) → Tm
rw x y f f' α z g =
  coh RW (arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                                  (comp (v 0) (v 1) (v 3) (v 5) (v 6)))
      ⟪ x ∷ y ∷ f ∷ f' ∷ α ∷ z ∷ g ∷ [] ⟫

comp-wf  = snd (from-just (infer Comp₂ (comp (v 0) (v 1) (v 2) (v 3) (v 4))))
vcomp-wf = snd (from-just (infer VComp (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))))
lw-wf    = snd (from-just (infer LW (lw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))))
rw-wf    = snd (from-just (infer RW (rw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))))

------------------------------------------------------------------------
-- §3.4: no horizontal composite of 2-cells across objects.
--
-- CaTT's horizontal composite α ⋆ β : f;g ⇒ f';g' over HComp is a
-- (plain CaTT) operation. In L its side condition fails: the
-- composite would be a 2-cell with the support of a 2-dimensional
-- unfolding, so neither case applies.

hcompTy : Ty
hcompTy = arr (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                                  (comp (v 0) (v 1) (v 3) (v 5) (v 7))

_ : graySide HComp (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                                       (comp (v 0) (v 1) (v 3) (v 5) (v 7)) ≡ false
_ = refl

-- …while plain CaTT accepts it.
_ : C.cattSide HComp (arr ⋆ (v 0) (v 5)) (comp (v 0) (v 1) (v 2) (v 5) (v 6))
                                         (comp (v 0) (v 1) (v 3) (v 5) (v 7)) ≡ true
_ = refl

------------------------------------------------------------------------
-- The two whiskered composites both exist.

-- names in HComp
x y f f' α z g g' β : Tm
x = v 0 ; y = v 1 ; f = v 2 ; f' = v 3 ; α = v 4 ; z = v 5 ; g = v 6 ; g' = v 7 ; β = v 8

fg fg' f'g f'g' : Tm
fg   = comp x y f  z g
fg'  = comp x y f  z g'
f'g  = comp x y f' z g
f'g' = comp x y f' z g'

-- (f◁β);(α▷g') : β first, then α
βα : Tm
βα = vcomp x z fg fg' (lw x y f z g g' β) f'g' (rw x y f f' α z g')

-- (α▷g);(f'◁β) : α first, then β
αβ : Tm
αβ = vcomp x z fg f'g (rw x y f f' α z g) f'g' (lw x y f' z g g' β)

Txz : Ty
Txz = arr ⋆ x z

βα-wf : HComp ⊢tm βα ∶ arr Txz fg f'g'
βα-wf = snd (from-just (infer HComp βα))

αβ-wf : HComp ⊢tm αβ ∶ arr Txz fg f'g'
αβ-wf = snd (from-just (infer HComp αβ))

------------------------------------------------------------------------
-- The interchanger: one direction only (§3.1, §3.4).
--
-- Forward: (f◁β);(α▷g')  ⇛  (α▷g);(f'◁β), "outer cell first ⇛ inner
-- cell first" in Mikhail's sense, an operation-case 3-cell.

ichTy ichTy⁻ : Ty
ichTy  = arr (arr Txz fg f'g') βα αβ
ichTy⁻ = arr (arr Txz fg f'g') αβ βα

ich ich⁻ : Tm
ich  = coh HComp ichTy  (idₛ HComp)
ich⁻ = coh HComp ichTy⁻ (idₛ HComp)

ich-wf : HComp ⊢tm ich ∶ ichTy
ich-wf = snd (from-just (infer HComp ich))

-- It is the operation case, not the coherence case.
_ : opCase HComp (arr Txz fg f'g') βα αβ ≡ true
_ = refl
_ : cohCase HComp (arr Txz fg f'g') βα αβ ≡ false
_ = refl

-- The reverse coh is not derivable: its side condition is false, and
-- the coh rule demands it. This is a proof about every context Γ, every
-- substitution and every claimed type.
ich⁻-side : graySide HComp (arr Txz fg f'g') αβ βα ≡ false
ich⁻-side = refl

no-ich⁻ : ∀ {Γ σ B} → ¬ (Γ ⊢tm coh HComp ichTy⁻ σ ∶ B)
no-ich⁻ (coh-wf _ _ _ ok _) = subst T ich⁻-side ok

-- Plain CaTT accepts the reverse too (both are full coherences there).
_ : C.cattSide HComp (arr Txz fg f'g') αβ βα ≡ true
_ = refl
_ : C.cattSide HComp (arr Txz fg f'g') βα αβ ≡ true
_ = refl

------------------------------------------------------------------------
-- Example 1 of the note: a lax transformation as a context variable.
--
-- Read HComp as  ⊤ —x,y→ B —F,G→ C  with an arrow φ : x ⇒ y of B
-- (an element 2-cell) and a transformation α : F ⇒ G. The component
-- α_x is the whiskering x◁α, and the naturality cell at φ is the
-- interchanger, typed only as
--     α_x ; Gφ  ⇛  Fφ ; α_y          (Gφ ∘ α_x ⇛ α_y ∘ Fφ, lax).

module Example1 where
  B⊤ BB Bx By Bφ BC BF BG Bα : Tm
  B⊤ = v 0 ; BB = v 1 ; Bx = v 2 ; By = v 3 ; Bφ = v 4
  BC = v 5 ; BF = v 6 ; BG = v 7 ; Bα = v 8

  α_x α_y Fφ Gφ : Tm
  α_x = lw B⊤ BB Bx BC BF BG Bα
  α_y = lw B⊤ BB By BC BF BG Bα
  Fφ  = rw B⊤ BB Bx By Bφ BC BF
  Gφ  = rw B⊤ BB Bx By Bφ BC BG

  α_x-wf = snd (from-just (infer HComp α_x))

  -- naturality: (α_x ; Gφ) ⇛ (Fφ ; α_y)
  natTy : Ty
  natTy = arr (arr (arr ⋆ B⊤ BC) (comp B⊤ BB Bx BC BF) (comp B⊤ BB By BC BG))
              (vcomp B⊤ BC (comp B⊤ BB Bx BC BF) (comp B⊤ BB Bx BC BG) α_x
                           (comp B⊤ BB By BC BG) Gφ)
              (vcomp B⊤ BC (comp B⊤ BB Bx BC BF) (comp B⊤ BB By BC BF) Fφ
                           (comp B⊤ BB By BC BG) α_y)

  -- This is literally ichTy (same term).
  _ : natTy ≡ ichTy
  _ = refl

------------------------------------------------------------------------
-- Example 2: composing lax transformations.
--
-- Vertical: α : F ⇒ G, α' : G ⇒ G' in one hom is `vcomp` over VComp
-- (vcomp-wf above); associativity and units are coherences in one
-- hom, exactly as in CaTT.

-- x0 y1 f2 g3 a4 h5 b6 k7 c8: three composable 2-cells in one hom.
VComp₃ : Ctx
VComp₃ = ctxOf (node (node (leaf ∷ leaf ∷ leaf ∷ []) ∷ []))

vassocTy : Ty
vassocTy = arr (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7))
  (vcomp (v 0) (v 1) (v 2) (v 5) (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) (v 7) (v 8))
  (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (vcomp (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8)))

vassoc-wf = snd (from-just (infer VComp₃ (coh VComp₃ vassocTy (idₛ VComp₃))))

-- …and it is invertible (the reverse is also a coherence).
_ : cohCase VComp₃ (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 7))
      (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 7) (vcomp (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8)))
      (vcomp (v 0) (v 1) (v 2) (v 5) (vcomp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) (v 7) (v 8))
    ≡ true
_ = refl

-- Horizontal: for α : F ⇒ G : B → C and β : H ⇒ K : C → D (HComp read
-- with B = x, C = y, D = z), the two layerings (βF);(Kα) = βα and
-- (Hα);(βG)… are the terms βα and αβ above, both well typed, related
-- by the interchanger in one direction only.

------------------------------------------------------------------------
-- Inside one hom, two-tier L is plain CaTT: the PR #4 examples.

module InsideAHom where
  open import CaTTExp.Examples as E using ()

  -- identity, composite, associator, left unitor, vertical composite
  _ : is-just (infer E.D₀ (E.id (v 0))) ≡ true
  _ = refl
  _ : is-just (infer E.Comp₂ (E.comp (v 0) (v 1) (v 2) (v 3) (v 4))) ≡ true
  _ = refl
  _ : is-just (infer E.Comp₃ E.assoc) ≡ true
  _ = refl
  _ : is-just (infer E.D₁ E.lunitor) ≡ true
  _ = refl
  _ : is-just (infer E.VComp E.vcomp) ≡ true
  _ = refl

  -- …and the negative ones are still rejected.
  _ : is-just (infer E.D₁ (coh E.D₁ (arr ⋆ (v 1) (v 0)) (idₛ E.D₁))) ≡ false
  _ = refl
  _ : is-just (infer E.Comp₂ (coh E.Comp₂ (arr ⋆ (v 0) (v 1)) (idₛ E.Comp₂))) ≡ false
  _ = refl

  -- The one PR #4 example that composes across objects, horizontal
  -- composition of 2-cells, is exactly what L removes.
  _ : is-just (infer E.HComp E.hcomp) ≡ false
  _ = refl

------------------------------------------------------------------------
-- Suspension. Inside a hom the interchanger of 2-cells is invertible:
-- the suspension of the interchanger, a coh over Σ(ΣD¹ ∨ ΣD¹), is
-- accepted in both directions (coherence case).

mutual
  ΣTy : Ty → Ty
  ΣTy ⋆           = arr ⋆ (v 0) (v 1)
  ΣTy (arr A t u) = arr (ΣTy A) (ΣTm t) (ΣTm u)

  ΣTm : Tm → Tm
  ΣTm (var i)     = var (suc (suc i))
  ΣTm (coh Δ A σ) = coh (ΣCtx Δ) (ΣTy A) (ΣSub σ)
  ΣTm (cst k)     = cst k

  -- the two new objects come first
  ΣSub : Sub → Sub
  ΣSub ⟨⟩       = ⟨⟩ ,ₛ v 0 ,ₛ v 1
  ΣSub (σ ,ₛ t) = ΣSub σ ,ₛ ΣTm t

  ΣCtx : Ctx → Ctx
  ΣCtx ε       = ε ▸ ⋆ ▸ ⋆
  ΣCtx (Γ ▸ A) = ΣCtx Γ ▸ ΣTy A

-- Suspension of a tree-built context is the tree with one more root.
_ : ΣCtx HComp ≡ ctxOf (node (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []) ∷ []))
_ = refl

Σich-wf  = snd (from-just (infer (ΣCtx HComp) (ΣTm ich)))
Σich⁻-wf = snd (from-just (infer (ΣCtx HComp) (ΣTm ich⁻)))

_ : cohCase (ΣCtx HComp) (ΣTy (arr Txz fg f'g')) (ΣTm αβ) (ΣTm βα) ≡ true
_ = refl

-- The suspensions of the other examples stay well typed.
_ : is-just (infer (ΣCtx HComp) (ΣTm βα)) ≡ true
_ = refl
