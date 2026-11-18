------------------------------------------------------------------------
-- SKETCH (exploratory, not a settled design).
--
-- Idea: read CaTT with the ambient ω-category being ωCat, so ⋆-terms
-- are ω-categories, 1-cells are functors, 2-cells lax transformations,
-- and so on. Add, for every well-formed *pure* CaTT context Γ (a finite
-- computad), a closed object ⟦Γ⟧ : ⋆, the free ω-category on Γ; and
-- for every pure substitution Δ ⊢ σ : Γ a closed functor
-- ⟦σ⟧ : ⟦Γ⟧ → ⟦Δ⟧.
--
-- This is realised as an ordinary CaTT signature whose validity side
-- conditions are *pure* CaTT judgments. Shapes are therefore stratified:
-- ⟦_⟧ only accepts pure contexts, never ambient ones that mention ⟦_⟧.
--
-- What the file establishes (by the certified checker):
--  * the ambient theory typechecks, and n-cells of a category C can be
--    represented as ambient maps ⟦Dⁿ⟧ → C;
--  * the source of such an element is a plain CaTT composite with
--    ⟦s⟧ : ⟦Dⁿ⁻¹⟧ → ⟦Dⁿ⟧;
--  * one candidate coh relating ⟦s⟧ ; ⟦id⟧ to ⟦s⟧ is rejected. That no
--    term at all relates them is argued informally (a strict model) in
--    notes/agda-sketch-findings.md, not proved here. See notes/agda-sketch-findings.md.
------------------------------------------------------------------------
module CaTTExp.Sketch.Representables where

open import CaTTExp.Prelude
open import CaTTExp.Signature
import CaTTExp.Pure as P
import CaTTExp.Examples as PE

------------------------------------------------------------------------
-- The ambient signature.

data AmbK : Set where
  rep : P.Ctx → AmbK                         -- ⟦Γ⟧
  fun : P.Ctx → P.Ctx → P.Sub → AmbK         -- ⟦σ⟧ : ⟦Γ⟧ → ⟦Δ⟧, for Δ ⊢ σ : Γ

private
  _==A_ : AmbK → AmbK → Bool
  rep Γ       ==A rep Γ'         = Γ P.==Ctx Γ'
  fun Γ Δ σ   ==A fun Γ' Δ' σ'   = (Γ P.==Ctx Γ') ∧ (Δ P.==Ctx Δ') ∧ (σ P.==Sub σ')
  _           ==A _              = false

  ==A-sound : ∀ k l → T (k ==A l) → k ≡ l
  ==A-sound (rep Γ) (rep Γ') p = cong rep (P.==Ctx-sound Γ Γ' p)
  ==A-sound (fun Γ Δ σ) (fun Γ' Δ' σ') p =
    let q = ∧-snd {Γ P.==Ctx Γ'} p in
    cong₂ (λ X (Y : P.Ctx × P.Sub) → fun X (fst Y) (snd Y))
      (P.==Ctx-sound Γ Γ' (∧-fst p))
      (cong₂ _,_ (P.==Ctx-sound Δ Δ' (∧-fst q))
                 (P.==Sub-sound σ σ' (∧-snd {Δ P.==Ctx Δ'} q)))

  ValidA : AmbK → Set
  ValidA (rep Γ)     = Γ P.⊢ctx
  ValidA (fun Γ Δ σ) = Γ P.⊢ctx × Δ P.⊢ctx × Δ P.⊢sub σ ∶ Γ

  validA? : (k : AmbK) → Maybe (ValidA k)
  validA? (rep Γ)     = P.checkCtx Γ
  validA? (fun Γ Δ σ) =
    P.checkCtx Γ >>= λ wΓ → P.checkCtx Δ >>= λ wΔ →
    P.checkSub Δ wΔ σ Γ >>= λ s → just (wΓ , wΔ , s)

open import CaTTExp.Syntax AmbK as S using ()

tyA : AmbK → S.Ty
tyA (rep Γ)     = S.⋆
tyA (fun Γ Δ σ) = S.arr S.⋆ (S.cst (rep Γ)) (S.cst (rep Δ))

𝔸 : Signature
𝔸 = record
  { K = AmbK ; _==K_ = _==A_ ; ==K-sound = ==A-sound
  ; ty = tyA ; Valid = ValidA ; valid? = validA? }

open Signature 𝔸
open import CaTTExp.Typing 𝔸
open import CaTTExp.Check 𝔸

⟦_⟧ : P.Ctx → Tm
⟦ Γ ⟧ = cst (rep Γ)

------------------------------------------------------------------------
-- Ambient composition of functors, over the ambient copy of Comp₂.

open import CaTTExp.PastingTrees 𝔸 using (ctxOf; node; leaf)

Comp₂ᴬ : Ctx
Comp₂ᴬ = ctxOf (node (leaf ∷ leaf ∷ []))

_⨾_[_,_,_] : Tm → Tm → Tm → Tm → Tm → Tm
f ⨾ g [ x , y , z ] = coh Comp₂ᴬ (arr ⋆ (var 0) (var 3)) (⟨⟩ ,ₛ x ,ₛ y ,ₛ f ,ₛ z ,ₛ g)

------------------------------------------------------------------------
-- Elements. In the ambient context  C : ⋆ , a : ⟦D₁⟧ → C,
-- `a` plays the role of an arrow of C.

ElemCtx : Ctx
ElemCtx = ε ▸ ⋆ ▸ arr ⋆ ⟦ PE.D₁ ⟧ (var 0)

-- The source inclusion ⟦D₀⟧ → ⟦D₁⟧, from the pure substitution
-- D₁ ⊢ ⟨x⟩ : D₀.
⟦s⟧ ⟦t⟧ : Tm
⟦s⟧ = cst (fun PE.D₀ PE.D₁ (P.⟪ P.var 0 ∷ [] ⟫))
⟦t⟧ = cst (fun PE.D₀ PE.D₁ (P.⟪ P.var 1 ∷ [] ⟫))

-- Source and target objects of the element a, as maps ⟦D₀⟧ → C.
src-a tgt-a : Tm
src-a = ⟦s⟧ ⨾ var 1 [ ⟦ PE.D₀ ⟧ , ⟦ PE.D₁ ⟧ , var 0 ]
tgt-a = ⟦t⟧ ⨾ var 1 [ ⟦ PE.D₀ ⟧ , ⟦ PE.D₁ ⟧ , var 0 ]

src-a-wf : ElemCtx ⊢tm src-a ∶ arr ⋆ ⟦ PE.D₀ ⟧ (var 0)
src-a-wf = snd (from-just (infer ElemCtx src-a))

tgt-a-wf : ElemCtx ⊢tm tgt-a ∶ arr ⋆ ⟦ PE.D₀ ⟧ (var 0)
tgt-a-wf = snd (from-just (infer ElemCtx tgt-a))

-- An invalid constant is rejected: D₁ ⊢ ⟨f⟩ : D₀ is ill typed
-- (f is an arrow, not an object), so ⟦that⟧ does not exist.
_ : is-just (infer ElemCtx (cst (fun PE.D₀ PE.D₁ (P.⟪ P.var 2 ∷ [] ⟫)))) ≡ false
_ = refl

------------------------------------------------------------------------
-- Finding: coh cannot relate constants.
--
-- ⟦s⟧ ; ⟦id_{D₁}⟧ and ⟦s⟧ are parallel closed functors ⟦D₀⟧ → ⟦D₁⟧,
-- where ⟦id_{D₁}⟧ is the functor of the identity substitution. They
-- should be related, but nothing provides a cell:
--  * a coh used directly needs a type that mentions its context's
--    variables, and this type mentions none (the test below);
--  * a coh instantiated at these constants only yields laws that hold
--    for *arbitrary* functors (e.g. id(⟦D₁⟧) ; f ⇒ f), and ⟦id_{D₁}⟧ is
--    not syntactically the ambient identity id(⟦D₁⟧).
-- The checker test below only rules out the direct attempt. That no term
-- relates them is an informal argument (see the notes). If it holds,
-- functoriality of ⟦_⟧ (⟦id⟧ ≅ id, ⟦σ ∘ τ⟧ ≅ ⟦τ⟧ ; ⟦σ⟧) needs a new rule.

⟦idD₁⟧ : Tm
⟦idD₁⟧ = cst (fun PE.D₁ PE.D₁ (P.idₛ PE.D₁))

s⨾id : Tm
s⨾id = ⟦s⟧ ⨾ ⟦idD₁⟧ [ ⟦ PE.D₀ ⟧ , ⟦ PE.D₁ ⟧ , ⟦ PE.D₁ ⟧ ]

D₀ᴬ : Ctx
D₀ᴬ = ctxOf leaf

_ : is-just (infer ε (coh D₀ᴬ (arr (arr ⋆ ⟦ PE.D₀ ⟧ ⟦ PE.D₁ ⟧) s⨾id ⟦s⟧) ⟨⟩)) ≡ false
_ = refl

------------------------------------------------------------------------
-- Elements by dimension shift.
--
-- Rather than taking an arrow of C to be a map ⟦D₁⟧ → C, take objects
-- of C to be maps x : ⟦D₀⟧ → C and arrows of C to be ambient 2-cells
-- f : x ⇒ y between them (for lax or pseudo transformations, the
-- hom ω-category Hom(⟦D₀⟧, C) is C again). Then a functor F : C → D
-- acts on f by whiskering, and functoriality and naturality are plain
-- CaTT coherences, as in "Omega-Categories Made Easy". Below we check
-- this, and then check the catch: the same coherences come in both
-- orientations, so the ambient forces naturality cells to be invertible.

1ᶜ : Tm
1ᶜ = ⟦ PE.D₀ ⟧

private
  v : Nat → Tm
  v = var

  sub : List Tm → Sub
  sub ts = go ⟨⟩ ts
    where
    go : Sub → List Tm → Sub
    go σ []       = σ
    go σ (t ∷ ts) = go (σ ,ₛ t) ts

-- Ambient pasting shapes (the same trees as in the pure examples).
-- a0 b1 p2 c3 q4                            (1-cell composition)
Cmp : Ctx
Cmp = ctxOf (node (leaf ∷ leaf ∷ []))
-- a0 b1 p2 q3 α4 r5 β6                      (vertical 2-composition)
VCmp : Ctx
VCmp = ctxOf (node (node (leaf ∷ leaf ∷ []) ∷ []))
-- a0 b1 p2 q3 α4 c5 F6                      (right whiskering)
RWh : Ctx
RWh = ctxOf (node (node (leaf ∷ []) ∷ leaf ∷ []))
-- a0 b1 x2 c3 F4 G5 α6                      (left whiskering)
LWh : Ctx
LWh = ctxOf (node (leaf ∷ node (leaf ∷ []) ∷ []))

cmp : Tm → Tm → Tm → Tm → Tm → Tm
cmp a b p c q = coh Cmp (arr ⋆ (v 0) (v 3)) (sub (a ∷ b ∷ p ∷ c ∷ q ∷ []))

vcmp : (a b p q α r β : Tm) → Tm
vcmp a b p q α r β =
  coh VCmp (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 5)) (sub (a ∷ b ∷ p ∷ q ∷ α ∷ r ∷ β ∷ []))

rwh : (a b p q α c F : Tm) → Tm
rwh a b p q α c F =
  coh RWh (arr (arr ⋆ (v 0) (v 5)) (cmp (v 0) (v 1) (v 2) (v 5) (v 6))
                                   (cmp (v 0) (v 1) (v 3) (v 5) (v 6)))
      (sub (a ∷ b ∷ p ∷ q ∷ α ∷ c ∷ F ∷ []))

lwh : (a b x c F G α : Tm) → Tm
lwh a b x c F G α =
  coh LWh (arr (arr ⋆ (v 0) (v 3)) (cmp (v 0) (v 1) (v 2) (v 3) (v 4))
                                   (cmp (v 0) (v 1) (v 2) (v 3) (v 5)))
      (sub (a ∷ b ∷ x ∷ c ∷ F ∷ G ∷ α ∷ []))

-- Ambient context:  C, D : ⋆ ;  F, G : C → D ;  α : F ⇒ G ;
--                   x, y : ⟦D₀⟧ → C ;  f : x ⇒ y
-- Levels:           C0 D1 F2 G3 α4 x5 y6 f7
Θ : Ctx
Θ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ (v 0) (v 1) ▸ arr ⋆ (v 0) (v 1)
      ▸ arr (arr ⋆ (v 0) (v 1)) (v 2) (v 3)
      ▸ arr ⋆ 1ᶜ (v 0) ▸ arr ⋆ 1ᶜ (v 0)
      ▸ arr (arr ⋆ 1ᶜ (v 0)) (v 5) (v 6)

-- F(f) : F(x) ⇒ F(y) is right whiskering.
Ff : Tm
Ff = rwh 1ᶜ (v 0) (v 5) (v 6) (v 7) (v 1) (v 2)

Ff-wf = snd (from-just (infer Θ Ff))

-- The naturality square of α at f, as a pasting shape
-- (horizontal composite of f and α):  a0 b1 x2 y3 f4 c5 F6 G7 α8.
NatSq : Ctx
NatSq = ctxOf (node (node (leaf ∷ []) ∷ node (leaf ∷ []) ∷ []))

-- F(f) then α_y   versus   α_x then G(f)   (both F x ⇒ G y).
private
  Fx Fy Gx Gy : Tm
  Fx = cmp (v 0) (v 1) (v 2) (v 5) (v 6)
  Fy = cmp (v 0) (v 1) (v 3) (v 5) (v 6)
  Gx = cmp (v 0) (v 1) (v 2) (v 5) (v 7)
  Gy = cmp (v 0) (v 1) (v 3) (v 5) (v 7)
  F⟨f⟩ G⟨f⟩ α⟨x⟩ α⟨y⟩ : Tm
  F⟨f⟩ = rwh (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
  G⟨f⟩ = rwh (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7)
  α⟨x⟩ = lwh (v 0) (v 1) (v 2) (v 5) (v 6) (v 7) (v 8)
  α⟨y⟩ = lwh (v 0) (v 1) (v 3) (v 5) (v 6) (v 7) (v 8)

  top bot : Tm
  top = vcmp (v 0) (v 5) Fx Fy F⟨f⟩ Gy α⟨y⟩
  bot = vcmp (v 0) (v 5) Fx Gx α⟨x⟩ Gy G⟨f⟩

  -- Substitute the shape into Θ: a↦⟦D₀⟧ b↦C x↦x y↦y f↦f c↦D F↦F G↦G α↦α
  intoΘ : Sub
  intoΘ = sub (1ᶜ ∷ v 0 ∷ v 5 ∷ v 6 ∷ v 7 ∷ v 1 ∷ v 2 ∷ v 3 ∷ v 4 ∷ [])

-- The naturality cell, in one orientation …
naturality : Tm
naturality = coh NatSq (arr (arr (arr ⋆ (v 0) (v 5)) Fx Gy) top bot) intoΘ

naturality-wf = snd (from-just (infer Θ naturality))

-- … and in the other. Both are full coherences, so plain CaTT proves
-- that every transformation is natural up to cells in *both*
-- directions (indeed invertible ones). Lax transformations are not:
-- their naturality cells point one way only. So the ambient cannot be
-- "ωCat with lax transformations" read as a plain CaTT model. See
-- notes/agda-sketch-findings.md.
naturality⁻¹ : Tm
naturality⁻¹ = coh NatSq (arr (arr (arr ⋆ (v 0) (v 5)) Fx Gy) bot top) intoΘ

naturality⁻¹-wf = snd (from-just (infer Θ naturality⁻¹))
