------------------------------------------------------------------------
-- Saturation of the `inv` judgment (notes/marking-alternatives.md §3,
-- ledger S17).
--
-- 1. The defect, machine-checked by evaluation of the encoded rules of
--    CaTTExp.Gray.Marks. In the context Γ₁ of an equivalence given by
--    data (x : a → b, y : b → a, l : y;x ⇛ 1_b and r : x;y ⇛ 1_a, with
--    l and r marked inv), the premises of ICaTT's inv-intro hold for x,
--    but `x inv` is not derivable. One dimension up (Γ₂, x a 2-cell of
--    𝒦(T, B) with inverse data, β : F ⇒ G a lax transformation), the
--    lax naturality cell of β at x is invertible in every model but is
--    not derivably inv. With x marked inv it is (INV-fac).
--
-- 2. The proposed repair (notes/marking-alternatives.md §6, item 2): an
--    equation-free evidence layer on top of the judgments.
--      jud           the judgment itself (ICaTT's evidence erased)
--      inv₁, inv₂    ICaTT's inv-intro, for cells of dimension 1 and 2
--      can es        a coh whose arguments at the listed positions are
--                    invertible by the given evidence (ICaTT's can-intro,
--                    over the L rules: the upgraded arguments feed (OP-inv),
--                    (INV-fac) and (INV-obj) through `invC`; only the inv
--                    component is upgraded, so an argument made inv by
--                    evidence does not become ps or ps* and cannot serve as
--                    the ps* factor of (PS-fac). (OBJ-k) is kept.)
--    `checkEv` decides it by structural recursion on the evidence. The
--    evidence `jud` coincides with the judgment by definition
--    (`jud-conservative`, which holds by refl), and the layer fixes both
--    examples. inv-intro checks that the evidence terms s, s′, l, r are
--    well-typed in Γ with the certified checker (`wt`).
--
-- Scope, stated honestly:
--  * inv-intro is encoded for cells of dimension 1 and 2 only (the
--    composite in the unit types is built with `comp` and `vcomp`). The
--    general rule uses the suspended composite and is not encoded.
--  * The term t itself is assumed well-typed, as in `Gray.Marks`; the new
--    terms introduced by evidence are type-checked (`wt`), and their types
--    are then read off syntactically (`typeOf`), which agrees with the
--    derived type on well-typed terms (`typeOf-sound`).
--  * Soundness of the evidence layer (inv-intro is sound for invertibility
--    in every model; can follows from the soundness of the judgment rules)
--    is on paper, notes/marking-alternatives.md §6, item 2. It is not encoded.
--  * Destructors (DES) are still not in the core syntax (ledger E4); the
--    evidence layer therefore has no linv/rinv term formers either.
------------------------------------------------------------------------
module CaTTExp.Gray.MarksSaturation where

open import CaTTExp.Prelude
open import CaTTExp.Gray.Pure
open import CaTTExp.Gray.Marks ∅
open import CaTTExp.Gray.Examples
  using (HComp; ichTy; comp; idc; vcomp; D₁)

v : Nat → Tm
v = var

-- identity 2-cell on f : x → y
id2 : Tm → Tm → Tm → Tm
id2 x y f = coh D₁ (arr (arr ⋆ (v 0) (v 1)) (v 2) (v 2)) ⟪ x ∷ y ∷ f ∷ [] ⟫

-- t is a well-typed term of Γ (certified checker)
wt : Ctx → Tm → Bool
wt Γ t = is-just (checkCtx Γ >>= λ w → inferTm Γ w t)

eqTy : Maybe Ty → Ty → Bool
eqTy (just A) B = A ==Ty B
eqTy nothing  B = false

------------------------------------------------------------------------
-- Evidence and its checker.

data Ev : Set where
  jud  : Ev
  inv₁ : (s s′ l r : Tm) → Ev → Ev → Ev
  inv₂ : (s s′ l r : Tm) → Ev → Ev → Ev
  can  : List (Nat × Ev) → Ev

subList : Sub → List Tm
subList ⟨⟩       = []
subList (γ ,ₛ t) = subList γ ++ (t ∷ [])

nthTm : Nat → List Tm → Maybe Tm
nthTm _       []       = nothing
nthTm zero    (t ∷ _)  = just t
nthTm (suc n) (_ ∷ ts) = nthTm n ts

-- set the inv component at position i
upInv : Nat → List IP → List IP
upInv _       []       = []
upInv zero    (j ∷ js) = ip true (jps j) (jpss j) ∷ js
upInv (suc n) (j ∷ js) = j ∷ upInv n js

mutual
  checkEv : Marks → Ctx → Tm → Ev → Bool
  checkEv ms Γ t jud = (ms , Γ) ⊢ t inv
  checkEv ms Γ t (inv₁ s s′ l r eL eR) = intro₁ ms Γ t s s′ l r (typeOf Γ t) eL eR
  checkEv ms Γ t (inv₂ s s′ l r eL eR) = intro₂ ms Γ t s s′ l r (typeOf Γ t) eL eR
  checkEv ms Γ (coh Θ (arr A t u) γ) (can es) =
    invC Θ A t u (upgrade ms Γ (subList γ) es (judgeSub (fuelOf Γ (coh Θ (arr A t u) γ)) ms Γ γ))
    ∨ objRule ms (just (arr A t u [ γ ]ty))
  checkEv ms Γ _ (can es) = false

  -- ICaTT's inv-intro for t : a → b.
  intro₁ : Marks → Ctx → (t s s′ l r : Tm) → Maybe Ty → Ev → Ev → Bool
  intro₁ ms Γ t s s′ l r (just (arr ⋆ a b)) eL eR =
       wt Γ s ∧ wt Γ s′ ∧ wt Γ l ∧ wt Γ r
     ∧ eqTy (typeOf Γ s)  (arr ⋆ b a)
     ∧ eqTy (typeOf Γ s′) (arr ⋆ b a)
     ∧ eqTy (typeOf Γ l)  (arr (arr ⋆ b b) (comp b a s b t) (idc b))
     ∧ eqTy (typeOf Γ r)  (arr (arr ⋆ a a) (comp a b t a s′) (idc a))
     ∧ checkEv ms Γ l eL ∧ checkEv ms Γ r eR
  intro₁ ms Γ t s s′ l r _ eL eR = false

  -- ICaTT's inv-intro for a 2-cell t : f ⇒ g : X → Y.
  intro₂ : Marks → Ctx → (t s s′ l r : Tm) → Maybe Ty → Ev → Ev → Bool
  intro₂ ms Γ t s s′ l r (just (arr (arr ⋆ X Y) f g)) eL eR =
       wt Γ s ∧ wt Γ s′ ∧ wt Γ l ∧ wt Γ r
     ∧ eqTy (typeOf Γ s)  (arr (arr ⋆ X Y) g f)
     ∧ eqTy (typeOf Γ s′) (arr (arr ⋆ X Y) g f)
     ∧ eqTy (typeOf Γ l)  (arr (arr (arr ⋆ X Y) g g) (vcomp X Y g f s g t) (id2 X Y g))
     ∧ eqTy (typeOf Γ r)  (arr (arr (arr ⋆ X Y) f f) (vcomp X Y f g t f s′) (id2 X Y f))
     ∧ checkEv ms Γ l eL ∧ checkEv ms Γ r eR
  intro₂ ms Γ t s s′ l r _ eL eR = false

  -- upgrade the argument judgments by checked evidence
  upgrade : Marks → Ctx → List Tm → List (Nat × Ev) → List IP → List IP
  upgrade ms Γ ts []             js = js
  upgrade ms Γ ts ((i , e) ∷ es) js = upgrade ms Γ ts es (upAt (nthTm i ts) i e js)
    where
    upAt : Maybe Tm → Nat → Ev → List IP → List IP
    upAt (just a) i e js = if checkEv ms Γ a e then upInv i js else js
    upAt nothing  i e js = js

-- The evidence layer is conservative over the judgment.
jud-conservative : ∀ ms Γ t → checkEv ms Γ t jud ≡ (ms , Γ) ⊢ t inv
jud-conservative ms Γ t = refl

------------------------------------------------------------------------
-- Example 1: an equivalence of objects given by data.
-- Γ₁: a0 b1 x2 : a → b, y3 : b → a, l4 : y;x ⇛ 1_b, r5 : x;y ⇛ 1_a.

a b x y l r : Tm
a = v 0
b = v 1
x = v 2
y = v 3
l = v 4
r = v 5

Γ₁ : Ctx
Γ₁ = ε ▸ ⋆ ▸ ⋆ ▸ arr ⋆ a b ▸ arr ⋆ b a
       ▸ arr (arr ⋆ b b) (comp b a y b x) (idc b)
       ▸ arr (arr ⋆ a a) (comp a b x a y) (idc a)

-- Γ₁ is a well-formed context of two-tier L (certified checker).
_ : is-just (checkCtx Γ₁) ≡ true
_ = refl

ms₁ : Marks
ms₁ = (4 , minv) ∷ (5 , minv) ∷ []

-- The premises of inv-intro hold: l and r are inv …
_ : (ms₁ , Γ₁) ⊢ l inv ≡ true
_ = refl
_ : (ms₁ , Γ₁) ⊢ r inv ≡ true
_ = refl
-- … and the shapes fit (this is `intro₁` with jud evidence for l, r):
_ : checkEv ms₁ Γ₁ x (inv₁ y y l r jud jud) ≡ true
_ = refl

-- The defect: x is not derivably inv, and neither is y.
_ : (ms₁ , Γ₁) ⊢ x inv ≡ false
_ = refl
_ : (ms₁ , Γ₁) ⊢ y inv ≡ false
_ = refl

-- Wrong evidence is rejected: l and r swapped, or y′ = x.
_ : checkEv ms₁ Γ₁ x (inv₁ y y r l jud jud) ≡ false
_ = refl
_ : checkEv ms₁ Γ₁ x (inv₁ x y l r jud jud) ≡ false
_ = refl
-- Evidence for l and r must itself check: without the marks it fails.
_ : checkEv [] Γ₁ x (inv₁ y y l r jud jud) ≡ false
_ = refl

------------------------------------------------------------------------
-- Example 2: lax naturality at a 2-cell that is invertible by data.
-- Γ₂: T0 B1 u2 w3 : T → B, x4 : u ⇒ w, y5 : w ⇒ u,
--     l6 : y;x ⇛ 1_w, r7 : x;y ⇛ 1_u, C8, F9 G10 : B → C, β11 : F ⇒ G.

T₀ B u w x₂ y₂ l₂ r₂ C F G β : Tm
T₀ = v 0
B  = v 1
u  = v 2
w  = v 3
x₂ = v 4
y₂ = v 5
l₂ = v 6
r₂ = v 7
C  = v 8
F  = v 9
G  = v 10
β  = v 11

TB : Ty
TB = arr ⋆ T₀ B

Γ₂ : Ctx
Γ₂ = ε ▸ ⋆ ▸ ⋆ ▸ TB ▸ TB ▸ arr TB u w ▸ arr TB w u
       ▸ arr (arr TB w w) (vcomp T₀ B w u y₂ w x₂) (id2 T₀ B w)
       ▸ arr (arr TB u u) (vcomp T₀ B u w x₂ u y₂) (id2 T₀ B u)
       ▸ ⋆ ▸ arr ⋆ B C ▸ arr ⋆ B C ▸ arr (arr ⋆ B C) F G

_ : is-just (checkCtx Γ₂) ≡ true
_ = refl

ms₂ : Marks
ms₂ = (6 , minv) ∷ (7 , minv) ∷ []

-- β's naturality cell at x: the Gray cell x ⊗ β (x first).
nat : Tm
nat = coh HComp ichTy ⟪ T₀ ∷ B ∷ u ∷ w ∷ x₂ ∷ C ∷ F ∷ G ∷ β ∷ [] ⟫

-- it is a well-typed term of Γ₂
_ : is-just (checkCtx Γ₂ >>= λ wf → inferTm Γ₂ wf nat) ≡ true
_ = refl

-- The defect propagates: the naturality cell is not derivably inv.
_ : (ms₂ , Γ₂) ⊢ nat inv ≡ false
_ = refl

-- Control: with x itself marked inv it is, by (INV-fac).
_ : (((4 , minv) ∷ ms₂) , Γ₂) ⊢ nat inv ≡ true
_ = refl

-- The repair: inv-intro evidence for x (position 4 of HComp), fed to
-- the L rules through `can`, makes the naturality cell invertible.
_ : checkEv ms₂ Γ₂ x₂ (inv₂ y₂ y₂ l₂ r₂ jud jud) ≡ true
_ = refl
_ : checkEv ms₂ Γ₂ nat (can ((4 , inv₂ y₂ y₂ l₂ r₂ jud jud) ∷ [])) ≡ true
_ = refl

-- Evidence for the wrong argument does not help: β (position 8) is not
-- invertible by this data, so the check fails.
_ : checkEv ms₂ Γ₂ nat (can ((8 , inv₂ y₂ y₂ l₂ r₂ jud jud) ∷ [])) ≡ false
_ = refl
