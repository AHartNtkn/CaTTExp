------------------------------------------------------------------------
-- G3 (cylinders preserve the wedge D¹ ∨ D¹) and vertical composition
-- of lax transformations as a substitution
--
--     Γ ⊗ (D¹ ∨ D¹)  ⊢  comp  :  Γ ⊗ D¹       (and the same for D¹ ⊗ Γ).
--
-- Γ ⊗ (D¹ ∨ D¹) is `cyl sd 2 Γ` (the path with two edges i, j).
-- `comp` sends the two ends of the cylinder to copies 0 and 2, and the
-- generator x⊗e to a composite "x⊗(i;j)" of x⊗i and x⊗j, built only
-- from substituted coherences over pasting schemes (associators,
-- naturality of associators, functoriality of whiskering) and the
-- generators. It is defined for globular Γ of dimension ≤ 2.
--
-- As everywhere in GrayCtx, these are raw-syntax constructions; the
-- certified checker establishes that the results are well typed
-- (CaTTExp.GrayCtx.Checks).
------------------------------------------------------------------------
module CaTTExp.GrayCtx.VComp where

open import CaTTExp.Prelude
open import CaTTExp.Pure
open import CaTTExp.GrayCtx.Elab
open import CaTTExp.GrayCtx.Cylinder
open import Agda.Builtin.Nat using (_*_)

-- Substitution from a list of terms, in the order of the target context.
fromList : List Tm → Sub
fromList ts = go ⟨⟩ ts
  where
  go : Sub → List Tm → Sub
  go σ []       = σ
  go σ (t ∷ ts) = go (σ ,ₛ t) ts

mapL : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

------------------------------------------------------------------------
-- G3. With N = len Γ, Γ ⊗ D¹ has copies 0, 1 and one edge block;
-- Γ ⊗ (D¹ ∨ D¹) has copies 0, 1, 2 and edge blocks i, j. The two
-- inclusions Γ ⊗ (D¹ ∨ D¹) ⊢ ι₁, ι₂ : Γ ⊗ D¹ are renamings.

ι₁ ι₂ : Nat → Sub
ι₁ N = fromList (mapL var (upto N ++ mapL (λ x → N + x) (upto N) ++ mapL (λ x → 3 * N + x) (upto N)))
ι₂ N = fromList (mapL var (mapL (λ x → N + x) (upto N) ++ mapL (λ x → 2 * N + x) (upto N)
                            ++ mapL (λ x → 4 * N + x) (upto N)))

------------------------------------------------------------------------
-- Vertical composition.

module Comp (sd : Side) (Γ : Ctx) (Γ' : Ctx) where
  -- Γ' is meant to be cyl sd 2 Γ.
  N = len Γ
  c₀ c₁ c₂ I J : Nat → Tm
  c₀ x = var x
  c₁ x = var (N + x)
  c₂ x = var (2 * N + x)
  I  x = var (3 * N + x)
  J  x = var (4 * N + x)

  _▹'_ _◃'_ : Tm → Tm → Maybe Tm
  c ▹' z = (Γ' ▹ c) z
  z ◃' c = (Γ' ◃ z) c

  vc : List Tm → Maybe Tm
  vc = vcomp Γ'

  -- Pasting schemes used for the 3-dimensional coherences.
  -- α in first / middle / last position of a 1-chain of length 3,
  -- and a vertical pair of 2-cells whiskered on the right / left.
  P-first P-mid P-last P-pairR P-pairL : Tree
  P-first = node (node (leaf ∷ []) ∷ leaf ∷ leaf ∷ [])
  P-mid   = node (leaf ∷ node (leaf ∷ []) ∷ leaf ∷ [])
  P-last  = node (leaf ∷ leaf ∷ node (leaf ∷ []) ∷ [])
  P-pairR = node (node (leaf ∷ leaf ∷ []) ∷ leaf ∷ [])
  P-pairL = node (leaf ∷ node (leaf ∷ leaf ∷ []) ∷ [])

  -- Functoriality of whiskering:  (β▹h);(γ▹h) ⇒ (β;γ)▹h  and back,
  -- h◃β ; h◃γ ⇒ h◃(β;γ) and back.
  funcR funcL : Bool → Tm → Tm → Tm → Maybe Tm
  funcR dir β γ h = cohT Γ' P-pairR (λ P →
      rw F P (var 4) (var 8) >>= λ βh → rw F P (var 6) (var 8) >>= λ γh →
      vcomp P (βh ∷ γh ∷ []) >>= λ l →
      vcomp P (var 4 ∷ var 6 ∷ []) >>= λ βγ → rw F P βγ (var 8) >>= λ r →
      just (if dir then (l , r) else (r , l)))
    (β ∷ γ ∷ h ∷ [])
  funcL dir h β γ = cohT Γ' P-pairL (λ P →
      lw F P (var 2) (var 6) >>= λ hβ → lw F P (var 2) (var 8) >>= λ hγ →
      vcomp P (hβ ∷ hγ ∷ []) >>= λ l →
      vcomp P (var 6 ∷ var 8 ∷ []) >>= λ βγ → lw F P (var 2) βγ >>= λ r →
      just (if dir then (l , r) else (r , l)))
    (h ∷ β ∷ γ ∷ [])

  -- Naturality of the associator (and of its inverse) in each argument.
  -- In P-first: f=2 g=3 α=4 h=6 k=8.  P-mid: u=2 f=4 g=5 α=6 v=8.
  -- P-last: u=2 v=4 f=6 g=7 α=8.
  -- `inv = false` uses assoc : (a;b);c ⇒ a;(b;c), `inv = true` uses assoc⁻.
  natFirst natMid natLast : Bool → Tm → Tm → Tm → Maybe Tm
  natFirst inv α h k = cohT Γ' P-first (λ P →
      A P (var 2) (var 6) (var 8) >>= λ Af → A P (var 3) (var 6) (var 8) >>= λ Ag →
      vcomp P (var 6 ∷ var 8 ∷ []) >>= λ hk → rw F P (var 4) hk >>= λ αhk →
      rw F P (var 4) (var 6) >>= λ αh → rw F P αh (var 8) >>= λ αhk' →
      if inv
      then (vcomp P (αhk ∷ Ag ∷ []) >>= λ l → vcomp P (Af ∷ αhk' ∷ []) >>= λ r → just (l , r))
      else (vcomp P (Af ∷ αhk ∷ []) >>= λ l → vcomp P (αhk' ∷ Ag ∷ []) >>= λ r → just (l , r)))
    (α ∷ h ∷ k ∷ [])
    where A = if inv then assoc⁻ else assoc
  natMid inv u α v = cohT Γ' P-mid (λ P →
      A P (var 2) (var 4) (var 8) >>= λ Af → A P (var 2) (var 5) (var 8) >>= λ Ag →
      lw F P (var 2) (var 6) >>= λ uα → rw F P uα (var 8) >>= λ uα-v →
      rw F P (var 6) (var 8) >>= λ αv → lw F P (var 2) αv >>= λ u-αv →
      if inv
      then (vcomp P (Af ∷ uα-v ∷ []) >>= λ l → vcomp P (u-αv ∷ Ag ∷ []) >>= λ r → just (l , r))
      else (vcomp P (Af ∷ u-αv ∷ []) >>= λ l → vcomp P (uα-v ∷ Ag ∷ []) >>= λ r → just (r , l)))
    (u ∷ α ∷ v ∷ [])
    where A = if inv then assoc⁻ else assoc
  natLast inv u v α = cohT Γ' P-last (λ P →
      A P (var 2) (var 4) (var 6) >>= λ Af → A P (var 2) (var 4) (var 7) >>= λ Ag →
      lw F P (var 4) (var 8) >>= λ vα → lw F P (var 2) vα >>= λ u-vα →
      vcomp P (var 2 ∷ var 4 ∷ []) >>= λ uv → lw F P uv (var 8) >>= λ uv-α →
      if inv
      then (vcomp P (u-vα ∷ Ag ∷ []) >>= λ l → vcomp P (Af ∷ uv-α ∷ []) >>= λ r → just (l , r))
      else (vcomp P (Af ∷ u-vα ∷ []) >>= λ l → vcomp P (uv-α ∷ Ag ∷ []) >>= λ r → just (l , r)))
    (u ∷ v ∷ α ∷ [])
    where A = if inv then assoc⁻ else assoc

  private
    splitAt : Nat → List Tm → List Tm × List Tm
    splitAt zero    xs       = [] , xs
    splitAt (suc n) []       = [] , []
    splitAt (suc n) (x ∷ xs) = let r = splitAt n xs in (x ∷ fst r) , snd r

  -- Rewrite the segment of length l at position k of a chain by Φ.
  at : List Tm → Nat → Nat → Tm → List Tm → Maybe (List Tm × Tm)
  at ch k l Φ seg' =
    let p = splitAt k ch ; q = splitAt l (snd p) in
    stepAt Γ' (fst p) (fst q) (snd q) Φ seg'

  asVar : Tm → Maybe Nat
  asVar (var n) = just n
  asVar _       = nothing

  -- The composite of a 1-cell f : x → y over i;j.
  comp1 : Nat → Maybe (List Tm)
  comp1 f = srcOf Γ (var f) >>= asVar >>= λ x → tgtOf Γ (var f) >>= asVar >>= λ y → go sd x y
    where
    go : Side → Nat → Nat → Maybe (List Tm)
    -- f⊗(i;j) : (xᵢ;xⱼ);f₂ ⇒ f₀;(yᵢ;yⱼ)
    go right x y =
      let F = f in
      assoc Γ' (I x) (J x) (c₂ F) >>= λ a₁ → (I x ◃' J F) >>= λ w₁ →
      assoc⁻ Γ' (I x) (c₁ F) (J y) >>= λ a₂ → (I F ▹' J y) >>= λ w₂ →
      assoc Γ' (c₀ F) (I y) (J y) >>= λ a₃ → just (a₁ ∷ w₁ ∷ a₂ ∷ w₂ ∷ a₃ ∷ [])
    -- (i;j)⊗f : f₀;(yᵢ;yⱼ) ⇒ (xᵢ;xⱼ);f₂
    go left x y =
      let F = f in
      assoc⁻ Γ' (c₀ F) (I y) (J y) >>= λ a₁ → (I F ▹' J y) >>= λ w₁ →
      assoc Γ' (I x) (c₁ F) (J y) >>= λ a₂ → (I x ◃' J F) >>= λ w₂ →
      assoc⁻ Γ' (I x) (J x) (c₂ F) >>= λ a₃ → just (a₁ ∷ w₁ ∷ a₂ ∷ w₂ ∷ a₃ ∷ [])

  -- The composite of a 2-cell α : f ⇒ g over i;j: a 3-cell, as a
  -- vertical composite of nine rewriting steps (notes/gray-cylinders.md §4).
  comp2 : Nat → Maybe Tm
  comp2 α =
    srcOf Γ (var α) >>= asVar >>= λ f → tgtOf Γ (var α) >>= asVar >>= λ g →
    srcOf Γ (var f) >>= asVar >>= λ x → tgtOf Γ (var f) >>= asVar >>= λ y →
    comp1 f >>= λ Fs → comp1 g >>= λ Gs →
    vc (I x ∷ J x ∷ []) >>= λ X → vc (I y ∷ J y ∷ []) >>= λ Y →
    go sd f g x y Fs Gs X Y
    where
    go : Side → Nat → Nat → Nat → Nat → List Tm → List Tm → Tm → Tm → Maybe Tm
    go right f g x y Fs Gs X Y =
      (c₀ α ▹' Y) >>= λ W →
      -- start: vcomp[vcomp Fs, W] ⇒ flat
      regroup false Γ' [] Fs (W ∷ []) >>= λ r₀ →
      let C₀ = Fs ++ (W ∷ []) in
      -- 1: [A3f, α₀▹Y] ⇒ [(α₀▹yᵢ)▹yⱼ, A3g]
      natFirst false (c₀ α) (I y) (J y) >>= λ Φ₁ →
      (c₀ α ▹' I y) >>= λ α₀yᵢ → (α₀yᵢ ▹' J y) >>= λ α₀yᵢyⱼ →
      assoc Γ' (c₀ g) (I y) (J y) >>= λ A3g →
      at C₀ 4 2 Φ₁ (α₀yᵢyⱼ ∷ A3g ∷ []) >>= λ s₁ →
      -- 2: [fᵢ▹yⱼ, (α₀▹yᵢ)▹yⱼ] ⇒ [Sᵢ▹yⱼ]
      funcR true (I f) α₀yᵢ (J y) >>= λ Φ₂ →
      vc (I f ∷ α₀yᵢ ∷ []) >>= λ Sᵢ → (Sᵢ ▹' J y) >>= λ Sᵢyⱼ →
      at (fst s₁) 3 2 Φ₂ (Sᵢyⱼ ∷ []) >>= λ s₂ →
      -- 3: αᵢ ▹ yⱼ
      (I α ▹' J y) >>= λ Φ₃ →
      (I x ◃' c₁ α) >>= λ xᵢα₁ → vc (xᵢα₁ ∷ I g ∷ []) >>= λ Tᵢ →
      (Tᵢ ▹' J y) >>= λ Tᵢyⱼ →
      at (fst s₂) 3 1 Φ₃ (Tᵢyⱼ ∷ []) >>= λ s₃ →
      -- 4: [Tᵢ▹yⱼ] ⇒ [(xᵢ◃α₁)▹yⱼ, gᵢ▹yⱼ]
      funcR false xᵢα₁ (I g) (J y) >>= λ Φ₄ →
      (xᵢα₁ ▹' J y) >>= λ xᵢα₁yⱼ → (I g ▹' J y) >>= λ gᵢyⱼ →
      at (fst s₃) 3 1 Φ₄ (xᵢα₁yⱼ ∷ gᵢyⱼ ∷ []) >>= λ s₄ →
      -- 5: [A2f, (xᵢ◃α₁)▹yⱼ] ⇒ [xᵢ◃(α₁▹yⱼ), A2g]
      natMid true (I x) (c₁ α) (J y) >>= λ Φ₅ →
      (c₁ α ▹' J y) >>= λ α₁yⱼ → (I x ◃' α₁yⱼ) >>= λ xᵢα₁yⱼ' →
      assoc⁻ Γ' (I x) (c₁ g) (J y) >>= λ A2g →
      at (fst s₄) 2 2 Φ₅ (xᵢα₁yⱼ' ∷ A2g ∷ []) >>= λ s₅ →
      -- 6: [xᵢ◃fⱼ, xᵢ◃(α₁▹yⱼ)] ⇒ [xᵢ◃Sⱼ]
      funcL true (I x) (J f) α₁yⱼ >>= λ Φ₆ →
      vc (J f ∷ α₁yⱼ ∷ []) >>= λ Sⱼ → (I x ◃' Sⱼ) >>= λ xᵢSⱼ →
      at (fst s₅) 1 2 Φ₆ (xᵢSⱼ ∷ []) >>= λ s₆ →
      -- 7: xᵢ ◃ αⱼ
      (I x ◃' J α) >>= λ Φ₇ →
      (J x ◃' c₂ α) >>= λ xⱼα₂ → vc (xⱼα₂ ∷ J g ∷ []) >>= λ Tⱼ →
      (I x ◃' Tⱼ) >>= λ xᵢTⱼ →
      at (fst s₆) 1 1 Φ₇ (xᵢTⱼ ∷ []) >>= λ s₇ →
      -- 8: [xᵢ◃Tⱼ] ⇒ [xᵢ◃(xⱼ◃α₂), xᵢ◃gⱼ]
      funcL false (I x) xⱼα₂ (J g) >>= λ Φ₈ →
      (I x ◃' xⱼα₂) >>= λ xᵢxⱼα₂ → (I x ◃' J g) >>= λ xᵢgⱼ →
      at (fst s₇) 1 1 Φ₈ (xᵢxⱼα₂ ∷ xᵢgⱼ ∷ []) >>= λ s₈ →
      -- 9: [A1f, xᵢ◃(xⱼ◃α₂)] ⇒ [X◃α₂, A1g]
      natLast false (I x) (J x) (c₂ α) >>= λ Φ₉ →
      (X ◃' c₂ α) >>= λ Xα₂ →
      assoc Γ' (I x) (J x) (c₂ g) >>= λ A1g →
      at (fst s₈) 0 2 Φ₉ (Xα₂ ∷ A1g ∷ []) >>= λ s₉ →
      -- end: flat ⇒ vcomp[X◃α₂, vcomp Gs]
      regroup true Γ' (Xα₂ ∷ []) Gs [] >>= λ r₁₀ →
      vc (r₀ ∷ snd s₁ ∷ snd s₂ ∷ snd s₃ ∷ snd s₄ ∷ snd s₅ ∷ snd s₆ ∷ snd s₇ ∷ snd s₈ ∷ snd s₉ ∷ r₁₀ ∷ [])
    go left f g x y Fs Gs X Y =
      (c₀ α ▹' Y) >>= λ W →
      regroup false Γ' (W ∷ []) Gs [] >>= λ r₀ →
      let C₀ = W ∷ Gs in
      -- 1: [α₀▹Y, B1g] ⇒ [B1f, (α₀▹yᵢ)▹yⱼ]
      natFirst true (c₀ α) (I y) (J y) >>= λ Φ₁ →
      (c₀ α ▹' I y) >>= λ α₀yᵢ → (α₀yᵢ ▹' J y) >>= λ α₀yᵢyⱼ →
      assoc⁻ Γ' (c₀ f) (I y) (J y) >>= λ B1f →
      at C₀ 0 2 Φ₁ (B1f ∷ α₀yᵢyⱼ ∷ []) >>= λ s₁ →
      -- 2: [(α₀▹yᵢ)▹yⱼ, gᵢ▹yⱼ] ⇒ [S′ᵢ▹yⱼ]
      funcR true α₀yᵢ (I g) (J y) >>= λ Φ₂ →
      vc (α₀yᵢ ∷ I g ∷ []) >>= λ Sᵢ → (Sᵢ ▹' J y) >>= λ Sᵢyⱼ →
      at (fst s₁) 1 2 Φ₂ (Sᵢyⱼ ∷ []) >>= λ s₂ →
      -- 3: αᵢ ▹ yⱼ
      (I α ▹' J y) >>= λ Φ₃ →
      (I x ◃' c₁ α) >>= λ xᵢα₁ → vc (I f ∷ xᵢα₁ ∷ []) >>= λ Tᵢ →
      (Tᵢ ▹' J y) >>= λ Tᵢyⱼ →
      at (fst s₂) 1 1 Φ₃ (Tᵢyⱼ ∷ []) >>= λ s₃ →
      -- 4: [T′ᵢ▹yⱼ] ⇒ [fᵢ▹yⱼ, (xᵢ◃α₁)▹yⱼ]
      funcR false (I f) xᵢα₁ (J y) >>= λ Φ₄ →
      (I f ▹' J y) >>= λ fᵢyⱼ → (xᵢα₁ ▹' J y) >>= λ xᵢα₁yⱼ →
      at (fst s₃) 1 1 Φ₄ (fᵢyⱼ ∷ xᵢα₁yⱼ ∷ []) >>= λ s₄ →
      -- 5: [(xᵢ◃α₁)▹yⱼ, B2g] ⇒ [B2f, xᵢ◃(α₁▹yⱼ)]
      natMid false (I x) (c₁ α) (J y) >>= λ Φ₅ →
      (c₁ α ▹' J y) >>= λ α₁yⱼ → (I x ◃' α₁yⱼ) >>= λ xᵢα₁yⱼ' →
      assoc Γ' (I x) (c₁ f) (J y) >>= λ B2f →
      at (fst s₄) 2 2 Φ₅ (B2f ∷ xᵢα₁yⱼ' ∷ []) >>= λ s₅ →
      -- 6: [xᵢ◃(α₁▹yⱼ), xᵢ◃gⱼ] ⇒ [xᵢ◃S′ⱼ]
      funcL true (I x) α₁yⱼ (J g) >>= λ Φ₆ →
      vc (α₁yⱼ ∷ J g ∷ []) >>= λ Sⱼ → (I x ◃' Sⱼ) >>= λ xᵢSⱼ →
      at (fst s₅) 3 2 Φ₆ (xᵢSⱼ ∷ []) >>= λ s₆ →
      -- 7: xᵢ ◃ αⱼ
      (I x ◃' J α) >>= λ Φ₇ →
      (J x ◃' c₂ α) >>= λ xⱼα₂ → vc (J f ∷ xⱼα₂ ∷ []) >>= λ Tⱼ →
      (I x ◃' Tⱼ) >>= λ xᵢTⱼ →
      at (fst s₆) 3 1 Φ₇ (xᵢTⱼ ∷ []) >>= λ s₇ →
      -- 8: [xᵢ◃T′ⱼ] ⇒ [xᵢ◃fⱼ, xᵢ◃(xⱼ◃α₂)]
      funcL false (I x) (J f) xⱼα₂ >>= λ Φ₈ →
      (I x ◃' J f) >>= λ xᵢfⱼ → (I x ◃' xⱼα₂) >>= λ xᵢxⱼα₂ →
      at (fst s₇) 3 1 Φ₈ (xᵢfⱼ ∷ xᵢxⱼα₂ ∷ []) >>= λ s₈ →
      -- 9: [xᵢ◃(xⱼ◃α₂), B3g] ⇒ [B3f, X◃α₂]
      natLast true (I x) (J x) (c₂ α) >>= λ Φ₉ →
      (X ◃' c₂ α) >>= λ Xα₂ →
      assoc⁻ Γ' (I x) (J x) (c₂ f) >>= λ B3f →
      at (fst s₈) 4 2 Φ₉ (B3f ∷ Xα₂ ∷ []) >>= λ s₉ →
      regroup true Γ' [] Fs (Xα₂ ∷ []) >>= λ r₁₀ →
      vc (r₀ ∷ snd s₁ ∷ snd s₂ ∷ snd s₃ ∷ snd s₄ ∷ snd s₅ ∷ snd s₆ ∷ snd s₇ ∷ snd s₈ ∷ snd s₉ ∷ r₁₀ ∷ [])

  -- The image of the cylinder generator of x.
  compGen : Nat → Maybe Tm
  compGen x = lookup Γ x >>= λ where
    ⋆ → vc (I x ∷ J x ∷ [])
    (arr ⋆ _ _) → comp1 x >>= vc
    (arr (arr ⋆ _ _) _ _) → comp2 x
    _ → nothing

  compSub : Maybe Sub
  compSub = mapM compGen (upto N) >>= λ gens →
    just (fromList (mapL c₀ (upto N) ++ mapL c₂ (upto N) ++ gens))

compSub : Side → Ctx → Maybe (Ctx × Sub)
compSub sd Γ = cyl sd 2 Γ >>= λ Γ' → Comp.compSub sd Γ Γ' >>= λ σ → just (Γ' , σ)
