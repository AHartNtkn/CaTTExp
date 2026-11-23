------------------------------------------------------------------------
-- Naturality fillers for the coherences of dimension 1 (ledger C1d,
-- item 1).
--
-- Every 1-dimensional coherence is over a chain
--
--   Θ_m = (x₀ —e₁→ x₁ —e₂→ … —e_m→ x_m),   c = coh Θ_m (x₀ → x_m) id
--
-- (CaTTExp.GraphFillerTotal.Chains, chain-side). For a datum D on Θ_m
-- landing in Δ, the cylinder c↑ : a_c → b_c with
--
--   a_c = c⁻ ▹ x_m↑          b_c = x₀↑ ◃ c⁺
--
-- (a factor omitted when its variable is unselected) is built by
-- induction along the chain. Write c⁻_j = (… (id ∗ e₁⁻) ∗ …) ∗ e_j⁻
-- and c⁺_j likewise, and
--
--   U_j = c⁻_j ▹ x_j↑ ,    V_j = x₀↑ ◃ c⁺_j     (both x₀⁻ → x_j⁺).
--
-- H_j : U_j → V_j is
--
--   H_0     = fill(U_0, V_0)
--   H_{j+1} = fill(U_{j+1}, c⁻_j ◃ a_e) ; (c⁻_j ◃ e↑) ; fill(c⁻_j ◃ b_e, U_j ▹ e⁺)
--             ; (H_j ▹ e⁺) ; fill(V_j ▹ e⁺, V_{j+1})              (e = e_{j+1} selected)
--   H_{j+1} = fill(U_{j+1}, U_j ▹ e⁺) ; (H_j ▹ e⁺) ; fill(V_j ▹ e⁺, V_{j+1})   (otherwise)
--
-- and c↑ = fill(a_c, U_m) ; H_m ; fill(V_m, b_c). Here `fill` is the
-- discreteness filler fill₁ between 1-cells with the same path
-- (CaTTExp.GraphFillerTotal, total), `;` is vertical composition (the
-- whisker rwT 1 0), and ◃, ▹ are the typed whiskers of
-- CaTTExp.DerivedBoundary. This is Proposition R of
-- notes/relative-coherence.md §4.1 in dimension 1: the squares e↑ are
-- layered, and RC(1) (fill₁) fills the gaps.
--
-- `fill1-wf` proves the term well typed for every valid datum, and
-- `K₁` packages it as a scoped filler family, well typed on every
-- 1-dimensional coherence (`K₁-ok : FillerOK K₁ Dim1`). With
-- CaTTExp.Naturality.Typing this gives the cylinder of every term
-- built from 1-dimensional coherences (`cyl₁-wf`).
------------------------------------------------------------------------
module CaTTExp.Naturality.DimOne where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open Sb using (ScTy; ScTm; ScSub)
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.Derived using (idS; id-wf; id-ty; id-tm; tm-ty; ++-assoc; subst₂; lk-ext; lk-top; T-≡)
open import CaTTExp.DerivedBoundary
open import CaTTExp.GraphFillerTotal using (path; pathCh; fill₁; total; ⋆-var; sub-len; lookupₛ-there₂)
open import CaTTExp.GraphFillerTotal.Chains
  using (chainC; vtx; edge; lookup-vtx; lookup-edge; chainC-wf; chainC-ps; chain-side; len-chain;
         _≤_; _<_; z≤n; s≤s; ≤-refl; ≤-step; <→T; vtx-<; edge-<; dbl)
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Typing using (UpSel; module Hyp; module Main; T-∨-false; ∨-false-l; ∨-false-r)
open import CaTTExp.Naturality.Boundary using (tyK-top; srcK-top; tgtK-top; BaseD; module Typed)
open import CaTTExp.Naturality.Commute using (Scoped)
open import CaTTExp.Naturality.CylCtx using (module VarBd)

------------------------------------------------------------------------
-- Lists.

++-[] : ∀ (xs : List Nat) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

-- The path contributed by an optional whisker.
bp : Bool → Tm → List Nat
bp true  h = path h
bp false h = []

path-rwI : ∀ c a b z h v → path (rwI 0 1 c (arr ⋆ a b) z h v) ≡ path c ++ bp v h
path-rwI c a b z h true  = refl
path-rwI c a b z h false = sym (++-[] (path c))

path-lwI : ∀ h x c a b v → path (lwI 0 1 h x c (arr ⋆ a b) v) ≡ bp v h ++ path c
path-lwI h x c a b true  = refl
path-lwI h x c a b false = refl

------------------------------------------------------------------------
-- The raw construction, for a datum D on Θ_m landing in Δ.

-- The identity 1-cell on an object.
idc : Tm → Tm
idc x = coh (chainC 0) (arr ⋆ (var 0) (var 0)) (⟨⟩ ,ₛ x)

module Raw1 (Δ : Ctx) (D : Datum) where
  -- Copies and cylinders of the objects x_j and the edges e_{j+1}.
  xm xp xt : Nat → Tm
  xm j = lookupₛ (mm D) (vtx j)
  xp j = lookupₛ (mp D) (vtx j)
  xt j = th D (vtx j)

  em ep et : Nat → Tm
  em j = lookupₛ (mm D) (edge (suc j))
  ep j = lookupₛ (mp D) (edge (suc j))
  et j = th D (edge (suc j))

  xs es : Nat → Bool
  xs j = anyL (sel D) (fvTm (var (vtx j)))
  es j = anyL (sel D) (fvTm (var (edge (suc j))))

  -- c⁻_j and c⁺_j.
  cm cp : Nat → Tm
  cm zero    = idc (xm 0)
  cm (suc j) = rwT 0 0 (cm j) (arr ⋆ (xm 0) (xm j)) (xm (suc j)) (em j)
  cp zero    = idc (xp 0)
  cp (suc j) = rwT 0 0 (cp j) (arr ⋆ (xp 0) (xp j)) (xp (suc j)) (ep j)

  Aj : Nat → Ty
  Aj j = arr ⋆ (xm 0) (xp j)

  U V : Nat → Tm
  U j = rwI 0 1 (cm j) (arr ⋆ (xm 0) (xm j)) (xp j) (xt j) (xs j)
  V j = lwI 0 1 (xt 0) (xm 0) (cp j) (arr ⋆ (xp 0) (xp j)) (xs 0)

  -- The boundary of e_{j+1}↑.
  aE bE : Nat → Tm
  aE j = rwI 0 1 (em j) (arr ⋆ (xm j) (xm (suc j))) (xp (suc j)) (xt (suc j)) (xs (suc j))
  bE j = lwI 0 1 (xt j) (xm j) (ep j) (arr ⋆ (xp j) (xp (suc j))) (xs j)

  CE : Nat → Ty
  CE j = arr (arr ⋆ (xm j) (xp (suc j))) (aE j) (bE j)

  fillA : Nat → Tm → Tm → Tm
  fillA j u v = fill₁ Δ u v (Aj j)

  -- Vertical composite of α : S → T and β : T → Z.
  vc : Nat → Tm → Tm → Tm → Tm → Tm → Tm
  vc j S T Z α β = rwT 1 0 α (arr (Aj j) S T) Z β

  -- c⁻_j ◃ (−) on the boundary of e_{j+1}↑, and (−) ▹ e⁺_{j+1}.
  lq : Nat → Tm → Tm
  lq j w = lwT 0 0 (cm j) (xm 0) w (arr ⋆ (xm j) (xp (suc j)))

  rq : Nat → Tm → Tm
  rq j w = rwT 0 0 w (Aj j) (xp (suc j)) (ep j)

  -- The square c⁻_j ◃ e↑ and the whisker α ▹ e⁺.
  Sq : Nat → Tm
  Sq j = lwT 0 1 (cm j) (xm 0) (et j) (CE j)

  RW : Nat → Tm → Tm → Tm → Tm
  RW j S T α = rwT 0 1 α (arr (Aj j) S T) (xp (suc j)) (ep j)

  stepH : Nat → Bool → Tm → Tm
  stepH j true  h =
    vc (suc j) (U (suc j)) (lq j (aE j)) (V (suc j)) (fillA (suc j) (U (suc j)) (lq j (aE j)))
    (vc (suc j) (lq j (aE j)) (lq j (bE j)) (V (suc j)) (Sq j)
    (vc (suc j) (lq j (bE j)) (rq j (U j)) (V (suc j)) (fillA (suc j) (lq j (bE j)) (rq j (U j)))
    (vc (suc j) (rq j (U j)) (rq j (V j)) (V (suc j)) (RW j (U j) (V j) h)
      (fillA (suc j) (rq j (V j)) (V (suc j))))))
  stepH j false h =
    vc (suc j) (U (suc j)) (rq j (U j)) (V (suc j)) (fillA (suc j) (U (suc j)) (rq j (U j)))
    (vc (suc j) (rq j (U j)) (rq j (V j)) (V (suc j)) (RW j (U j) (V j) h)
      (fillA (suc j) (rq j (V j)) (V (suc j))))

  H : Nat → Tm
  H zero    = fillA 0 (U 0) (V 0)
  H (suc j) = stepH j (es j) (H j)

  -- a_c and b_c for c = coh Θ_m (x₀ → x_m) id.
  ac bc : Nat → Tm → Tm
  ac m c = rwI 0 1 (c [ mm D ]tm) (arr ⋆ (xm 0) (xm m)) (xp m) (xt m) (xs m)
  bc m c = lwI 0 1 (xt 0) (xm 0) (c [ mp D ]tm) (arr ⋆ (xp 0) (xp m)) (xs 0)

  -- The filler.
  fill1 : Nat → Tm → Tm
  fill1 m c = vc m (ac m c) (U m) (bc m c) (fillA m (ac m c) (U m))
                (vc m (U m) (V m) (bc m c) (H m) (fillA m (V m) (bc m c)))

------------------------------------------------------------------------
-- Typing, for a valid datum D on Θ_m landing in Δ.

≤-weak : ∀ {j m} → suc j ≤ m → j ≤ m
≤-weak (s≤s p) = ≤-step p

-- The path of a substitution out of a chain: its edges, in order.
pE : Sub → Nat → List Nat
pE σ zero    = []
pE σ (suc j) = pE σ j ++ path (lookupₛ σ (edge (suc j)))

pE-ext : ∀ σ x e k → lenₛ σ ≡ vtx (suc k) → ∀ j → j ≤ k → pE (σ ,ₛ x ,ₛ e) j ≡ pE σ j
pE-ext σ x e k l zero    p = refl
pE-ext σ x e k l (suc j) p =
  cong₂ _++_ (pE-ext σ x e k l j (≤-weak p))
             (cong path (lookupₛ-there₂ σ x e (edge (suc j)) (subst (edge (suc j) <_) (sym l) (edge-< p))))

pathCh-chain : ∀ {Γ σ} k → Γ ⊢sub σ ∶ chainC k → pathCh σ ≡ pE σ k
pathCh-chain zero (,-wf (⟨⟩-wf _) _) = refl
pathCh-chain {σ = (σ ,ₛ x) ,ₛ e} (suc k) (,-wf (,-wf sσ _) _) =
  trans (cong (_++ path e) (pathCh-chain k sσ))
        (cong₂ _++_ (sym (pE-ext σ x e k (sub-len sσ) k ≤-refl)) (cong path (sym lkE)))
  where
  lkE : lookupₛ (σ ,ₛ x ,ₛ e) (edge (suc k)) ≡ e
  lkE = subst (λ n → lookupₛ (σ ,ₛ x ,ₛ e) (suc n) ≡ e) (sub-len sσ) (lk-top (σ ,ₛ x) e)

-- The 1-dimensional coherence over Θ_m.
B₀ : Nat → Ty
B₀ m = arr ⋆ (var 0) (var (vtx m))

c₀ : Nat → Tm
c₀ m = coh (chainC m) (B₀ m) (idS (len (chainC m)))

module Typ1 (K : Filler) {Δ : Ctx} {D : Datum} (m : Nat) (VD : Hyp.ValidD K D (chainC m) Δ) where
  open Cyl K
  open Hyp K
  open ValidD VD
  open Raw1 Δ D

  private
    wΔ : Δ ⊢ctx
    wΔ = Sb.sub-ctx closed vmm
    wC : chainC m ⊢ctx
    wC = chainC-wf m
    lenC : ∀ {i} → i < len (chainC m) → T (i <ℕ len (chainC m))
    lenC = <→T

    vtx<len : ∀ j → j ≤ m → T (vtx j <ℕ len (chainC m))
    vtx<len j p = subst (λ n → T (vtx j <ℕ n)) (sym (len-chain m)) (<→T (vtx-< p))

    edge<len : ∀ j → j < m → T (edge (suc j) <ℕ len (chainC m))
    edge<len j p = subst (λ n → T (edge (suc j) <ℕ n)) (sym (len-chain m)) (<→T (edge-< p))

  -- The pieces of the datum.
  tx⁻ : ∀ j → j ≤ m → Δ ⊢tm xm j ∶ ⋆
  tx⁻ j p = Sb.lookup-sub closed wC (lookup-vtx m j p) vmm

  tx⁺ : ∀ j → j ≤ m → Δ ⊢tm xp j ∶ ⋆
  tx⁺ j p = Sb.lookup-sub closed wC (lookup-vtx m j p) vmp

  te⁻ : ∀ j → j < m → Δ ⊢tm em j ∶ arr ⋆ (xm j) (xm (suc j))
  te⁻ j p = Sb.lookup-sub closed wC (lookup-edge m j p) vmm

  te⁺ : ∀ j → j < m → Δ ⊢tm ep j ∶ arr ⋆ (xp j) (xp (suc j))
  te⁺ j p = Sb.lookup-sub closed wC (lookup-edge m j p) vmp

  tx↑ : ∀ j → j ≤ m → xs j ≡ true → Δ ⊢tm xt j ∶ arr ⋆ (xm j) (xp j)
  tx↑ j p e = vth (vtx j) ⋆ (lookup-vtx m j p) (T-∨-false (subst T (sym e) tt))

  te↑ : ∀ j → j < m → es j ≡ true → Δ ⊢tm et j ∶ CE j
  te↑ j p e = vth (edge (suc j)) _ (lookup-edge m j p) (T-∨-false (subst T (sym e) tt))

  same-x : ∀ j → j ≤ m → xs j ≡ false → xm j ≡ xp j
  same-x j p e = vsame (vtx j) (vtx<len j p) (∨-false-l e)

  same-e : ∀ j → j < m → es j ≡ false → em j ≡ ep j
  same-e j p e = vsame (edge (suc j)) (edge<len j p) (∨-false-l e)

  -- An unselected edge has unselected ends.
  up-e : ∀ j → j < m → es j ≡ false → (xs j ≡ false) × (xs (suc j) ≡ false)
  up-e j p e = cong (_∨ false) (∨-false-l {sel D (vtx j)} u) , ∨-false-r {sel D (vtx j)} u
    where u = vup (edge (suc j)) _ (lookup-edge m j p) (∨-false-l e)

  ----------------------------------------------------------------------
  -- Cells.

  idc-wf : ∀ {x} → Δ ⊢tm x ∶ ⋆ → Δ ⊢tm idc x ∶ arr ⋆ x x
  idc-wf dx = coh-wf (ps (chainC-ps 0)) (chainC-wf 0) (arr-wf v0 v0) tt (,-wf (⟨⟩-wf wΔ) dx)
    where v0 = var-wf (chainC-wf 0) refl

  rw0 : ∀ {c a b z h} → Δ ⊢tm c ∶ arr ⋆ a b → Δ ⊢tm h ∶ arr ⋆ b z → Δ ⊢tm rwT 0 0 c (arr ⋆ a b) z h ∶ arr ⋆ a z
  rw0 {c} {a} {b} {z} {h} dc dh =
    subst (Δ ⊢tm rwT 0 0 c (arr ⋆ a b) z h ∶_) (rwT-ty0 0 c (arr ⋆ a b) z h refl) (rwT-wf 0 0 dc refl dh)

  lw0 : ∀ {h x c a b} → Δ ⊢tm h ∶ arr ⋆ x a → Δ ⊢tm c ∶ arr ⋆ a b → Δ ⊢tm lwT 0 0 h x c (arr ⋆ a b) ∶ arr ⋆ x b
  lw0 {h} {x} {c} {a} {b} dh dc =
    subst (Δ ⊢tm lwT 0 0 h x c (arr ⋆ a b) ∶_) (lwT-ty0 0 h x c (arr ⋆ a b) refl) (lwT-wf 0 0 dc refl dh)

  cm-wf : ∀ j → j ≤ m → Δ ⊢tm cm j ∶ arr ⋆ (xm 0) (xm j)
  cm-wf zero    p = idc-wf (tx⁻ 0 z≤n)
  cm-wf (suc j) p = rw0 (cm-wf j (≤-weak p)) (te⁻ j p)

  cp-wf : ∀ j → j ≤ m → Δ ⊢tm cp j ∶ arr ⋆ (xp 0) (xp j)
  cp-wf zero    p = idc-wf (tx⁺ 0 z≤n)
  cp-wf (suc j) p = rw0 (cp-wf j (≤-weak p)) (te⁺ j p)

  U-wf : ∀ j → j ≤ m → Δ ⊢tm U j ∶ Aj j
  U-wf j p = go (xs j) refl
    where
    go : ∀ v → xs j ≡ v → Δ ⊢tm rwI 0 1 (cm j) (arr ⋆ (xm 0) (xm j)) (xp j) (xt j) v ∶ Aj j
    go true  e = rw0 (cm-wf j p) (tx↑ j p e)
    go false e = subst (λ y → Δ ⊢tm cm j ∶ arr ⋆ (xm 0) y) (same-x j p e) (cm-wf j p)

  V-wf : ∀ j → j ≤ m → Δ ⊢tm V j ∶ Aj j
  V-wf j p = go (xs 0) refl
    where
    go : ∀ v → xs 0 ≡ v → Δ ⊢tm lwI 0 1 (xt 0) (xm 0) (cp j) (arr ⋆ (xp 0) (xp j)) v ∶ Aj j
    go true  e = lw0 (tx↑ 0 z≤n e) (cp-wf j p)
    go false e = subst (λ y → Δ ⊢tm cp j ∶ arr ⋆ y (xp j)) (sym (same-x 0 z≤n e)) (cp-wf j p)

  vc-wf : ∀ j {S T Z α β} → Δ ⊢tm α ∶ arr (Aj j) S T → Δ ⊢tm β ∶ arr (Aj j) T Z →
          Δ ⊢tm vc j S T Z α β ∶ arr (Aj j) S Z
  vc-wf j {S} {T} {Z} {α} {β} dα dβ =
    subst (Δ ⊢tm vc j S T Z α β ∶_) (rwT-ty0 1 α (arr (Aj j) S T) Z β refl) (rwT-wf 1 0 dα refl dβ)

  fl : ∀ {x y u v} → Δ ⊢tm x ∶ ⋆ → Δ ⊢tm y ∶ ⋆ → Δ ⊢tm u ∶ arr ⋆ x y → Δ ⊢tm v ∶ arr ⋆ x y →
       path u ≡ path v → Δ ⊢tm fill₁ Δ u v (arr ⋆ x y) ∶ arr (arr ⋆ x y) u v
  fl dx dy du dv pe with ⋆-var dx refl | ⋆-var dy refl
  ... | a , refl | b , refl = total du dv pe

  fill-wf : ∀ j → j ≤ m → ∀ {u v} → Δ ⊢tm u ∶ Aj j → Δ ⊢tm v ∶ Aj j → path u ≡ path v →
            Δ ⊢tm fillA j u v ∶ arr (Aj j) u v
  fill-wf j p du dv pe = fl (tx⁻ 0 z≤n) (tx⁺ j p) du dv pe

  sq-wf : ∀ j → j < m → es j ≡ true → Δ ⊢tm Sq j ∶ arr (Aj (suc j)) (lq j (aE j)) (lq j (bE j))
  sq-wf j p e =
    subst (Δ ⊢tm Sq j ∶_)
      (trans (lwT-ty 0 0 (cm j) (xm 0) (et j) C' (aE j) (bE j) refl)
             (cong (λ X → arr X (lq j (aE j)) (lq j (bE j))) (lwT-ty0 0 (cm j) (xm 0) (aE j) C' refl)))
      (lwT-wf 0 1 (te↑ j p e) refl (cm-wf j (≤-weak p)))
    where C' = arr ⋆ (xm j) (xp (suc j))

  rw-wf : ∀ j → j < m → ∀ {S T α} → Δ ⊢tm α ∶ arr (Aj j) S T →
          Δ ⊢tm RW j S T α ∶ arr (Aj (suc j)) (rq j S) (rq j T)
  rw-wf j p {S} {T} {α} dα =
    subst (Δ ⊢tm RW j S T α ∶_)
      (trans (rwT-ty 0 0 α (Aj j) S T (xp (suc j)) (ep j) refl)
             (cong (λ X → arr X (rq j S) (rq j T)) (rwT-ty0 0 S (Aj j) (xp (suc j)) (ep j) refl)))
      (rwT-wf 0 1 dα refl (te⁺ j p))

  lq-wf : ∀ j → j < m → ∀ {w} → Δ ⊢tm w ∶ arr ⋆ (xm j) (xp (suc j)) → Δ ⊢tm lq j w ∶ Aj (suc j)
  lq-wf j p dw = lw0 (cm-wf j (≤-weak p)) dw

  rq-wf : ∀ j → j < m → ∀ {w} → Δ ⊢tm w ∶ Aj j → Δ ⊢tm rq j w ∶ Aj (suc j)
  rq-wf j p dw = rw0 dw (te⁺ j p)

  ----------------------------------------------------------------------
  -- Paths of the 1-cells.

  path-UV0 : path (U 0) ≡ path (V 0)
  path-UV0 =
    trans (path-rwI (cm 0) (xm 0) (xm 0) (xp 0) (xt 0) (xs 0))
    (trans (sym (++-[] (bp (xs 0) (xt 0)))) (sym (path-lwI (xt 0) (xm 0) (cp 0) (xp 0) (xp 0) (xs 0))))

  path-S1 : ∀ j → path (U (suc j)) ≡ path (lq j (aE j))
  path-S1 j =
    trans (path-rwI (cm (suc j)) (xm 0) (xm (suc j)) (xp (suc j)) (xt (suc j)) (xs (suc j)))
    (trans (++-assoc (path (cm j)) (path (em j)) (bp (xs (suc j)) (xt (suc j))))
           (cong (path (cm j) ++_) (sym (path-rwI (em j) (xm j) (xm (suc j)) (xp (suc j)) (xt (suc j)) (xs (suc j))))))

  path-S2 : ∀ j → path (lq j (bE j)) ≡ path (rq j (U j))
  path-S2 j =
    trans (cong (path (cm j) ++_) (path-lwI (xt j) (xm j) (ep j) (xp j) (xp (suc j)) (xs j)))
    (trans (sym (++-assoc (path (cm j)) (bp (xs j) (xt j)) (path (ep j))))
           (cong (_++ path (ep j)) (sym (path-rwI (cm j) (xm 0) (xm j) (xp j) (xt j) (xs j)))))

  path-S3 : ∀ j → path (rq j (V j)) ≡ path (V (suc j))
  path-S3 j =
    trans (cong (_++ path (ep j)) (path-lwI (xt 0) (xm 0) (cp j) (xp 0) (xp j) (xs 0)))
    (trans (++-assoc (bp (xs 0) (xt 0)) (path (cp j)) (path (ep j)))
           (sym (path-lwI (xt 0) (xm 0) (cp (suc j)) (xp 0) (xp (suc j)) (xs 0))))

  path-N1 : ∀ j → j < m → es j ≡ false → path (U (suc j)) ≡ path (rq j (U j))
  path-N1 j p e =
    trans (path-rwI (cm (suc j)) (xm 0) (xm (suc j)) (xp (suc j)) (xt (suc j)) (xs (suc j)))
    (trans (cong (λ v → path (cm (suc j)) ++ bp v (xt (suc j))) (snd (up-e j p e)))
    (trans (++-[] (path (cm (suc j))))
    (trans (cong (λ w → path (cm j) ++ path w) (same-e j p e))
           (cong (_++ path (ep j))
              (sym (trans (path-rwI (cm j) (xm 0) (xm j) (xp j) (xt j) (xs j))
                   (trans (cong (λ v → path (cm j) ++ bp v (xt j)) (fst (up-e j p e)))
                          (++-[] (path (cm j))))))))))

  ----------------------------------------------------------------------
  -- H_j : U_j → V_j.

  stepH-wf : ∀ j → j < m → ∀ v → es j ≡ v → ∀ {h} → Δ ⊢tm h ∶ arr (Aj j) (U j) (V j) →
             Δ ⊢tm stepH j v h ∶ arr (Aj (suc j)) (U (suc j)) (V (suc j))
  stepH-wf j p true e dh =
    vc-wf (suc j) (fill-wf (suc j) p (U-wf (suc j) p) (lq-wf j p daE) (path-S1 j))
    (vc-wf (suc j) (sq-wf j p e)
    (vc-wf (suc j) (fill-wf (suc j) p (lq-wf j p dbE) (rq-wf j p (U-wf j (≤-weak p))) (path-S2 j))
    (vc-wf (suc j) (rw-wf j p dh)
      (fill-wf (suc j) p (rq-wf j p (V-wf j (≤-weak p))) (V-wf (suc j) p) (path-S3 j)))))
    where
    dCE = tm-ty (te↑ j p e)
    daE : Δ ⊢tm aE j ∶ arr ⋆ (xm j) (xp (suc j))
    daE with dCE
    ... | arr-wf da db = da
    dbE : Δ ⊢tm bE j ∶ arr ⋆ (xm j) (xp (suc j))
    dbE with dCE
    ... | arr-wf da db = db
  stepH-wf j p false e dh =
    vc-wf (suc j) (fill-wf (suc j) p (U-wf (suc j) p) (rq-wf j p (U-wf j (≤-weak p))) (path-N1 j p e))
    (vc-wf (suc j) (rw-wf j p dh)
      (fill-wf (suc j) p (rq-wf j p (V-wf j (≤-weak p))) (V-wf (suc j) p) (path-S3 j)))

  H-wf : ∀ j → j ≤ m → Δ ⊢tm H j ∶ arr (Aj j) (U j) (V j)
  H-wf zero    p = fill-wf 0 z≤n (U-wf 0 z≤n) (V-wf 0 z≤n) path-UV0
  H-wf (suc j) p = stepH-wf j p (es j) refl (H-wf j (≤-weak p))

  ----------------------------------------------------------------------
  -- The filler, given a_c, b_c typed and the paths of c⁻, c⁺.

  fill1-wf : ∀ c → Δ ⊢tm ac m c ∶ Aj m → Δ ⊢tm bc m c ∶ Aj m →
             path (c [ mm D ]tm) ≡ path (cm m) → path (c [ mp D ]tm) ≡ path (cp m) →
             Δ ⊢tm fill1 m c ∶ arr (Aj m) (ac m c) (bc m c)
  fill1-wf c da db pa pb =
    vc-wf m (fill-wf m ≤-refl da (U-wf m ≤-refl) pA)
      (vc-wf m (H-wf m ≤-refl) (fill-wf m ≤-refl (V-wf m ≤-refl) db pB))
    where
    pA : path (ac m c) ≡ path (U m)
    pA = trans (path-rwI (c [ mm D ]tm) (xm 0) (xm m) (xp m) (xt m) (xs m))
         (trans (cong (_++ bp (xs m) (xt m)) pa) (sym (path-rwI (cm m) (xm 0) (xm m) (xp m) (xt m) (xs m))))
    pB : path (V m) ≡ path (bc m c)
    pB = trans (path-lwI (xt 0) (xm 0) (cp m) (xp 0) (xp m) (xs 0))
         (trans (cong (bp (xs 0) (xt 0) ++_) (sym pb)) (sym (path-lwI (xt 0) (xm 0) (c [ mp D ]tm) (xp 0) (xp m) (xs 0))))

  ----------------------------------------------------------------------
  -- The chain coherence c₀ m: its copies have the paths of c⁻_m, c⁺_m,
  -- and a_c, b_c are typed (CaTTExp.Naturality.Boundary).

  cm-path : ∀ j → path (cm j) ≡ pE (mm D) j
  cm-path zero    = refl
  cm-path (suc j) = cong (_++ path (em j)) (cm-path j)

  cp-path : ∀ j → path (cp j) ≡ pE (mp D) j
  cp-path zero    = refl
  cp-path (suc j) = cong (_++ path (ep j)) (cp-path j)

  private
    idS-path : ∀ σ → Δ ⊢sub σ ∶ chainC m → pathCh (idS (len (chainC m)) ∘ σ) ≡ pE σ m
    idS-path σ sσ =
      trans (cong pathCh (subst (λ n → idS n ∘ σ ≡ σ) (snd (Sb.sub-sc closed sσ)) (idS∘ σ σ (λ _ _ → refl))))
            (pathCh-chain m sσ)

  chain-ok : chainC m ⊢tm c₀ m ∶ B₀ m → Δ ⊢tm fill1 m (c₀ m) ∶ cylTy D (c₀ m) (B₀ m)
  chain-ok dc with cylTy-wf base dc bd
    where
    open Typed K
    base : BaseD D (chainC m) Δ
    base = record { bmm = vmm ; bmp = vmp ; bsame = vsame ; bup = vup }
    bd : CylBd D Δ (B₀ m)
    bd = tt , (λ p → vth 0 ⋆ (lookup-vtx m 0 z≤n) (T-∨-false p))
            , (λ p → vth (vtx m) ⋆ (lookup-vtx m m ≤-refl) (T-∨-false p))
  ... | arr-wf da db =
    fill1-wf (c₀ m) da db (trans (idS-path (mm D) vmm) (sym (cm-path m)))
                         (trans (idS-path (mp D) vmp) (sym (cp-path m)))

------------------------------------------------------------------------
-- The filler family.

-- Decidable scoping, to make the family scoped on every input.
mutual
  scTm? : Nat → Tm → Bool
  scTm? n (var i)     = i <ℕ n
  scTm? n (coh _ _ γ) = scSub? n γ
  scTm? n (cst _)     = true

  scSub? : Nat → Sub → Bool
  scSub? n ⟨⟩       = true
  scSub? n (γ ,ₛ t) = scSub? n γ ∧ scTm? n t

mutual
  sc-sound : ∀ n t → T (scTm? n t) → ScTm n t
  sc-sound n (var i)     p = p
  sc-sound n (coh _ _ γ) p = scs-sound n γ p
  sc-sound n (cst _)     p = tt

  scs-sound : ∀ n γ → T (scSub? n γ) → ScSub n γ
  scs-sound n ⟨⟩       p = tt
  scs-sound n (γ ,ₛ t) p = scs-sound n γ (∧-fst p) , sc-sound n t (∧-snd {scSub? n γ} p)

mutual
  sc-complete : ∀ n t → ScTm n t → scTm? n t ≡ true
  sc-complete n (var i)     p = T-≡ p
  sc-complete n (coh _ _ γ) p = scs-complete n γ p
  sc-complete n (cst _)     p = refl

  scs-complete : ∀ n γ → ScSub n γ → scSub? n γ ≡ true
  scs-complete n ⟨⟩       p       = refl
  scs-complete n (γ ,ₛ t) (p , q) = cong₂ _∧_ (scs-complete n γ p) (sc-complete n t q)

clean : Nat → Tm → Tm
clean n t = if scTm? n t then t else junk

clean-sc : ∀ n t → ScTm n (clean n t)
clean-sc n t = go (scTm? n t) refl
  where
  go : ∀ v → scTm? n t ≡ v → ScTm n (if v then t else junk)
  go true  e = sc-sound n t (subst T (sym e) tt)
  go false e = tt

clean-eq : ∀ n t → ScTm n t → clean n t ≡ t
clean-eq n t p = cong (λ v → if v then t else junk) (sc-complete n t p)

-- The length of a chain.
half : Nat → Nat
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

chainLen : Ctx → Nat
chainLen Q = half (len Q ∸ 1)

chainLen-chain : ∀ k → chainLen (chainC k) ≡ k
chainLen-chain k = trans (cong (λ n → half (n ∸ 1)) (len-chain k)) (go k)
  where
  go : ∀ k → half (dbl k) ≡ k
  go zero    = refl
  go (suc k) = cong suc (go k)

-- The family: the filler over Q↑Y, computed with the cylinder context
-- of the empty family (on chains it does not depend on the family).
K₀ : Filler
K₀ _ _ _ = junk

K₁raw : Ctx → Ty → Sel → Tm
K₁raw Q B Y = Raw1.fill1 (Cyl.cylCtx K₀ Q Y) (Cyl.gen K₀ Y) (chainLen Q) (Cyl.cohId K₀ Q B)

K₁ : Filler
K₁ Q B Y = clean (cnt Y) (K₁raw Q B Y)

K₁-sc : Scoped K₁
K₁-sc Q B Y = clean-sc (cnt Y) (K₁raw Q B Y)

-- The generic data and the cylinder context of a chain do not depend
-- on the family.
module Indep (K K' : Filler) where
  module C = Cyl K
  module C' = Cyl K'

  gm-indep : ∀ Y → C.genMm Y ≡ C'.genMm Y
  gm-indep ◇       = refl
  gm-indep (Y ◂ b) = cong (_,ₛ var (cnt Y)) (gm-indep Y)

  gp-indep : ∀ Y → C.genMp Y ≡ C'.genMp Y
  gp-indep ◇           = refl
  gp-indep (Y ◂ true)  = cong (_,ₛ var (suc (cnt Y))) (gp-indep Y)
  gp-indep (Y ◂ false) = cong (_,ₛ var (cnt Y)) (gp-indep Y)

  gt-indep : ∀ Y → C.genTh Y ≡ C'.genTh Y
  gt-indep ◇       = refl
  gt-indep (Y ◂ b) = cong (_,ₛ var (suc (suc (cnt Y)))) (gt-indep Y)

  gen-indep : ∀ Y → C.gen Y ≡ C'.gen Y
  gen-indep Y = cong₃ (λ a b c → datum a b (selAt Y) (lookupₛ c)) (gm-indep Y) (gp-indep Y) (gt-indep Y)
    where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
            a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
    cong₃ f refl refl refl = refl

  private
    ext : ∀ Q A Y b → C.cylCtx Q Y ≡ C'.cylCtx Q Y →
          C.cylTy (C.gen (Y ◂ true)) (var (len Q)) A ≡ C'.cylTy (C'.gen (Y ◂ true)) (var (len Q)) A →
          C.cylCtx (Q ▸ A) (Y ◂ b) ≡ C'.cylCtx (Q ▸ A) (Y ◂ b)
    ext Q A Y true  e f = go e (gm-indep Y) (gp-indep Y) f
      where
      go : ∀ {Γ Γ' X X' Z Z' T T'} → Γ ≡ Γ' → X ≡ X' → Z ≡ Z' → T ≡ T' →
           Γ ▸ A [ X ]ty ▸ A [ Z ]ty ▸ T ≡ Γ' ▸ A [ X' ]ty ▸ A [ Z' ]ty ▸ T'
      go refl refl refl refl = refl
    ext Q A Y false e f = cong₂ (λ Γ X → Γ ▸ A [ X ]ty) e (gm-indep Y)

  cylCtx-indep : ∀ k Y → C.cylCtx (chainC k) Y ≡ C'.cylCtx (chainC k) Y
  cylCtx-indep zero    ◇           = refl
  cylCtx-indep zero    (Y ◂ b)     =
    ext ε ⋆ Y b refl (cong (λ G → C'.cylTy G (var 0) ⋆) (gen-indep (Y ◂ true)))
  cylCtx-indep (suc k) ◇           = refl
  cylCtx-indep (suc k) (◇ ◂ b)     = ext (chainC k ▸ ⋆) E ◇ b refl
                                         (cong (λ G → C'.cylTy G (var (len (chainC k ▸ ⋆))) E) (gen-indep (◇ ◂ true)))
    where E = arr ⋆ (var (vtx k)) (var (vtx (suc k)))
  cylCtx-indep (suc k) (Y ◂ a ◂ b) =
    ext (chainC k ▸ ⋆) E (Y ◂ a) b
      (ext (chainC k) ⋆ Y a (cylCtx-indep k Y) (cong (λ G → C'.cylTy G (var (len (chainC k))) ⋆) (gen-indep (Y ◂ true))))
      (cong (λ G → C'.cylTy G (var (len (chainC k ▸ ⋆))) E) (gen-indep (Y ◂ a ◂ true)))
    where E = arr ⋆ (var (vtx k)) (var (vtx (suc k)))

------------------------------------------------------------------------
-- The family is well typed on every coherence of dimension 1.

Dim1 : Ctx → Ty → Set
Dim1 _ ⋆                   = ⊥
Dim1 _ (arr ⋆ _ _)         = ⊤
Dim1 _ (arr (arr _ _ _) _ _) = ⊥

private
  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

ok-chain : ∀ {Q s u Y} → Q ⊢ps → Q ⊢ctx → Q ⊢ty arr ⋆ s u → T (cattSide Q ⋆ s u) →
           lenSel Y ≡ len Q → UpSel Q Y →
           Cyl.cylCtx K₁ Q Y ⊢tm K₁ Q (arr ⋆ s u) Y
             ∶ Cyl.cylTy K₁ (Cyl.gen K₁ Y) (Cyl.cohId K₁ Q (arr ⋆ s u)) (arr ⋆ s u)
ok-chain {Y = Y} pQ wQ wB@(arr-wf ds du) side lY upY with ⋆-var ds refl | ⋆-var du refl
... | i , refl | i' , refl with chain-side pQ side
... | k , refl , refl , refl =
  subst (λ t → Δ ⊢tm t ∶ Cyl.cylTy K₁ (Cyl.gen K₁ Y) (c₀ k) (B₀ k)) (sym eqK) typed
  where
  module V1 = VarBd K₁ K₁-sc
  IH = V1.cylCtx-ok (chainC k) Y wQ (V1.chain-good k) lY upY
  Δ = Cyl.cylCtx K₁ (chainC k) Y
  G = Cyl.gen K₁ Y
  module T1 = Typ1 K₁ k (snd IH)
  dc : chainC k ⊢tm c₀ k ∶ B₀ k
  dc = subst (chainC k ⊢tm c₀ k ∶_) (id-ty (len (chainC k)) (B₀ k) (Sb.ty-sc closed wB))
         (coh-wf pQ wQ wB side (id-wf wQ))
  typed : Δ ⊢tm Raw1.fill1 Δ G k (c₀ k) ∶ Cyl.cylTy K₁ G (c₀ k) (B₀ k)
  typed = T1.chain-ok dc
  eqRaw : K₁raw (chainC k) (B₀ k) Y ≡ Raw1.fill1 Δ G k (c₀ k)
  eqRaw = cong₃ (λ Γ G' n → Raw1.fill1 Γ G' n (c₀ k))
            (Indep.cylCtx-indep K₀ K₁ k Y) (Indep.gen-indep K₀ K₁ Y) (chainLen-chain k)
  eqK : K₁ (chainC k) (B₀ k) Y ≡ Raw1.fill1 Δ G k (c₀ k)
  eqK = trans (cong (clean (cnt Y)) eqRaw)
              (clean-eq (cnt Y) _ (subst (λ n → ScTm n (Raw1.fill1 Δ G k (c₀ k))) (V1.len-cylCtx (chainC k) Y lY)
                                     (Sb.tm-sc closed typed)))

K₁-ok : Hyp.FillerOK K₁ Dim1
K₁-ok {A = ⋆}         pQ wQ wB side lY upY anyY g = ok-chain pQ wQ wB side lY upY
K₁-ok {A = arr _ _ _} pQ wQ wB side lY upY anyY ()

-- The cylinder of every term whose coherences are 1-dimensional
-- (in particular of every term of dimension ≤ 1, see `dim1-good`), for
-- every valid datum, with no hypothesis on fillers.
module Cyl₁ = Main K₁ K₁-sc Dim1 K₁-ok

------------------------------------------------------------------------
-- Terms of dimension ≤ 1 only use 1-dimensional coherences.

LowCtx : Ctx → Set
LowCtx ε       = ⊤
LowCtx (Q ▸ A) = LowCtx Q × T (dim A <ℕ 2)

low-chain : ∀ k → LowCtx (chainC k)
low-chain zero    = tt , tt
low-chain (suc k) = (low-chain k , tt) , tt

private
  low-coh : ∀ {Q s u} → Q ⊢ps → Q ⊢ty arr ⋆ s u → T (cattSide Q ⋆ s u) → LowCtx Q
  low-coh pQ (arr-wf ds du) side with ⋆-var ds refl | ⋆-var du refl
  ... | i , refl | i' , refl with chain-side pQ side
  ... | k , refl , _ = low-chain k

open Hyp K₁ using (AllGood; AllGoodS)

mutual
  dim1-good : ∀ {Γ t A} → Γ ⊢tm t ∶ A → T (dim A <ℕ 2) → AllGood Dim1 t
  dim1-good (var-wf _ _) _ = tt
  dim1-good (coh-wf {A = ⋆} pQ wQ wB side sγ) p = tt , dim1-goodS sγ (low-coh pQ wB side)
  dim1-good (coh-wf {A = arr _ _ _} pQ wQ wB side sγ) ()
  dim1-good (cst-wf {()} _ _) _

  dim1-goodS : ∀ {Γ γ Q} → Γ ⊢sub γ ∶ Q → LowCtx Q → AllGoodS Dim1 γ
  dim1-goodS (⟨⟩-wf _)            _        = tt
  dim1-goodS (,-wf {σ = σ} {A = B} sγ dt) (lQ , lB) =
    dim1-goodS sγ lQ , dim1-good dt (subst (λ n → T (n <ℕ 2)) (sym (dim[] B σ)) lB)

-- The theorem: every term of dimension ≤ 1 has a well-typed cylinder,
-- for every valid datum, with no hypothesis on fillers.
cyl₁-wf : ∀ {D Γ Δ t A} → Hyp.ValidD K₁ D Γ Δ → Γ ⊢tm t ∶ A → T (dim A <ℕ 2) →
          T (Cyl.touched K₁ D t) → Δ ⊢tm Cyl.cyl K₁ D t ∶ Cyl.cylTy K₁ D t A
cyl₁-wf V dt p q = Cyl₁.cyl-wf V dt (dim1-good dt p) q
