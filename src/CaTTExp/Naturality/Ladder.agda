------------------------------------------------------------------------
-- The ladder filler one dimension up (ledger C1d, item 2).
--
-- CaTTExp.Naturality.DimOne builds c↑ for a chain composite by
-- stacking squares along the chain and filling the gaps with RC(1).
-- This module runs the same construction one level higher: in the hom
-- between two fixed objects X → Y, the "objects" are 1-cells, the
-- "edges" are 2-cells and the squares are 3-cells. Composition is ∗₁
-- (rwT 1 0), the stack is composed by ∗₂ (rwT 2 0), and whiskering a
-- 3-cell by a 2-cell is rwT 1 1 / lwT 1 1.
--
-- The construction is abstract: the data (copies x⁻_j, x⁺_j, cylinders
-- x↑_j of the objects, copies e⁻_j, e⁺_j and squares e↑_j of the edges)
-- are parameters with typing hypotheses (`LOK`), and so is the gap
-- filler `fl`. `Conn` lists exactly the gaps the construction fills,
-- each with the side condition under which it is used; the filler is
-- well typed (`fill-wf`) given that `fl` is well typed on those gaps.
-- CaTTExp.Naturality.Column instantiates it at the cylinder of a
-- vertical composite of 2-cells, where `fl` is the relative-coherence
-- procedure.
------------------------------------------------------------------------
module CaTTExp.Naturality.Ladder where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.Derived using (tm-ty; ps-wf; Dsk; dsk-ps; dsk-wf; dskSub; sphSub; aL-sph; lenₛ-sph; sc-aL'; lk-top)
open import CaTTExp.DerivedBoundary
open import CaTTExp.GraphFillerTotal.Chains using (_≤_; _<_; z≤n; s≤s; ≤-refl; ≤-step)
open import CaTTExp.GrayCtx.Natural using (dbl; aL)
open import CaTTExp.RCProc using (rc-id)
open import CaTTExp.Naturality.Raw using (rwI; lwI)

------------------------------------------------------------------------
-- Identities in every dimension, from the identity coherence on the
-- disk (CaTTExp.RCProc.rc-id), pulled back.

idCore : Nat → Tm
idCore m = fst (rc-id (snd (ps-wf (dsk-ps m))))

idT : Tm → Ty → Tm
idT t A = idCore (dim A) [ dskSub t A ]tm

idT-wf : ∀ {Γ t A} → Γ ⊢tm t ∶ A → Γ ⊢tm idT t A ∶ arr A t t
idT-wf {Γ} {t} {A} dt = subst (Γ ⊢tm idT t A ∶_) tyEq (tm[] (snd (rc-id (snd (ps-wf (dsk-ps m))))) (dsk-wf dt))
  where
  m = dim A
  σ = dskSub t A
  topσ : var (dbl m) [ σ ]tm ≡ t
  topσ = subst (λ k → lookupₛ (sphSub A ,ₛ t) k ≡ t) (lenₛ-sph A) (lk-top (sphSub A) t)
  tyEq : arr (aL m) (var (dbl m)) (var (dbl m)) [ σ ]ty ≡ arr A t t
  tyEq = cong₂ (λ X y → arr X y y) (trans (Sb.ext-ty (aL m) (sphSub A) t (sc-aL' A)) (aL-sph A)) topσ

------------------------------------------------------------------------
-- The raw construction.

module Raw2 (X Y : Tm) (xm xp xt em ep et : Nat → Tm) (xs es : Nat → Bool)
            (fl : Ty → Tm → Tm → Tm) where
  Base : Ty
  Base = arr ⋆ X Y

  cm cp : Nat → Tm
  cm zero    = idT (xm 0) Base
  cm (suc j) = rwT 1 0 (cm j) (arr Base (xm 0) (xm j)) (xm (suc j)) (em j)
  cp zero    = idT (xp 0) Base
  cp (suc j) = rwT 1 0 (cp j) (arr Base (xp 0) (xp j)) (xp (suc j)) (ep j)

  Aj : Nat → Ty
  Aj j = arr Base (xm 0) (xp j)

  U V : Nat → Tm
  U j = rwI 1 2 (cm j) (arr Base (xm 0) (xm j)) (xp j) (xt j) (xs j)
  V j = lwI 1 2 (xt 0) (xm 0) (cp j) (arr Base (xp 0) (xp j)) (xs 0)

  aE bE : Nat → Tm
  aE j = rwI 1 2 (em j) (arr Base (xm j) (xm (suc j))) (xp (suc j)) (xt (suc j)) (xs (suc j))
  bE j = lwI 1 2 (xt j) (xm j) (ep j) (arr Base (xp j) (xp (suc j))) (xs j)

  CE : Nat → Ty
  CE j = arr (arr Base (xm j) (xp (suc j))) (aE j) (bE j)

  fillA : Nat → Tm → Tm → Tm
  fillA j u v = fl (Aj j) u v

  vc : Nat → Tm → Tm → Tm → Tm → Tm → Tm
  vc j S T Z α β = rwT 2 0 α (arr (Aj j) S T) Z β

  lq : Nat → Tm → Tm
  lq j w = lwT 1 0 (cm j) (xm 0) w (arr Base (xm j) (xp (suc j)))

  rq : Nat → Tm → Tm
  rq j w = rwT 1 0 w (Aj j) (xp (suc j)) (ep j)

  Sq : Nat → Tm
  Sq j = lwT 1 1 (cm j) (xm 0) (et j) (CE j)

  RW : Nat → Tm → Tm → Tm → Tm
  RW j S T α = rwT 1 1 α (arr (Aj j) S T) (xp (suc j)) (ep j)

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

  -- a and b of the composite, given its two copies c⁻, c⁺ (1-cells
  -- X → Y in the hom, i.e. 2-cells xm 0 ⇒ xm m and xp 0 ⇒ xp m).
  ac : Nat → Tm → Tm
  ac m c⁻ = rwI 1 2 c⁻ (arr Base (xm 0) (xm m)) (xp m) (xt m) (xs m)
  bc : Nat → Tm → Tm
  bc m c⁺ = lwI 1 2 (xt 0) (xm 0) c⁺ (arr Base (xp 0) (xp m)) (xs 0)

  fill : Nat → Tm → Tm → Tm
  fill m c⁻ c⁺ = vc m (ac m c⁻) (U m) (bc m c⁺) (fillA m (ac m c⁻) (U m))
                   (vc m (U m) (V m) (bc m c⁺) (H m) (fillA m (V m) (bc m c⁺)))

  -- The gaps the construction fills, each with its side condition.
  data Conn (m : Nat) (c⁻ c⁺ : Tm) : Nat → Tm → Tm → Set where
    g-0 : Conn m c⁻ c⁺ 0 (U 0) (V 0)
    g-1 : ∀ j → suc j ≤ m → es j ≡ true  → Conn m c⁻ c⁺ (suc j) (U (suc j)) (lq j (aE j))
    g-2 : ∀ j → suc j ≤ m → es j ≡ true  → Conn m c⁻ c⁺ (suc j) (lq j (bE j)) (rq j (U j))
    g-3 : ∀ j → suc j ≤ m → Conn m c⁻ c⁺ (suc j) (rq j (V j)) (V (suc j))
    g-n : ∀ j → suc j ≤ m → es j ≡ false → Conn m c⁻ c⁺ (suc j) (U (suc j)) (rq j (U j))
    g-a : Conn m c⁻ c⁺ m (ac m c⁻) (U m)
    g-b : Conn m c⁻ c⁺ m (V m) (bc m c⁺)

------------------------------------------------------------------------
-- Typing.

≤-weak : ∀ {j m} → suc j ≤ m → j ≤ m
≤-weak (s≤s p) = ≤-step p

module Typ2 {Δ : Ctx} {X Y : Tm} {xm xp xt em ep et : Nat → Tm} {xs es : Nat → Bool}
            {fl : Ty → Tm → Tm → Tm} (m : Nat) (c⁻ c⁺ : Tm) where
  open Raw2 X Y xm xp xt em ep et xs es fl

  -- The hypotheses on the data.
  record LOK : Set where
    field
      wX     : Δ ⊢tm X ∶ ⋆
      wY     : Δ ⊢tm Y ∶ ⋆
      tx⁻    : ∀ j → j ≤ m → Δ ⊢tm xm j ∶ Base
      tx⁺    : ∀ j → j ≤ m → Δ ⊢tm xp j ∶ Base
      te⁻    : ∀ j → suc j ≤ m → Δ ⊢tm em j ∶ arr Base (xm j) (xm (suc j))
      te⁺    : ∀ j → suc j ≤ m → Δ ⊢tm ep j ∶ arr Base (xp j) (xp (suc j))
      tx↑    : ∀ j → j ≤ m → xs j ≡ true → Δ ⊢tm xt j ∶ arr Base (xm j) (xp j)
      te↑    : ∀ j → suc j ≤ m → es j ≡ true → Δ ⊢tm et j ∶ CE j
      same-x : ∀ j → j ≤ m → xs j ≡ false → xm j ≡ xp j
      same-e : ∀ j → suc j ≤ m → es j ≡ false → em j ≡ ep j
      up-e   : ∀ j → suc j ≤ m → es j ≡ false → (xs j ≡ false) × (xs (suc j) ≡ false)
      -- the gap filler, on the gaps above
      fl-wf  : ∀ {j u v} → Conn m c⁻ c⁺ j u v → Δ ⊢tm u ∶ Aj j → Δ ⊢tm v ∶ Aj j →
               Δ ⊢tm fillA j u v ∶ arr (Aj j) u v

  module _ (L : LOK) where
    open LOK L

    rw1 : ∀ {c a b z h} → Δ ⊢tm c ∶ arr Base a b → Δ ⊢tm h ∶ arr Base b z →
          Δ ⊢tm rwT 1 0 c (arr Base a b) z h ∶ arr Base a z
    rw1 {c} {a} {b} {z} {h} dc dh =
      subst (Δ ⊢tm rwT 1 0 c (arr Base a b) z h ∶_) (rwT-ty0 1 c (arr Base a b) z h refl) (rwT-wf 1 0 dc refl dh)

    lw1 : ∀ {h x c a b} → Δ ⊢tm h ∶ arr Base x a → Δ ⊢tm c ∶ arr Base a b →
          Δ ⊢tm lwT 1 0 h x c (arr Base a b) ∶ arr Base x b
    lw1 {h} {x} {c} {a} {b} dh dc =
      subst (Δ ⊢tm lwT 1 0 h x c (arr Base a b) ∶_) (lwT-ty0 1 h x c (arr Base a b) refl) (lwT-wf 1 0 dc refl dh)

    cm-wf : ∀ j → j ≤ m → Δ ⊢tm cm j ∶ arr Base (xm 0) (xm j)
    cm-wf zero    p = idT-wf (tx⁻ 0 z≤n)
    cm-wf (suc j) p = rw1 (cm-wf j (≤-weak p)) (te⁻ j p)

    cp-wf : ∀ j → j ≤ m → Δ ⊢tm cp j ∶ arr Base (xp 0) (xp j)
    cp-wf zero    p = idT-wf (tx⁺ 0 z≤n)
    cp-wf (suc j) p = rw1 (cp-wf j (≤-weak p)) (te⁺ j p)

    U-wf : ∀ j → j ≤ m → Δ ⊢tm U j ∶ Aj j
    U-wf j p = go (xs j) refl
      where
      go : ∀ v → xs j ≡ v → Δ ⊢tm rwI 1 2 (cm j) (arr Base (xm 0) (xm j)) (xp j) (xt j) v ∶ Aj j
      go true  e = rw1 (cm-wf j p) (tx↑ j p e)
      go false e = subst (λ y → Δ ⊢tm cm j ∶ arr Base (xm 0) y) (same-x j p e) (cm-wf j p)

    V-wf : ∀ j → j ≤ m → Δ ⊢tm V j ∶ Aj j
    V-wf j p = go (xs 0) refl
      where
      go : ∀ v → xs 0 ≡ v → Δ ⊢tm lwI 1 2 (xt 0) (xm 0) (cp j) (arr Base (xp 0) (xp j)) v ∶ Aj j
      go true  e = lw1 (tx↑ 0 z≤n e) (cp-wf j p)
      go false e = subst (λ y → Δ ⊢tm cp j ∶ arr Base y (xp j)) (sym (same-x 0 z≤n e)) (cp-wf j p)

    vc-wf : ∀ j {S T Z α β} → Δ ⊢tm α ∶ arr (Aj j) S T → Δ ⊢tm β ∶ arr (Aj j) T Z →
            Δ ⊢tm vc j S T Z α β ∶ arr (Aj j) S Z
    vc-wf j {S} {T} {Z} {α} {β} dα dβ =
      subst (Δ ⊢tm vc j S T Z α β ∶_) (rwT-ty0 2 α (arr (Aj j) S T) Z β refl) (rwT-wf 2 0 dα refl dβ)

    sq-wf : ∀ j → suc j ≤ m → es j ≡ true → Δ ⊢tm Sq j ∶ arr (Aj (suc j)) (lq j (aE j)) (lq j (bE j))
    sq-wf j p e =
      subst (Δ ⊢tm Sq j ∶_)
        (trans (lwT-ty 1 0 (cm j) (xm 0) (et j) C' (aE j) (bE j) refl)
               (cong (λ Z → arr Z (lq j (aE j)) (lq j (bE j))) (lwT-ty0 1 (cm j) (xm 0) (aE j) C' refl)))
        (lwT-wf 1 1 (te↑ j p e) refl (cm-wf j (≤-weak p)))
      where C' = arr Base (xm j) (xp (suc j))

    rw-wf : ∀ j → suc j ≤ m → ∀ {S T α} → Δ ⊢tm α ∶ arr (Aj j) S T →
            Δ ⊢tm RW j S T α ∶ arr (Aj (suc j)) (rq j S) (rq j T)
    rw-wf j p {S} {T} {α} dα =
      subst (Δ ⊢tm RW j S T α ∶_)
        (trans (rwT-ty 1 0 α (Aj j) S T (xp (suc j)) (ep j) refl)
               (cong (λ Z → arr Z (rq j S) (rq j T)) (rwT-ty0 1 S (Aj j) (xp (suc j)) (ep j) refl)))
        (rwT-wf 1 1 dα refl (te⁺ j p))

    lq-wf : ∀ j → suc j ≤ m → ∀ {w} → Δ ⊢tm w ∶ arr Base (xm j) (xp (suc j)) → Δ ⊢tm lq j w ∶ Aj (suc j)
    lq-wf j p dw = lw1 (cm-wf j (≤-weak p)) dw

    rq-wf : ∀ j → suc j ≤ m → ∀ {w} → Δ ⊢tm w ∶ Aj j → Δ ⊢tm rq j w ∶ Aj (suc j)
    rq-wf j p dw = rw1 dw (te⁺ j p)

    stepH-wf : ∀ j → suc j ≤ m → ∀ v → es j ≡ v → ∀ {h} → Δ ⊢tm h ∶ arr (Aj j) (U j) (V j) →
               Δ ⊢tm stepH j v h ∶ arr (Aj (suc j)) (U (suc j)) (V (suc j))
    stepH-wf j p true e dh =
      vc-wf (suc j) (fl-wf (g-1 j p e) (U-wf (suc j) p) (lq-wf j p daE))
      (vc-wf (suc j) (sq-wf j p e)
      (vc-wf (suc j) (fl-wf (g-2 j p e) (lq-wf j p dbE) (rq-wf j p (U-wf j (≤-weak p))))
      (vc-wf (suc j) (rw-wf j p dh)
        (fl-wf (g-3 j p) (rq-wf j p (V-wf j (≤-weak p))) (V-wf (suc j) p)))))
      where
      dCE = tm-ty (te↑ j p e)
      daE : Δ ⊢tm aE j ∶ arr Base (xm j) (xp (suc j))
      daE with dCE
      ... | arr-wf da db = da
      dbE : Δ ⊢tm bE j ∶ arr Base (xm j) (xp (suc j))
      dbE with dCE
      ... | arr-wf da db = db
    stepH-wf j p false e dh =
      vc-wf (suc j) (fl-wf (g-n j p e) (U-wf (suc j) p) (rq-wf j p (U-wf j (≤-weak p))))
      (vc-wf (suc j) (rw-wf j p dh)
        (fl-wf (g-3 j p) (rq-wf j p (V-wf j (≤-weak p))) (V-wf (suc j) p)))

    H-wf : ∀ j → j ≤ m → Δ ⊢tm H j ∶ arr (Aj j) (U j) (V j)
    H-wf zero    p = fl-wf g-0 (U-wf 0 z≤n) (V-wf 0 z≤n)
    H-wf (suc j) p = stepH-wf j p (es j) refl (H-wf j (≤-weak p))

    -- The filler, given its two ends typed.
    fill-wf : Δ ⊢tm ac m c⁻ ∶ Aj m → Δ ⊢tm bc m c⁺ ∶ Aj m →
              Δ ⊢tm fill m c⁻ c⁺ ∶ arr (Aj m) (ac m c⁻) (bc m c⁺)
    fill-wf da db =
      vc-wf m (fl-wf g-a da (U-wf m ≤-refl))
        (vc-wf m (H-wf m ≤-refl) (fl-wf g-b (V-wf m ≤-refl) db))
