------------------------------------------------------------------------
-- The cylinder of a vertical composite of 2-cells (ledger C1d, item 2).
--
-- The column Q_m = Σ Θ_m is the suspension of the chain: two objects
-- x, y, 1-cells f_0, …, f_m : x → y and 2-cells α_j : f_{j−1} ⇒ f_j.
-- For a valid cylinder datum D on Q_m landing in Δ, the hom between x⁻
-- and y⁺ carries a ladder (CaTTExp.Naturality.Ladder):
--
--   objects   f_j⁻ ▹ y↑  and  x↑ ◃ f_j⁺       (P 1 f_j, L 1 f_j)
--   rungs     f_j↑                            (θ of f_j)
--   edges     α_j⁻ ▹ y↑  and  x↑ ◃ α_j⁺       (P 1 α_j, L 1 α_j)
--   squares   α_j↑                            (θ of α_j)
--
-- These are exactly the pieces of Naturality.Raw's boundary cells, so
-- the ladder's ends are a_c and b_c of any 2-cell c : f_0 ⇒ f_m over
-- Q_m, and `col-ok` types the ladder filler as c↑ : a_c → b_c.
--
-- The gaps of the ladder are filled by the relative-coherence
-- procedure (`General.solve`). `col-ok` is CONDITIONAL on rcS answering
-- each gap the construction uses (`ColRC`). When c is the vertical
-- composite, each gap should relate two 2-cells with the same strict
-- image (they differ by reassociation and identities), so that the
-- planned Theorem A (`rcS-thmA`, with Key2Ctx) discharges them. Neither
-- the strict-image equalities nor the discharge is proved here.
------------------------------------------------------------------------
module CaTTExp.Naturality.Column where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.PureMetatheory using (closed)
open import CaTTExp.Suspension ∅ using (Σctx; Σty; Σtm; S; lookupΣ; lookupΣ-N; lookupΣ-S)
open import CaTTExp.GraphFillerTotal.Chains
  using (chainC; vtx; edge; lookup-vtx; lookup-edge; _≤_; _<_; z≤n; s≤s; ≤-refl)
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Typing using (module Hyp; T-∨-false; ∨-false-l; ∨-false-r)
open import CaTTExp.Naturality.Boundary using (BaseD; module Typed; module Shape)
open import CaTTExp.Naturality.Ladder using (module Raw2; module Typ2)
open import CaTTExp.Naturality.General using (solve; solve-ok; RCAt)

-- The column and its cells.
colC : Nat → Ctx
colC m = Σctx (chainC m)

Af : Ty
Af = arr ⋆ (var 0) (var 1)

fv av : Nat → Nat
fv j = S (vtx j)
av j = S (edge (suc j))

Aα : Nat → Ty
Aα j = arr Af (var (fv j)) (var (fv (suc j)))

lk-f : ∀ m j → j ≤ m → lookup (colC m) (fv j) ≡ just Af
lk-f m j p = lookupΣ (chainC m) (vtx j) (lookup-vtx m j p)

lk-a : ∀ m j → j < m → lookup (colC m) (av j) ≡ just (Aα j)
lk-a m j p = lookupΣ (chainC m) (edge (suc j)) (lookup-edge m j p)

-- The 2-cell type f_0 ⇒ f_m.
Bc : Nat → Ty
Bc m = arr Af (var (fv 0)) (var (fv m))

module Col (K : Filler) {Δ : Ctx} {D : Datum} (m : Nat) (wQ : colC m ⊢ctx)
           (VD : Hyp.ValidD K D (colC m) Δ) where
  open Cyl K
  open Hyp K using (module ValidD)
  open ValidD VD
  open Typed K

  X Y : Tm
  X = P D 0 (var 0) ⋆
  Y = L D 0 (var 1) ⋆

  xm xp xt em ep et : Nat → Tm
  xm j = P D 1 (var (fv j)) Af
  xp j = L D 1 (var (fv j)) Af
  xt j = th D (fv j)
  em j = P D 1 (var (av j)) (Aα j)
  ep j = L D 1 (var (av j)) (Aα j)
  et j = th D (av j)

  xs es : Nat → Bool
  xs j = touched D (var (fv j))
  es j = touched D (var (av j))

  fl : Ty → Tm → Tm → Tm
  fl = solve Δ

  open Raw2 X Y xm xp xt em ep et xs es fl public

  base : BaseD D (colC m) Δ
  base = record { bmm = vmm ; bmp = vmp ; bsame = vsame ; bup = vup }

  private
    lk-x : lookup (colC m) 0 ≡ just ⋆
    lk-x = lookupΣ-N (chainC m)
    lk-y : lookup (colC m) 1 ≡ just ⋆
    lk-y = lookupΣ-S (chainC m)

    cy-x : CylT D Δ (var 0) ⋆
    cy-x p = vth 0 ⋆ lk-x (T-∨-false p)
    cy-y : CylT D Δ (var 1) ⋆
    cy-y p = vth 1 ⋆ lk-y (T-∨-false p)

    bdF : CylBd D Δ Af
    bdF = tt , cy-x , cy-y

    df : ∀ j → j ≤ m → colC m ⊢tm var (fv j) ∶ Af
    df j p = var-wf wQ (lk-f m j p)

    da : ∀ j → j < m → colC m ⊢tm var (av j) ∶ Aα j
    da j p = var-wf wQ (lk-a m j p)

    cy-f : ∀ j → j ≤ m → CylT D Δ (var (fv j)) Af
    cy-f j p q = vth (fv j) Af (lk-f m j p) (T-∨-false q)

    bdA : ∀ j → j < m → CylBd D Δ (Aα j)
    bdA j p = bdF , cy-f j (≤-w p) , cy-f (suc j) p
      where
      ≤-w : ∀ {j m} → j < m → j ≤ m
      ≤-w (s≤s q) = go q
        where
        go : ∀ {a b} → a ≤ b → a ≤ suc b
        go z≤n     = z≤n
        go (s≤s r) = s≤s (go r)

  -- The hypothesis: rcS answers every gap the construction uses.
  ColRC : Tm → Tm → Set
  ColRC c⁻ c⁺ = ∀ {j u v} → Conn m c⁻ c⁺ j u v → RCAt Δ (arr (Aj j) u v)

  lok : ∀ c⁻ c⁺ → ColRC c⁻ c⁺ → Typ2.LOK {Δ} {X} {Y} {xm} {xp} {xt} {em} {ep} {et} {xs} {es} {fl} m c⁻ c⁺
  lok c⁻ c⁺ rc = record
    { wX     = Sb.lookup-sub closed wQ lk-x vmm
    ; wY     = Sb.lookup-sub closed wQ lk-y vmp
    ; tx⁻    = λ j p → P-wf base (df j p) bdF 1 tt
    ; tx⁺    = λ j p → L-wf base (df j p) bdF 1 tt
    ; te⁻    = λ j p → P-wf base (da j p) (bdA j p) 1 tt
    ; te⁺    = λ j p → L-wf base (da j p) (bdA j p) 1 tt
    ; tx↑    = λ j p e → vth (fv j) Af (lk-f m j p) (T-∨-false (subst T (sym e) tt))
    ; te↑    = λ j p e → vth (av j) (Aα j) (lk-a m j p) (T-∨-false (subst T (sym e) tt))
    ; same-x = λ j p e → triv base (df j p) e 1 refl
    ; same-e = λ j p e → same-α j p e
    ; up-e   = λ j p e → up-α j p e
    ; fl-wf  = λ g du dv → solve-ok du dv (rc g)
    }
    where
    open Shape K D using (triv-P; triv-L)
    same-α : ∀ j → j < m → es j ≡ false → em j ≡ ep j
    same-α j p e =
      trans (triv-P (var (av j)) (Aα j) uB 1 tt)
      (trans (same-tm base (var (av j)) (Sb.tm-sc closed (da j p)) e)
             (sym (triv-L (var (av j)) (Aα j) uB 1 tt)))
      where uB = UT base (da j p) e
    up-α : ∀ j → j < m → es j ≡ false → (xs j ≡ false) × (xs (suc j) ≡ false)
    up-α j p e = cong (_∨ false) (∨-false-l {sel D (fv j)} u₂) , ∨-false-r {sel D (fv j)} u₂
      where
      u  = UT base (da j p) e
      u₁ = ∨-false-r {sel D 0} u
      u₂ = ∨-false-r {sel D 1} u₁

  -- The theorem: for any 2-cell c : f_0 ⇒ f_m over Q_m, the ladder
  -- filler is c↑ : a_c → b_c, given that rcS answers its gaps.
  col-ok : ∀ c → colC m ⊢tm c ∶ Bc m → ColRC (P D 1 c (Bc m)) (L D 1 c (Bc m)) →
           Δ ⊢tm fill m (P D 1 c (Bc m)) (L D 1 c (Bc m)) ∶ cylTy D c (Bc m)
  col-ok c dc rc with cylTy-wf base dc (bdF , cy-f 0 z≤n , cy-f m ≤-refl)
  ... | arr-wf da' db' = Typ2.fill-wf m c⁻ c⁺ (lok c⁻ c⁺ rc) da' db'
    where
    c⁻ = P D 1 c (Bc m)
    c⁺ = L D 1 c (Bc m)
