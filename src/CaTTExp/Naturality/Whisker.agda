------------------------------------------------------------------------
-- The cylinder of a right whisker (ledger C1d, item 2).
--
-- The whisker context is Q = BK 0 1 = (x, y, f, g, α, z, h): objects
-- x, y, z, 1-cells f, g : x → y, h : y → z and a 2-cell α : f ⇒ g. The
-- whisker c = α ∗₀ h has type B = (f ∗ h ⇒ g ∗ h), f ∗ h = rwT 0 0 f h.
-- For a valid cylinder datum D on Q landing in Δ, c↑ : a_c → b_c is a
-- 3-cell in the hom between x⁻ and z⁺ (`Base`). Its two ends are
--
--   a_c = (c⁻ ▹₀ z↑) ▹₁ (g∗h)↑         b_c = (f∗h)↑ ◃₁ (x↑ ◃₀ c⁺)
--
-- (factors omitted for unselected variables), 2-cells O₁ ⇒ O₆ with
-- O₁ = (f∗h)⁻ ▹ z↑ and O₆ = x↑ ◃ (g∗h)⁺.
--
-- When α is selected, α↑ is a 3-cell that a_c and b_c both contain
-- (through the cylinders of f∗h and g∗h, which contain g↑ and f↑), so
-- a_c and b_c have different strict images and no single coherence
-- relates them. The filler layers α↑ (relative-coherence.md §10):
--
--   O₂ = f⁻ ◃ (h⁻ ▹ z↑)     O₃ = f⁻ ◃ (y↑ ◃ h⁺)
--   O₄ = (f⁻ ▹ y↑) ▹ h⁺     O₅ = (x↑ ◃ g⁺) ▹ h⁺
--
--   Pc = gap(O₁, O₂) ; (f⁻ ◃ h↑) ; gap(O₃, O₄)      (h selected)
--   Pc = gap(O₁, O₄)                                (otherwise)
--   W  = α↑ ▹₀ h⁺                       a 3-cell between 2-cells O₄ ⇒ O₅
--   Λ  = (Pc ◃₁ W) ▹₁ gap(O₅, O₆)       a 3-cell between 2-cells O₁ ⇒ O₆
--
--   c↑ = gap(a_c, Λ⁻) ; Λ ; gap(Λ⁺, b_c)          (α selected)
--   c↑ = gap(a_c, b_c)                            (otherwise)
--
-- Every gap is filled by the relative-coherence procedure
-- (`General.solve`). `whisk-ok` is CONDITIONAL on rcS answering each
-- gap the construction uses (`WRC`), and on the cylinders of f ∗ h and
-- g ∗ h being typed (`cy-fh`, `cy-gh`; for the family of
-- CaTTExp.Naturality.General these are dimension-1 cylinders, typed by
-- `cylω-low`). For c = α ∗₀ h each gap should relate two cells with
-- the same strict image (the 3-cell gaps differ by interchange,
-- reassociation and identities, the 2-cell gaps by reassociation and
-- identities): expected, not proved. Neither that nor the discharge of
-- `WRC` is done here.
------------------------------------------------------------------------
module CaTTExp.Naturality.Whisker where

open import CaTTExp.Prelude
open import CaTTExp.Pure
import CaTTExp.Subst ∅ cattSide as Sb
open import CaTTExp.PureMetatheory using (closed; tm[])
open import CaTTExp.Derived using (tm-ty; BK; wK)
open import CaTTExp.DerivedBoundary
open import CaTTExp.Naturality.Raw
open import CaTTExp.Naturality.Typing using (module Hyp; T-∨-false)
open import CaTTExp.Naturality.Boundary using (BaseD; module Typed)
open import CaTTExp.Naturality.General using (solve; solve-ok; RCAt)

------------------------------------------------------------------------
-- The whisker context and its cells.

WQ : Ctx
WQ = BK 0 1

Af Aα Ah Axz : Ty
Af  = arr ⋆ (var 0) (var 1)
Aα  = arr Af (var 2) (var 3)
Ah  = arr ⋆ (var 1) (var 5)
Axz = arr ⋆ (var 0) (var 5)

fhT ghT : Tm
fhT = rwT 0 0 (var 2) Af (var 5) (var 6)
ghT = rwT 0 0 (var 3) Af (var 5) (var 6)

Bw : Ty
Bw = arr Axz fhT ghT

Bw-eq : wK 0 1 ≡ Bw
Bw-eq = refl

ty-src : ∀ {Γ A s t} → Γ ⊢ty arr A s t → Γ ⊢tm s ∶ A
ty-src (arr-wf a b) = a
ty-tgt' : ∀ {Γ A s t} → Γ ⊢ty arr A s t → Γ ⊢tm t ∶ A
ty-tgt' (arr-wf a b) = b

-- The whisker itself.
cW : Tm
cW = rwT 0 1 (var 4) Aα (var 5) (var 6)

-- c = α ∗₀ h has type B.
cW-wf : WQ ⊢ctx → WQ ⊢tm cW ∶ Bw
cW-wf w =
  subst (WQ ⊢tm cW ∶_)
    (trans (rwT-ty 0 0 (var 4) Af (var 2) (var 3) (var 5) (var 6) refl)
           (cong (λ U → arr U fhT ghT) (rwT-ty0 0 (var 2) Af (var 5) (var 6) refl)))
    (rwT-wf 0 1 (var-wf w refl) refl (var-wf w refl))

-- The construction, for an abstract gap filler fl (kept abstract so
-- that the type checker never unfolds the solver).
module WhF (K : Filler) {Δ : Ctx} {D : Datum} (wQ : WQ ⊢ctx)
           (VD : Hyp.ValidD K D WQ Δ) (fl : Ty → Tm → Tm → Tm) where
  open Cyl K
  open Hyp K using (module ValidD)
  open ValidD VD
  open Typed K

  base : BaseD D WQ Δ
  base = record { bmm = vmm ; bmp = vmp ; bsame = vsame ; bup = vup }

  -- Copies and cylinders.
  X Yp Ym Z fm hp hU αU : Tm
  X  = P D 0 (var 0) ⋆
  Ym = P D 0 (var 1) ⋆
  Yp = L D 0 (var 1) ⋆
  Z  = L D 0 (var 5) ⋆
  fm = P D 0 (var 2) Af
  hp = L D 0 (var 6) Ah
  hU = th D 6
  αU = th D 4

  hs as : Bool
  hs = touched D (var 6)
  as = touched D (var 4)

  Base Base' : Ty
  Base  = arr ⋆ X Z
  Base' = arr ⋆ X Yp

  -- The 1-cells O₁ … O₆ of the hom x⁻ → z⁺.
  O1 O2 O3 O4 O5 O6 : Tm
  O1 = P D 1 fhT Axz
  O2 = lwT 0 0 fm X (P D 1 (var 6) Ah) (TP D 1 Ah)
  O3 = lwT 0 0 fm X (L D 1 (var 6) Ah) (TP D 1 Ah)
  O4 = rwT 0 0 (P D 1 (var 2) Af) Base' Z hp
  O5 = rwT 0 0 (L D 1 (var 3) Af) Base' Z hp
  O6 = L D 1 ghT Axz

  -- Vertical composites of 2-cells and of 3-cells.
  vc2 : Tm → Tm → Tm → Tm → Tm → Tm
  vc2 S T U a b = rwT 1 0 a (arr Base S T) U b

  B3 : Ty
  B3 = arr Base O1 O6

  vc3 : Tm → Tm → Tm → Tm → Tm → Tm
  vc3 S T U a b = rwT 2 0 a (arr B3 S T) U b

  -- f⁻ ◃ h↑ : O₂ ⇒ O₃.
  Fh : Tm
  Fh = lwT 0 1 fm X hU (cylTy D (var 6) Ah)

  Pc : Bool → Tm
  Pc true  = vc2 O1 O2 O4 (fl Base O1 O2) (vc2 O2 O3 O4 Fh (fl Base O3 O4))
  Pc false = fl Base O1 O4

  Qc : Tm
  Qc = fl Base O5 O6

  -- W = α↑ ▹₀ h⁺ : Wa → Wb.
  Wa Wb W : Tm
  Wa = rwT 0 1 (P D 2 (var 4) Aα) (arr Base' (P D 1 (var 2) Af) (L D 1 (var 3) Af)) Z hp
  Wb = rwT 0 1 (L D 2 (var 4) Aα) (arr Base' (P D 1 (var 2) Af) (L D 1 (var 3) Af)) Z hp
  W  = rwT 0 2 αU (cylTy D (var 4) Aα) Z hp

  -- Λ₁ = Pc ◃₁ W and Λ = Λ₁ ▹₁ Qc.
  Λ1⁻ Λ1⁺ Λ1 Λ⁻ Λ⁺ Λ : Tm
  Λ1⁻ = lwT 1 0 (Pc hs) O1 Wa (arr Base O4 O5)
  Λ1⁺ = lwT 1 0 (Pc hs) O1 Wb (arr Base O4 O5)
  Λ1  = lwT 1 1 (Pc hs) O1 W (arr (arr Base O4 O5) Wa Wb)
  Λ⁻  = rwT 1 0 Λ1⁻ (arr Base O1 O5) O6 Qc
  Λ⁺  = rwT 1 0 Λ1⁺ (arr Base O1 O5) O6 Qc
  Λ   = rwT 1 1 Λ1 (arr (arr Base O1 O5) Λ1⁻ Λ1⁺) O6 Qc

  -- The filler, for any 2-cell c : f ∗ h ⇒ g ∗ h of Q.
  ac bc : Tm → Tm
  ac c = P D 2 c Bw
  bc c = L D 2 c Bw

  whiskB : Tm → Bool → Tm
  whiskB c true  = vc3 (ac c) Λ⁻ (bc c) (fl B3 (ac c) Λ⁻) (vc3 Λ⁻ Λ⁺ (bc c) Λ (fl B3 Λ⁺ (bc c)))
  whiskB c false = fl B3 (ac c) (bc c)

  whisk : Tm → Tm
  whisk c = whiskB c as

  -- The gaps the construction fills, each with its side condition.
  data Conn (c : Tm) : Ty → Tm → Tm → Set where
    g-12 : as ≡ true → hs ≡ true  → Conn c Base O1 O2
    g-34 : as ≡ true → hs ≡ true  → Conn c Base O3 O4
    g-14 : as ≡ true → hs ≡ false → Conn c Base O1 O4
    g-56 : as ≡ true → Conn c Base O5 O6
    g-a  : as ≡ true → Conn c B3 (ac c) Λ⁻
    g-b  : as ≡ true → Conn c B3 Λ⁺ (bc c)
    g-ab : as ≡ false → Conn c B3 (ac c) (bc c)

  -- The hypothesis: fl is well typed on every gap the construction uses.
  FlOK : Tm → Set
  FlOK c = ∀ {A u v} → Conn c A u v → Δ ⊢tm u ∶ A → Δ ⊢tm v ∶ A → Δ ⊢tm fl A u v ∶ arr A u v

  ----------------------------------------------------------------------
  -- Typing.

  module _ (cy-fh : CylT D Δ fhT Axz) (cy-gh : CylT D Δ ghT Axz)
           {c : Tm} (dc : WQ ⊢tm c ∶ Bw) (flok : FlOK c) where
    private
      dfh : WQ ⊢tm fhT ∶ Axz
      dfh = ty-src (tm-ty dc)

      dgh : WQ ⊢tm ghT ∶ Axz
      dgh = ty-tgt' (tm-ty dc)

      cy-v : ∀ i A → lookup WQ i ≡ just A → CylT D Δ (var i) A
      cy-v i A e p = vth i A e (T-∨-false p)

      dv : ∀ i A → lookup WQ i ≡ just A → WQ ⊢tm var i ∶ A
      dv i A e = var-wf wQ e

      bd⋆ : CylBd D Δ ⋆
      bd⋆ = tt

      bdF : CylBd D Δ Af
      bdF = tt , cy-v 0 ⋆ refl , cy-v 1 ⋆ refl

      bdH : CylBd D Δ Ah
      bdH = tt , cy-v 1 ⋆ refl , cy-v 5 ⋆ refl

      bdXZ : CylBd D Δ Axz
      bdXZ = tt , cy-v 0 ⋆ refl , cy-v 5 ⋆ refl

      bdα : CylBd D Δ Aα
      bdα = bdF , cy-v 2 Af refl , cy-v 3 Af refl

      bdB : CylBd D Δ Bw
      bdB = bdXZ , cy-fh , cy-gh

      d-f : Δ ⊢tm fm ∶ arr ⋆ X Ym
      d-f = P-wf base (dv 2 Af refl) bdF 0 tt

      d-hp : Δ ⊢tm hp ∶ arr ⋆ Yp Z
      d-hp = L-wf base (dv 6 Ah refl) bdH 0 tt

      d-P1h : Δ ⊢tm P D 1 (var 6) Ah ∶ arr ⋆ Ym Z
      d-P1h = P-wf base (dv 6 Ah refl) bdH 1 tt

      d-L1h : Δ ⊢tm L D 1 (var 6) Ah ∶ arr ⋆ Ym Z
      d-L1h = L-wf base (dv 6 Ah refl) bdH 1 tt

      d-P1f : Δ ⊢tm P D 1 (var 2) Af ∶ Base'
      d-P1f = P-wf base (dv 2 Af refl) bdF 1 tt

      d-L1g : Δ ⊢tm L D 1 (var 3) Af ∶ Base'
      d-L1g = L-wf base (dv 3 Af refl) bdF 1 tt

      rw0 : ∀ {c a b z h} → Δ ⊢tm c ∶ arr ⋆ a b → Δ ⊢tm h ∶ arr ⋆ b z →
            Δ ⊢tm rwT 0 0 c (arr ⋆ a b) z h ∶ arr ⋆ a z
      rw0 {c} {a} {b} {z} {h} dc dh =
        subst (Δ ⊢tm rwT 0 0 c (arr ⋆ a b) z h ∶_) (rwT-ty0 0 c (arr ⋆ a b) z h refl) (rwT-wf 0 0 dc refl dh)

      lw0 : ∀ {h x c a b} → Δ ⊢tm h ∶ arr ⋆ x a → Δ ⊢tm c ∶ arr ⋆ a b →
            Δ ⊢tm lwT 0 0 h x c (arr ⋆ a b) ∶ arr ⋆ x b
      lw0 {h} {x} {c} {a} {b} dh dc =
        subst (Δ ⊢tm lwT 0 0 h x c (arr ⋆ a b) ∶_) (lwT-ty0 0 h x c (arr ⋆ a b) refl) (lwT-wf 0 0 dc refl dh)

      vc2-wf : ∀ {S T U a b} → Δ ⊢tm a ∶ arr Base S T → Δ ⊢tm b ∶ arr Base T U →
               Δ ⊢tm vc2 S T U a b ∶ arr Base S U
      vc2-wf {S} {T} {U} {a} {b} da db =
        subst (Δ ⊢tm vc2 S T U a b ∶_) (rwT-ty0 1 a (arr Base S T) U b refl) (rwT-wf 1 0 da refl db)

      vc3-wf : ∀ {S T U a b} → Δ ⊢tm a ∶ arr B3 S T → Δ ⊢tm b ∶ arr B3 T U →
               Δ ⊢tm vc3 S T U a b ∶ arr B3 S U
      vc3-wf {S} {T} {U} {a} {b} da db =
        subst (Δ ⊢tm vc3 S T U a b ∶_) (rwT-ty0 2 a (arr B3 S T) U b refl) (rwT-wf 2 0 da refl db)

      d-O1 : Δ ⊢tm O1 ∶ Base
      d-O1 = P-wf base dfh bdXZ 1 tt

      d-O6 : Δ ⊢tm O6 ∶ Base
      d-O6 = L-wf base dgh bdXZ 1 tt

      d-O2 : Δ ⊢tm O2 ∶ Base
      d-O2 = lw0 d-f d-P1h

      d-O3 : Δ ⊢tm O3 ∶ Base
      d-O3 = lw0 d-f d-L1h

      d-O4 : Δ ⊢tm O4 ∶ Base
      d-O4 = rw0 d-P1f d-hp

      d-O5 : Δ ⊢tm O5 ∶ Base
      d-O5 = rw0 d-L1g d-hp

      d-hU : hs ≡ true → Δ ⊢tm hU ∶ cylTy D (var 6) Ah
      d-hU e = vth 6 Ah refl (T-∨-false (subst T (sym e) tt))

      d-αU : as ≡ true → Δ ⊢tm αU ∶ cylTy D (var 4) Aα
      d-αU e = vth 4 Aα refl (T-∨-false (subst T (sym e) tt))

      -- f⁻ ◃ h↑ : O₂ ⇒ O₃.
      d-Fh : hs ≡ true → Δ ⊢tm Fh ∶ arr Base O2 O3
      d-Fh e =
        subst (Δ ⊢tm Fh ∶_)
          (trans (lwT-ty 0 0 fm X hU (TP D 1 Ah) (P D 1 (var 6) Ah) (L D 1 (var 6) Ah) refl)
                 (cong (λ U → arr U O2 O3) (lwT-ty0 0 fm X (P D 1 (var 6) Ah) (TP D 1 Ah) refl)))
          (lwT-wf 0 1 (d-hU e) refl d-f)

      gap : ∀ {A u v} → Conn c A u v → Δ ⊢tm u ∶ A → Δ ⊢tm v ∶ A → Δ ⊢tm fl A u v ∶ arr A u v
      gap = flok

      d-Pc : as ≡ true → ∀ v → hs ≡ v → Δ ⊢tm Pc v ∶ arr Base O1 O4
      d-Pc ea true  e = vc2-wf (gap (g-12 ea e) d-O1 d-O2) (vc2-wf (d-Fh e) (gap (g-34 ea e) d-O3 d-O4))
      d-Pc ea false e = gap (g-14 ea e) d-O1 d-O4

      d-Qc : as ≡ true → Δ ⊢tm Qc ∶ arr Base O5 O6
      d-Qc ea = gap (g-56 ea) d-O5 d-O6

      -- W = α↑ ▹₀ h⁺ : Wa → Wb, between 2-cells O₄ ⇒ O₅.
      CW : Ty
      CW = arr (arr Base O4 O5) Wa Wb

      d-W : as ≡ true → Δ ⊢tm W ∶ CW
      d-W ea =
        subst (Δ ⊢tm W ∶_)
          (trans (rwT-ty 0 1 αU C' (P D 2 (var 4) Aα) (L D 2 (var 4) Aα) Z hp refl)
                 (cong (λ U → arr U Wa Wb)
                   (trans (rwT-ty 0 0 (P D 2 (var 4) Aα) Base' (P D 1 (var 2) Af) (L D 1 (var 3) Af) Z hp refl)
                          (cong (λ U → arr U O4 O5) (rwT-ty0 0 (P D 1 (var 2) Af) Base' Z hp refl)))))
          (rwT-wf 0 2 (d-αU ea) refl d-hp)
        where C' = arr Base' (P D 1 (var 2) Af) (L D 1 (var 3) Af)

      -- Λ₁ = Pc ◃₁ W : Λ₁⁻ → Λ₁⁺, between 2-cells O₁ ⇒ O₅.
      d-Λ1 : as ≡ true → Δ ⊢tm Λ1 ∶ arr (arr Base O1 O5) Λ1⁻ Λ1⁺
      d-Λ1 ea =
        subst (Δ ⊢tm Λ1 ∶_)
          (trans (lwT-ty 1 0 (Pc hs) O1 W (arr Base O4 O5) Wa Wb refl)
                 (cong (λ U → arr U Λ1⁻ Λ1⁺) (lwT-ty0 1 (Pc hs) O1 Wa (arr Base O4 O5) refl)))
          (lwT-wf 1 1 (d-W ea) refl (d-Pc ea hs refl))

      -- Λ = Λ₁ ▹₁ Qc : Λ⁻ → Λ⁺, between 2-cells O₁ ⇒ O₆. (The implicit
      -- arguments are given explicitly: inferring them exhausts memory.)
      CΛ : Ty
      CΛ = arr (arr Base O1 O5) Λ1⁻ Λ1⁺

      r-Λ : as ≡ true → Δ ⊢tm Λ ∶ wK 1 1 [ σR Λ1 CΛ O6 Qc ]ty
      r-Λ ea = rwT-wf 1 1 {Δ} {Λ1} {CΛ} {O6} {Qc} (d-Λ1 ea) refl (d-Qc ea)

      e1-Λ : wK 1 1 [ σR Λ1 CΛ O6 Qc ]ty ≡ arr (wK 1 0 [ σR Λ1⁻ (arr Base O1 O5) O6 Qc ]ty) Λ⁻ Λ⁺
      e1-Λ = rwT-ty 1 0 Λ1 (arr Base O1 O5) Λ1⁻ Λ1⁺ O6 Qc refl

      e2-Λ : wK 1 0 [ σR Λ1⁻ (arr Base O1 O5) O6 Qc ]ty ≡ B3
      e2-Λ = rwT-ty0 1 Λ1⁻ (arr Base O1 O5) O6 Qc refl

      d-Λ : as ≡ true → Δ ⊢tm Λ ∶ arr B3 Λ⁻ Λ⁺
      d-Λ ea = subst (Δ ⊢tm Λ ∶_) (trans e1-Λ (cong (λ U → arr U Λ⁻ Λ⁺) e2-Λ)) (r-Λ ea)

      d-Λ⁻ : as ≡ true → Δ ⊢tm Λ⁻ ∶ B3
      d-Λ⁻ ea = ty-src (tm-ty (d-Λ ea))

      d-Λ⁺ : as ≡ true → Δ ⊢tm Λ⁺ ∶ B3
      d-Λ⁺ ea = ty-tgt' (tm-ty (d-Λ ea))

      d-ac : Δ ⊢tm ac c ∶ B3
      d-ac = ty-src {Δ} {B3} {ac c} {bc c} (cylTy-wf base dc bdB)

      d-bc : Δ ⊢tm bc c ∶ B3
      d-bc = ty-tgt' {Δ} {B3} {ac c} {bc c} (cylTy-wf base dc bdB)

    -- The filler is c↑ : a_c → b_c, given that fl is well typed on
    -- its gaps and the cylinders of f ∗ h and g ∗ h are typed.
    whiskF-ok : Δ ⊢tm whisk c ∶ arr B3 (ac c) (bc c)
    whiskF-ok = go as refl
      where
      go : ∀ v → as ≡ v → Δ ⊢tm whiskB c v ∶ arr B3 (ac c) (bc c)
      go true  e =
        vc3-wf {ac c} {Λ⁻} {bc c} {fl B3 (ac c) Λ⁻} {vc3 Λ⁻ Λ⁺ (bc c) Λ (fl B3 Λ⁺ (bc c))}
          (gap (g-a e) d-ac (d-Λ⁻ e))
          (vc3-wf {Λ⁻} {Λ⁺} {bc c} {Λ} {fl B3 Λ⁺ (bc c)} (d-Λ e) (gap (g-b e) (d-Λ⁺ e) d-bc))
      go false e = gap (g-ab e) d-ac d-bc

-- The instance at the relative-coherence procedure.
module Wh (K : Filler) {Δ : Ctx} {D : Datum} (wQ : WQ ⊢ctx) (VD : Hyp.ValidD K D WQ Δ) where
  open WhF K wQ VD (solve Δ) public
  open Typed K using (CylT)

  -- The hypothesis: rcS answers every gap the construction uses.
  WRC : Tm → Set
  WRC c = ∀ {A u v} → Conn c A u v → RCAt Δ (arr A u v)

  -- The theorem: for any 2-cell c : f ∗ h ⇒ g ∗ h over Q, the filler is
  -- c↑ : a_c → b_c, given that rcS answers its gaps and the cylinders
  -- of f ∗ h and g ∗ h are typed.
  whisk-ok : CylT D Δ fhT Axz → CylT D Δ ghT Axz →
             ∀ c → WQ ⊢tm c ∶ Bw → WRC c → Δ ⊢tm whisk c ∶ Cyl.cylTy K D c Bw
  whisk-ok cfh cgh c dc rc = whiskF-ok cfh cgh dc (λ g du dv → solve-ok du dv (rc g))

